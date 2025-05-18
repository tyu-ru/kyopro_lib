use rand::{prelude::*, rngs::SmallRng, SeedableRng};
use std::cmp::Ordering;

pub fn insertion_sort<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    // sorted a[..i]
    for mut i in 1..a.len() {
        while i != 0 && !is_less(&a[i - 1], &a[i]) {
            a.swap(i - 1, i);
            i -= 1;
        }
    }
}

#[cfg(test)]
#[test]
fn test_insertion_sort() {
    use itertools::Itertools;
    let n = 5;
    for mut v in (0..n).permutations(n) {
        insertion_sort(&mut v, &mut |a, b| a < b);
        assert_eq!(v, (0..n).collect_vec());
    }
}

fn mid3<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], rng: &mut SmallRng, is_less: &mut F) {
    let m = a.len() - 1;
    let pb = rng.gen_range(1..m);
    if is_less(&a[0], &a[m]) {
        a.swap(m, 0);
    }
    if is_less(&a[pb], &a[0]) {
        a.swap(0, pb);
    }
    if is_less(&a[0], &a[m]) {
        a.swap(m, 0);
    }
}

fn select_nth_unstable1_impl<T, F: FnMut(&T, &T) -> bool>(
    a: &mut [T],
    index: usize,
    mut is_less: F,
) -> (&mut [T], &mut T, &mut [T]) {
    assert!(index < a.len(), "index must include 0..a.len()!");

    let mut rng = SmallRng::from_entropy();
    let mut range = 0..a.len();
    while range.start + 1 != range.end {
        if range.end - range.start <= 5 {
            insertion_sort(&mut a[range], &mut is_less);
            break;
        }
        let mut l = range.start + 1;
        let mut r = range.end - 1;
        mid3(&mut a[range.clone()], &mut rng, &mut is_less);
        loop {
            while l + 1 < range.end && is_less(&a[l], &a[range.start]) {
                l += 1;
            }
            while r != 0 && is_less(&a[range.start], &a[r]) {
                r -= 1;
            }
            if r <= l {
                break;
            }
            a.swap(l, r);
            l += 1;
            r -= 1;
        }
        a.swap(range.start, r);
        if index < l {
            range = range.start..l
        } else if index > r {
            range = r + 1..range.end
        } else {
            break;
        }
    }

    let (l, mr) = a.split_at_mut(index);
    let (m, r) = mr.split_first_mut().unwrap();
    (l, m, r)
}

pub fn select_nth_unstable1<T: Ord>(a: &mut [T], index: usize) -> (&mut [T], &mut T, &mut [T]) {
    select_nth_unstable1_impl(a, index, |a, b| a.lt(b))
}
pub fn select_nth_unstable1_by<T, F: FnMut(&T, &T) -> Ordering>(
    a: &mut [T],
    index: usize,
    mut compare: F,
) -> (&mut [T], &mut T, &mut [T]) {
    select_nth_unstable1_impl(a, index, |a, b| compare(a, b) == Ordering::Less)
}
pub fn select_nth_unstable1_by_key<T, F: FnMut(&T) -> K, K: Ord>(
    a: &mut [T],
    index: usize,
    mut f: F,
) -> (&mut [T], &mut T, &mut [T]) {
    select_nth_unstable1_impl(a, index, |a, b| f(a).lt(&f(b)))
}

#[cfg(test)]
mod test_select_nth_unstable {
    use super::select_nth_unstable1;
    use itertools::Itertools;

    #[test]
    #[should_panic(expected = "index must include 0..a.len()!")]
    fn empty() {
        select_nth_unstable1(&mut Vec::<i32>::new(), 0);
    }
    #[test]
    fn once() {
        let mut v = vec![1];
        {
            let (l, m, r) = select_nth_unstable1(&mut v, 0);
            assert_eq!(l, &[]);
            assert_eq!(m, &1);
            assert_eq!(r, &[]);
        }
        assert_eq!(v, &[1]);
    }

    #[test]
    fn normal() {
        let mut v = vec![0, 4, 2, 1, 3];
        {
            let (l, m, r) = select_nth_unstable1(&mut v, 2);
            println!("{:?} {} {:?}", l, m, r);
            assert!(l.iter().all(|x| *x < *m) && r.iter().all(|x| *m < *x));
        }
        assert!(
            v == [1, 0, 2, 3, 4]
                || v == [0, 1, 2, 3, 4]
                || v == [1, 0, 2, 4, 3]
                || v == [0, 1, 2, 4, 3]
        );

        let mut v = vec![0, 4, 2, 1, 3];
        select_nth_unstable1(&mut v, 3);
        assert!(
            v == [0, 1, 2, 3, 4]
                || v == [0, 2, 1, 3, 4]
                || v == [1, 0, 2, 3, 4]
                || v == [1, 2, 0, 3, 4]
                || v == [2, 0, 1, 3, 4]
                || v == [2, 1, 0, 3, 4]
        );
    }

    #[cfg(test)]
    #[test]
    fn all_pertern() {
        let n = 8;
        for v in (0..n).permutations(n) {
            for i in 0..n {
                let mut v = v.clone();
                let (l, m, r) = select_nth_unstable1(&mut v, i);
                assert!(l.iter().all(|x| *x < *m));
                assert!(r.iter().all(|x| *m < *x));
                assert_eq!(l.len(), i);
                assert_eq!(m, &i);
                assert_eq!(r.len(), n - i - 1);
            }
        }
    }

    #[cfg(test)]
    #[test]
    fn all_pertern2() {
        let n = 5;
        for v in (0..n).map(|_| 0..10).multi_cartesian_product() {
            for i in 0..n {
                let mut v = v.clone();
                let (l, m, r) = select_nth_unstable1(&mut v, i);
                assert!(l.iter().all(|x| *x <= *m));
                assert!(r.iter().all(|x| *m <= *x));
            }
        }
    }

    #[cfg(test)]
    #[test]
    fn all_equal() {
        let mut v = vec![1; 100];
        {
            let (_, m, _) = select_nth_unstable1(&mut v, 50);
            assert_eq!(m, &1);
        }
        assert_eq!(v, vec![1; 100]);
    }

    #[cfg(test)]
    #[test]
    fn almost_euql() {
        let mut v = vec![1; 10];
        v.extend_from_slice(&[3; 10]);
        v.push(2);
        let (l, m, r) = select_nth_unstable1(&mut v, 10);
        assert!(l.iter().all(|x| x == &1));
        assert_eq!(m, &2);
        assert!(r.iter().all(|x| x == &3));
    }
    #[cfg(test)]
    #[test]
    fn almost_euql2() {
        let mut v = vec![1; 10];
        v.extend_from_slice(&[3; 10]);
        v.extend_from_slice(&[2; 10]);
        use rand::prelude::*;
        v.shuffle(&mut thread_rng());

        let (l, m, r) = select_nth_unstable1(&mut v, 15);
        assert!(l.iter().all(|x| x <= &2));
        assert_eq!(m, &2);
        assert!(r.iter().all(|x| x >= &2));
    }

    #[cfg(test)]
    #[test]
    fn stress() {
        use rand::prelude::*;
        for _ in 0..100 {
            let mut v = (0..100).collect::<Vec<_>>();
            v.shuffle(&mut thread_rng());
            let idx = thread_rng().gen_range(0..100);
            {
                let (l, m, r) = select_nth_unstable1(&mut v, idx);
                assert!(l.iter().all(|x| *x < *m));
                assert!(r.iter().all(|x| *m < *x));
                assert_eq!(l.len(), idx);
                assert_eq!(m, &idx);
            }
            assert_eq!(v[idx], idx);
        }
    }
}
