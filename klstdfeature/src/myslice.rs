use rand::{prelude::*, rngs::SmallRng, SeedableRng};

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
