use std::ops::{Add, AddAssign, Mul, MulAssign};

fn kitamasa_next<T>(v: &[T], c: &[T]) -> Vec<T>
where
    T: Copy + AddAssign + MulAssign,
{
    debug_assert!(!v.is_empty());
    debug_assert_eq!(v.len(), c.len());
    let n = v.len();
    let mut res = Vec::from(c);
    res[0] *= v[n - 1];
    for i in 1..n {
        res[i] *= v[n - 1];
        res[i] += v[i - 1];
    }
    res
}

pub fn kitamasa<T>(c: &[T], ini: &[T], n: usize) -> T
where
    T: Copy + Add<Output = T> + AddAssign + Mul<Output = T> + MulAssign + From<i32>,
{
    debug_assert_eq!(c.len(), ini.len());
    debug_assert!(!c.is_empty());
    let len = c.len();
    let mut v = vec![T::from(0); len];
    v[0] = T::from(1);
    for i in (0..64).rev() {
        let mut w = Vec::with_capacity(len);
        w.push(std::mem::replace(&mut v, vec![T::from(0); len]));
        for j in 0..len - 1 {
            w.push(kitamasa_next(&w[j], c));
        }
        for j in 0..len {
            for k in 0..len {
                v[j] += w[0][k] * w[k][j];
            }
        }
        if n >> i & 1 == 1 {
            v = kitamasa_next(&v, c);
        }
    }
    v.iter()
        .zip(ini)
        .map(|(&c, &v)| c * v)
        .fold(T::from(0), |s, a| s + a)
}

#[cfg(test)]
#[test]
fn test_kitamasa() {
    assert_eq!(kitamasa(&[1, 1], &[0, 1], 6), 8);
    assert_eq!(kitamasa(&[1, 1, 1], &[0, 0, 1], 6), 7);

    assert_eq!(kitamasa(&[3, 2, 1], &[2, 1, 1], 0), 2);
    assert_eq!(kitamasa(&[3, 2, 1], &[2, 1, 1], 1), 1);
    assert_eq!(kitamasa(&[3, 2, 1], &[2, 1, 1], 2), 1);
    assert_eq!(kitamasa(&[3, 2, 1], &[2, 1, 1], 3), 9);
    assert_eq!(kitamasa(&[3, 2, 1], &[2, 1, 1], 4), 14);
    assert_eq!(kitamasa(&[3, 2, 1], &[2, 1, 1], 5), 35);
}
