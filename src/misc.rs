extern crate num;

pub fn ceil<T: num::Integer + Copy>(x: T, y: T) -> T {
    (x + y - T::one()) / y
}

#[test]
fn test_ceil() {
    assert_eq!(ceil(10 + 0, 5), 2);
    assert_eq!(ceil(10 + 1, 5), 3);
    assert_eq!(ceil(10 + 4, 5), 3);
    assert_eq!(ceil(10 + 5, 5), 3);
    assert_eq!(ceil(10 + 6, 5), 4);
}

pub fn ntz(x: u64) -> usize {
    (!x & (x - 1)).count_ones() as usize
}

#[test]
fn test_ntz() {
    assert_eq!(ntz(0b1000 as u64), 3);
    assert_eq!(ntz(0b1001 as u64), 0);
}

/// f(i) == true となる 最小のi
pub fn lower_bound<F>(mut l: usize, mut r: usize, f: F) -> usize
where
    F: Fn(usize) -> bool,
{
    while l != r {
        let m = l + (r - l) / 2;
        if f(m) {
            r = m;
        } else {
            l = m + 1;
        }
    }
    r
}

#[test]
fn test_lower_bound() {
    let arr = &[0, 2, 4, 6, 8];
    let g = |x| move |i| x <= arr[i];

    assert_eq!(lower_bound(0, arr.len(), g(0)), 0);
    assert_eq!(lower_bound(0, arr.len(), g(4)), 2);
    assert_eq!(lower_bound(0, arr.len(), g(8)), 4);

    assert_eq!(lower_bound(0, arr.len(), g(-1)), 0);
    assert_eq!(lower_bound(0, arr.len(), g(1)), 1);
    assert_eq!(lower_bound(0, arr.len(), g(9)), 5);
}
