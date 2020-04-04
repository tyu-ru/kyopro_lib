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
