extern crate num;

#[inline]
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

#[inline]
pub fn lowest_one_bit(x: u64) -> u64 {
    x & ((!x).wrapping_add(1))
}

#[test]
fn test_lowest_one_bit() {
    assert_eq!(lowest_one_bit(0), 0);
    assert_eq!(lowest_one_bit(0b1), 1);
    assert_eq!(lowest_one_bit(0b101001000), 0b1000);
}

#[inline]
pub fn ntz(x: u64) -> usize {
    lowest_one_bit(x).wrapping_sub(1).count_ones() as usize
}

#[test]
fn test_ntz() {
    assert_eq!(ntz(0), 64);
    assert_eq!(ntz(0b1000), 3);
    assert_eq!(ntz(0b1001), 0);
}

/// f(i) == true となる 最小のi
pub fn lower_bound<I, F>(mut l: I, mut r: I, mut f: F) -> I
where
    I: num::traits::PrimInt,
    F: FnMut(I) -> bool,
{
    while l != r {
        let m = l + ((r - l) >> 1);
        if f(m) {
            r = m;
        } else {
            l = m + I::one();
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
#[test]
fn test_lower_bound2() {
    assert_eq!(lower_bound(i64::min_value() + 1, 0, |x| -100 < x), -99);
}

pub struct BitPattern {
    i: u64,
    mask: u64,
    end: bool,
}
impl BitPattern {
    #[inline]
    pub fn new(n: usize) -> Self {
        Self {
            i: (1 << n) - 1,
            mask: (1 << n) - 1,
            end: n == 0,
        }
    }
    #[inline]
    pub fn with_mask(n: usize, mask: u64) -> Self {
        Self {
            i: (1 << n) - 1,
            mask: mask & ((1 << n) - 1),
            end: n == 0,
        }
    }
}

impl Iterator for BitPattern {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        if self.end {
            None
        } else {
            let x = self.i;
            if self.i == 0 {
                self.end = true;
            } else {
                self.i = (self.i - 1) & self.mask;
            }
            Some(!x & self.mask)
        }
    }
}

#[test]
fn test_bit_pattern() {
    assert_eq!(BitPattern::new(0).collect::<Vec<_>>(), []);
    assert_eq!(BitPattern::new(1).collect::<Vec<_>>(), [0b0, 0b1]);
    assert_eq!(
        BitPattern::new(3).collect::<Vec<_>>(),
        [0b000, 0b001, 0b010, 0b011, 0b100, 0b101, 0b110, 0b111]
    );
    assert_eq!(
        BitPattern::with_mask(6, 0b10_1011).collect::<Vec<_>>(),
        [
            0b00_0000, 0b00_0001, 0b00_0010, 0b00_0011, 0b00_1000, 0b00_1001, 0b00_1010, 0b00_1011,
            0b10_0000, 0b10_0001, 0b10_0010, 0b10_0011, 0b10_1000, 0b10_1001, 0b10_1010, 0b10_1011,
        ]
    );
}

pub struct BitIter {
    i: u64,
}
impl BitIter {
    #[inline]
    pub fn new(x: u64) -> Self {
        Self { i: x }
    }
}
impl Iterator for BitIter {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        if self.i == 0 {
            None
        } else {
            let res = self.i.trailing_zeros() as usize;
            self.i &= self.i - 1;
            Some(res)
        }
    }
}

#[test]
fn test_bit_iter() {
    assert_eq!(BitIter::new(0).collect::<Vec<_>>(), []);
    assert_eq!(BitIter::new(0b0100_1101).collect::<Vec<_>>(), [0, 2, 3, 6]);
}

pub fn pick2(r: std::ops::Range<usize>) -> impl Iterator<Item = (usize, usize)> {
    r.clone()
        .flat_map(move |i| (i + 1..r.end).map(move |j| (i, j)))
}

#[test]
fn test_pick2() {
    assert_eq!(pick2(0..0).collect::<Vec<_>>(), []);
    assert_eq!(pick2(0..1).collect::<Vec<_>>(), []);
    assert_eq!(pick2(0..3).collect::<Vec<_>>(), [(0, 1), (0, 2), (1, 2)]);
    assert_eq!(
        pick2(0..4).collect::<Vec<_>>(),
        [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    );
}

pub fn log2p1<T: num::PrimInt>(x: T) -> T {
    match x.count_ones() {
        0 => T::zero(),
        _ => T::from(std::mem::size_of::<T>() * 8 - x.leading_zeros() as usize).unwrap(),
    }
}

#[test]
fn test_log2p1() {
    assert_eq!(log2p1(0), 0);
    assert_eq!(1 << log2p1(1 - 1), 1);
    assert_eq!(1 << log2p1(7 - 1), 8);
    assert_eq!(1 << log2p1(8 - 1), 8);
    assert_eq!(1 << log2p1(9 - 1), 16);
}

pub fn next_permutation(p: &mut [usize]) -> bool {
    if let Some(i) = (0..p.len() - 1).rev().filter(|&i| p[i] < p[i + 1]).next() {
        let j = (0..p.len()).rev().filter(|&j| p[i] < p[j]).next().unwrap();
        p.swap(i, j);
        p[i + 1..].reverse();
        true
    } else {
        p.reverse();
        false
    }
}

#[test]
fn test_next_permutation() {
    let mut a = [1, 2, 3];
    assert_eq!(next_permutation(&mut a), true);
    assert_eq!(a, [1, 3, 2]);
    assert_eq!(next_permutation(&mut a), true);
    assert_eq!(a, [2, 1, 3]);
    assert_eq!(next_permutation(&mut a), true);
    assert_eq!(a, [2, 3, 1]);
    assert_eq!(next_permutation(&mut a), true);
    assert_eq!(a, [3, 1, 2]);
    assert_eq!(next_permutation(&mut a), true);
    assert_eq!(a, [3, 2, 1]);
    assert_eq!(next_permutation(&mut a), false);
    assert_eq!(a, [1, 2, 3]);
}
