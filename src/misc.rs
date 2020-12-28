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

#[cfg(test)]
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
#[cfg(test)]
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
        let mask = mask & ((1 << n) - 1);
        Self {
            i: mask,
            mask: mask,
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

#[cfg(test)]
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
    assert_eq!(BitPattern::with_mask(6, 0).collect::<Vec<_>>(), [0]);
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

#[cfg(test)]
#[test]
fn test_bit_iter() {
    assert_eq!(BitIter::new(0).collect::<Vec<_>>(), []);
    assert_eq!(BitIter::new(0b0100_1101).collect::<Vec<_>>(), [0, 2, 3, 6]);
}

#[derive(PartialEq, PartialOrd)]
pub struct Total<T>(pub T);
impl<T: PartialEq> Eq for Total<T> {}
impl<T: PartialOrd> Ord for Total<T> {
    fn cmp(&self, other: &Total<T>) -> std::cmp::Ordering {
        self.0.partial_cmp(&other.0).unwrap()
    }
}
