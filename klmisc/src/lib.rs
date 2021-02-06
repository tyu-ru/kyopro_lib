/// Returns the smallest `i` that is `f(i) == true`
pub fn lower_bound<I, F>(r: std::ops::Range<I>, mut f: F) -> I
where
    I: num::traits::PrimInt,
    F: FnMut(I) -> bool,
{
    let std::ops::Range {
        start: mut l,
        end: mut r,
    } = r;
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

    assert_eq!(lower_bound(0..arr.len(), g(0)), 0);
    assert_eq!(lower_bound(0..arr.len(), g(4)), 2);
    assert_eq!(lower_bound(0..arr.len(), g(8)), 4);

    assert_eq!(lower_bound(0..arr.len(), g(-1)), 0);
    assert_eq!(lower_bound(0..arr.len(), g(1)), 1);
    assert_eq!(lower_bound(0..arr.len(), g(9)), 5);
}
#[cfg(test)]
#[test]
fn test_lower_bound2() {
    assert_eq!(lower_bound(i64::min_value() + 1..0, |x| -100 < x), -99);
}

/// Bit all pettern enumeration iterator.
/// # See also
/// [`bit_pattern`]
#[derive(Clone)]
pub struct BitPattern {
    i: usize,
    mask: usize,
    end: bool,
}

/// Bit all pettern enumeration iterator.
/// Scan only the bit where `mask` stands.
/// # Example
/// ```
/// # use klmisc::bit_pattern;
/// let mut iter = bit_pattern(0b101);
/// assert_eq!(iter.next(), Some(0b000));
/// assert_eq!(iter.next(), Some(0b001));
/// assert_eq!(iter.next(), Some(0b100));
/// assert_eq!(iter.next(), Some(0b101));
/// assert_eq!(iter.next(), None);
/// ```
pub fn bit_pattern(mask: usize) -> BitPattern {
    BitPattern {
        i: mask,
        mask: mask,
        end: false,
    }
}

impl Iterator for BitPattern {
    type Item = usize;
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
    use itertools::assert_equal;
    assert_equal(bit_pattern(0b0), vec![0]);
    assert_equal(bit_pattern(0b1), vec![0b0, 0b1]);
    assert_equal(
        bit_pattern(0b111),
        vec![0b000, 0b001, 0b010, 0b011, 0b100, 0b101, 0b110, 0b111],
    );
    assert_equal(bit_pattern(0b101), vec![0b000, 0b001, 0b100, 0b101]);
    assert_equal(
        bit_pattern(0b10_1011),
        vec![
            0b00_0000, 0b00_0001, 0b00_0010, 0b00_0011, 0b00_1000, 0b00_1001, 0b00_1010, 0b00_1011,
            0b10_0000, 0b10_0001, 0b10_0010, 0b10_0011, 0b10_1000, 0b10_1001, 0b10_1010, 0b10_1011,
        ],
    );
}

/// Standing Bit enumeration iterator.
/// # See also
/// [`bit_iter`]
#[derive(Clone)]
pub struct BitIter {
    i: usize,
}
/// Standing Bit enumeration iterator.
/// # Example
/// ```
/// # use klmisc::bit_iter;
/// let mut iter = bit_iter(0b11_0101);
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(4));
/// assert_eq!(iter.next(), Some(5));
/// assert_eq!(iter.next(), None);
/// ```
pub fn bit_iter(x: usize) -> BitIter {
    BitIter { i: x }
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
    use itertools::assert_equal;
    assert_equal(bit_iter(0), vec![]);
    assert_equal(bit_iter(0b0100_1101), vec![0, 2, 3, 6]);
}

#[derive(PartialEq, PartialOrd)]
pub struct Total<T>(pub T);
impl<T: PartialEq> Eq for Total<T> {}
impl<T: PartialOrd> Ord for Total<T> {
    fn cmp(&self, other: &Total<T>) -> std::cmp::Ordering {
        self.0.partial_cmp(&other.0).unwrap()
    }
}

pub fn atcg_to_index(c: char) -> usize {
    match c {
        'A' | 'a' => 0,
        'T' | 't' => 1,
        'C' | 'c' => 2,
        _ => 3,
    }
}
