/// Fewnick-Tree(Binary-Indexed-Tree)
pub struct FewnickTree<T>(Vec<T>);

impl<T: Clone + num::Num + std::ops::AddAssign> FewnickTree<T> {
    pub fn new(n: usize) -> Self {
        Self(vec![T::zero(); n + 1])
    }
    pub fn from_slice(dat: &[T]) -> Self {
        let mut v = vec![T::zero()];
        v.extend_from_slice(dat);
        for i in 1..dat.len() {
            let j = i + (i & i.wrapping_neg());
            if j < v.len() {
                let x = v[i].clone();
                v[j] += x;
            }
        }
        Self(v)
    }
    pub fn clear(&mut self) {
        for x in &mut self.0 {
            *x = T::zero();
        }
    }
    pub fn add(&mut self, mut i: usize, x: T) {
        i += 1;
        while i < self.0.len() {
            (self.0)[i] += x.clone();
            i += i & i.wrapping_neg();
        }
    }
    /// sum of [0, i)
    pub fn sum(&self, mut i: usize) -> T {
        // i+=1; i-=1; // 1-indexed & closed range convert
        let mut res = T::zero();
        while 0 < i {
            res += (self.0)[i].clone();
            i ^= i & i.wrapping_neg();
        }
        res
    }
}

impl<T: Clone + num::Num + std::ops::AddAssign + std::ops::Sub> FewnickTree<T> {
    pub fn sum_range(&self, r: std::ops::Range<usize>) -> T {
        self.sum(r.end) - self.sum(r.start)
    }
}

#[cfg(test)]
#[test]
fn test_bit() {
    let mut bit = FewnickTree::new(5);
    bit.add(3, 2);
    bit.add(0, 1);
    assert_eq!(bit.sum(0), 0);
    assert_eq!(bit.sum(1), 1);
    assert_eq!(bit.sum(2), 1);
    assert_eq!(bit.sum(3), 1);
    assert_eq!(bit.sum(4), 3);
    assert_eq!(bit.sum(5), 3);
}
