/// Binary-Indexed-Tree(Fewnick-Tree)
pub struct BIT<T>(Vec<T>);

impl<T: Copy + num::Num + std::ops::AddAssign> BIT<T> {
    pub fn new(n: usize) -> Self {
        Self(vec![T::zero(); n + 1])
    }
    pub fn clear(&mut self) {
        for x in &mut self.0 {
            *x = T::zero();
        }
    }
    pub fn add(&mut self, mut i: usize, x: T) {
        i += 1;
        while i < self.0.len() {
            (self.0)[i] += x;
            i += i & i.wrapping_neg();
        }
    }
    /// sum of [0, i)
    pub fn sum(&self, mut i: usize) -> T {
        // i+=1; i-=1; // 1-indexed & closed range convert
        let mut res = T::zero();
        while 0 < i {
            res += (self.0)[i];
            i ^= i & i.wrapping_neg();
        }
        res
    }
}

impl <T:Copy+num::Num+std::ops::AddAssign+std::ops::Sub> BIT<T> {
    pub fn sum_range(&self, r: std::ops::Range<usize>)->T {
        self.sum(r.end)-self.sum(r.start)
    }
}

#[test]
fn test_bit() {
    let mut bit = BIT::new(5);
    bit.add(3, 2);
    bit.add(0, 1);
    assert_eq!(bit.sum(0), 0);
    assert_eq!(bit.sum(1), 1);
    assert_eq!(bit.sum(2), 1);
    assert_eq!(bit.sum(3), 1);
    assert_eq!(bit.sum(4), 3);
    assert_eq!(bit.sum(5), 3);
}

pub struct DoubleBIT<T>(BIT<T>, BIT<T>);
impl<T> DoubleBIT<T>
where
    T: Copy + num::Num + num::FromPrimitive + std::ops::AddAssign + std::ops::Neg<Output = T>,
{
    pub fn new(n: usize) -> Self {
        Self(BIT::new(n), BIT::new(n))
    }
    pub fn clear(&mut self) {
        self.0.clear();
        self.1.clear();
    }
    pub fn add(&mut self, i: usize, x: T) {
        self.0.add(i, x);
    }

    pub fn add_range(&mut self, r: std::ops::Range<usize>, x: T) {
        let lx = T::from_usize(r.start).unwrap();
        let rx = T::from_usize(r.end).unwrap();
        self.0.add(r.start, -x * (lx - T::one()));
        self.0.add(r.end, x * rx);
        self.1.add(r.start, x);
        self.1.add(r.end, -x);
    }

    /// sum of [0, i)
    pub fn sum(&self, i: usize) -> T {
        self.0.sum(i) + self.1.sum(i)
    }
}

impl<T> DoubleBIT<T>
where
    T: Copy
        + num::Num
        + num::FromPrimitive
        + std::ops::AddAssign
        + std::ops::Neg<Output = T>
        + std::ops::Sub,
{
    pub fn sum_range(&self, r: std::ops::Range<usize>) -> T {
        self.sum(r.end) - self.sum(r.start)
    }
}
