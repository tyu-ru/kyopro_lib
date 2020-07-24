pub struct RLE<T> {
    v: Vec<(T, usize)>,
    len: usize,
}

impl<T: std::cmp::PartialEq + Copy> RLE<T> {
    pub fn new() -> Self {
        Self { v: vec![], len: 0 }
    }
    pub fn from_slice(s: &[T]) -> Self {
        let mut res = Self::new();
        res.extend_from_slice(s);
        res
    }

    pub fn v(&self) -> &Vec<(T, usize)> {
        &self.v
    }
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn push(&mut self, x: T) {
        let l = self.v.len();
        if l == 0 || self.v[l - 1].0 != x {
            self.v.push((x, 1));
        } else {
            self.v[l - 1].1 += 1;
        }
        self.len += 1;
    }
    pub fn push_n(&mut self, x: T, n: usize) {
        let l = self.v.len();
        if l == 0 || self.v[l - 1].0 != x {
            self.v.push((x, n));
        } else {
            self.v[l - 1].1 += n;
        }
        self.len += n;
    }
    pub fn push_zero(&mut self, x: T) {
        let l = self.v.len();
        if l == 0 || self.v[l - 1].0 != x {
            self.v.push((x, 0));
        }
    }
    pub fn extend_from_slice(&mut self, s: &[T]) {
        for x in s {
            self.push(*x);
        }
    }
    pub fn pop(&mut self) -> Option<T> {
        let l = self.v.len();
        if l == 0 {
            None
        } else {
            let res = Some(self.v[l - 1].0);
            if self.v[l - 1].1 == 1 {
                self.v.pop();
            } else {
                self.v[l - 1].1 -= 1;
            }
            self.len -= 1;
            res
        }
    }

    pub fn first(&self)->Option<T> {
        self.v.first().map(|(x,_)|*x)
    }
    pub fn last(&self)->Option<T> {
        self.v.last().map(|(x,_)|*x)
    }
}

#[test]
fn test_rle() {
    let mut rle = RLE::new();
    assert_eq!(rle.len(), 0);
    assert_eq!(rle.v, &[]);
    rle.push(12);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.v, &[(12, 1)]);
    rle.push(12);
    assert_eq!(rle.len(), 2);
    assert_eq!(rle.v, &[(12, 2)]);
    rle.push(65);
    assert_eq!(rle.len(), 3);
    assert_eq!(rle.v, &[(12, 2), (65, 1)]);
    rle.push_n(12, 2);
    assert_eq!(rle.len(), 5);
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 2)]);
    rle.push_n(12, 2);
    assert_eq!(rle.len(), 7);
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4)]);
    rle.extend_from_slice(&[34, 56, 56]);
    assert_eq!(rle.len(), 10);
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4), (34, 1), (56, 2)]);
    assert_eq!(rle.pop(), Some(56));
    assert_eq!(rle.len(), 9);
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4), (34, 1), (56, 1)]);
    assert_eq!(rle.pop(), Some(56));
    assert_eq!(rle.len(), 8);
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4), (34, 1)]);
    let mut rle = RLE::<i32>::new();
    assert_eq!(rle.pop(), None);
    assert_eq!(rle.len(), 0);
    rle.push_zero(3);
    assert_eq!(rle.len(), 0);
    assert_eq!(rle.v, &[(3, 0)]);
    rle.push(3);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.v, &[(3, 1)]);
    rle.push_zero(3);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.v, &[(3, 1)]);
    rle.push_zero(2);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.v, &[(3, 1), (2, 0)]);
    rle.push(3);
    assert_eq!(rle.len(), 2);
    assert_eq!(rle.v, &[(3, 1), (2, 0), (3, 1)]);
}
