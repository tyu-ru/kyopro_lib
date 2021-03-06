pub struct RLE<T> {
    v: Vec<(T, usize)>,
    len: usize,
}

impl<T: std::cmp::PartialEq + Clone> RLE<T> {
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
            self.push(x.clone());
        }
    }
    pub fn pop(&mut self) -> Option<T> {
        let l = self.v.len();
        if l == 0 {
            None
        } else {
            let res = Some((self.v[l - 1].0).clone());
            if self.v[l - 1].1 == 0 {
                self.v.pop();
            } else if self.v[l - 1].1 == 1 {
                self.v.pop();
                self.len -= 1;
            } else {
                self.v[l - 1].1 -= 1;
                self.len -= 1;
            }
            res
        }
    }

    pub fn first(&self) -> Option<&T> {
        self.v.first().map(|(x, _)| x)
    }
    pub fn last(&self) -> Option<&T> {
        self.v.last().map(|(x, _)| x)
    }
}

impl<T> std::iter::IntoIterator for RLE<T> {
    type Item = (T, usize);
    type IntoIter = <Vec<Self::Item> as std::iter::IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.v.into_iter()
    }
}

#[cfg(test)]
#[test]
fn test_rle() {
    let mut rle = RLE::new();
    assert_eq!(rle.len(), 0);
    assert_eq!(rle.v, &[]);
    assert_eq!(rle.first(), None);
    assert_eq!(rle.last(), None);

    rle.push(12);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.first(), Some(&12));
    assert_eq!(rle.last(), Some(&12));
    assert_eq!(rle.v, &[(12, 1)]);
    rle.push(12);
    assert_eq!(rle.len(), 2);
    assert_eq!(rle.first(), Some(&12));
    assert_eq!(rle.last(), Some(&12));
    assert_eq!(rle.v, &[(12, 2)]);

    rle.push(65);
    assert_eq!(rle.len(), 3);
    assert_eq!(rle.first(), Some(&12));
    assert_eq!(rle.last(), Some(&65));
    assert_eq!(rle.v, &[(12, 2), (65, 1)]);

    rle.push_n(12, 2);
    assert_eq!(rle.len(), 5);
    assert_eq!(rle.first(), Some(&12));
    assert_eq!(rle.last(), Some(&12));
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 2)]);

    rle.push_n(12, 2);
    assert_eq!(rle.len(), 7);
    assert_eq!(rle.first(), Some(&12));
    assert_eq!(rle.last(), Some(&12));
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4)]);

    rle.extend_from_slice(&[34, 56, 56]);
    assert_eq!(rle.len(), 10);
    assert_eq!(rle.last(), Some(&56));
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4), (34, 1), (56, 2)]);

    assert_eq!(rle.pop(), Some(56));
    assert_eq!(rle.last(), Some(&56));
    assert_eq!(rle.len(), 9);
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4), (34, 1), (56, 1)]);

    assert_eq!(rle.pop(), Some(56));
    assert_eq!(rle.last(), Some(&34));
    assert_eq!(rle.len(), 8);
    assert_eq!(rle.v, &[(12, 2), (65, 1), (12, 4), (34, 1)]);
}

#[cfg(test)]
#[test]
fn test_rle_zero_width_push() {
    let mut rle = RLE::new();
    assert_eq!(rle.pop(), None);
    assert_eq!(rle.len(), 0);

    rle.push_zero(3);
    assert_eq!(rle.len(), 0);
    assert_eq!(rle.first(), Some(&3));
    assert_eq!(rle.last(), Some(&3));
    assert_eq!(rle.v, &[(3, 0)]);

    rle.push(3);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.first(), Some(&3));
    assert_eq!(rle.last(), Some(&3));
    assert_eq!(rle.v, &[(3, 1)]);

    rle.push_zero(3);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.first(), Some(&3));
    assert_eq!(rle.last(), Some(&3));
    assert_eq!(rle.v, &[(3, 1)]);

    rle.push_zero(2);
    assert_eq!(rle.len(), 1);
    assert_eq!(rle.first(), Some(&3));
    assert_eq!(rle.last(), Some(&2));
    assert_eq!(rle.v, &[(3, 1), (2, 0)]);

    rle.push(3);
    assert_eq!(rle.len(), 2);
    assert_eq!(rle.v, &[(3, 1), (2, 0), (3, 1)]);

    assert_eq!(rle.pop(), Some(3));
    assert_eq!(rle.pop(), Some(2));
    assert_eq!(rle.pop(), Some(3));
    assert_eq!(rle.pop(), None);
}

#[cfg(test)]
#[test]
fn test_rle_into_iter() {
    let mut rle = RLE::from_slice(&[3, 3, 3, 3, 1, 1]);
    rle.push_zero(2);
    rle.push_n(3, 1);
    itertools::assert_equal(rle, vec![(3, 4), (1, 2), (2, 0), (3, 1)]);
}
