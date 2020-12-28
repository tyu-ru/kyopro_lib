use std::ops::Range;
use std::ops::RangeBounds;
fn bound_to_range<R: RangeBounds<usize>>(r1: R, r2: Range<usize>) -> Range<usize> {
    use std::ops::Bound;
    let s = match r1.start_bound() {
        Bound::Included(&s) => s,
        Bound::Excluded(&s) => s + 1,
        Bound::Unbounded => r2.start,
    };
    let e = match r1.end_bound() {
        Bound::Included(&e) => e + 1,
        Bound::Excluded(&e) => e,
        Bound::Unbounded => r2.end,
    };
    std::cmp::max(s, r2.start)..std::cmp::min(e, r2.end)
}

#[cfg(test)]
#[test]
fn test_bound_to_range() {
    assert_eq!(bound_to_range(1..3, 0..4), 1..3);
    assert_eq!(bound_to_range(0..5, 1..4), 1..4);
    assert_eq!(bound_to_range(.., 0..4), 0..4);
    assert_eq!(bound_to_range(2.., 0..4), 2..4);
    assert_eq!(bound_to_range(..3, 0..4), 0..3);
    assert_eq!(bound_to_range(..=3, 0..4), 0..4);
}

fn is_overlap(r1: &Range<usize>, r2: &Range<usize>) -> bool {
    !(r2.end <= r1.start || r1.end <= r2.start)
}
fn is_include(r1: &Range<usize>, r2: &Range<usize>) -> bool {
    r1.start <= r2.start && r2.end <= r1.end
}

#[cfg(test)]
#[test]
fn test_range_overlap() {
    let check = |r1, r2, res| {
        assert_eq!(is_overlap(&r1, &r2), res);
        assert_eq!(is_overlap(&r2, &r1), res);
    };
    check(0..2, 0..2, true);
    check(0..2, 0..3, true);
    check(1..3, 0..3, true);
    check(1..2, 0..3, true);
    check(0..2, 1..1, true);
    check(0..2, 3..5, false);
    check(0..2, 2..4, false);
    check(0..2, 0..0, false);
    check(0..2, 2..2, false);
    check(0..2, 3..3, false);
}

#[cfg(test)]
#[test]
fn test_range_include() {
    let is_include = |r1, r2| is_include(&r1, &r2);
    assert_eq!(is_include(0..2, 0..2), true);
    assert_eq!(is_include(0..3, 1..2), true);
    assert_eq!(is_include(0..2, 3..5), false);
    assert_eq!(is_include(3..5, 0..2), false);
    assert_eq!(is_include(0..2, 0..3), false);
}

/// Segment Tree. Supports single element update and range query.
///
/// (`T`, `f`) must be monoid with `id` as identity.
///
/// In this data structure, the number of elements is an power of 2.
/// The number of elements is extended to a smallest power of 2 greater than or equal to specified.
/// (with each additional element filled with identity.)
/// In this docment, treat *N* as the (extended) number of elements.
///
/// # Example
/// ```
/// # use kyopro_lib::segtree::SegTree;
/// // Range Minimum Query
/// let mut st = SegTree::build_from_slice(&[2,4,3,1,5], std::i32::MAX, |&a, &b|std::cmp::min(a,b));
///
/// assert_eq!(st.len(), 8);
///
/// assert_eq!(st.query(..), 1);
/// assert_eq!(st.query(1..3), 3);
///
/// st.update(3, 10);
/// assert_eq!(st.query(..4), 2);
/// ```
pub struct SegTree<T, F> {
    /// element len
    n: usize,
    /// identity
    id: T,
    /// data buf
    dat: Vec<T>,
    /// binary operation
    f: F,
}

impl<T, F> SegTree<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    /// Constructs a new Segment Tree, all elements is initialized by `id`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn new(n: usize, id: T, f: F) -> Self {
        let n = n.next_power_of_two();
        Self {
            n: n,
            id: id.clone(),
            dat: vec![id; n * 2 - 1],
            f: f,
        }
    }

    /// Constructs a new Segment Tree, initialized by `dat`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_slice(dat: &[T], id: T, f: F) -> Self {
        let n = dat.len().next_power_of_two();
        let mut v = Vec::with_capacity(2 * n - 1);
        v.resize(n - 1, id.clone());
        v.extend_from_slice(dat);
        v.resize(2 * n - 1, id.clone());
        let mut st = Self {
            n: n,
            id: id,
            dat: v,
            f: f,
        };
        for i in (0..n - 1).rev() {
            st.update_at(i);
        }
        st
    }

    /// Constructs a new Segment Tree, initialized by `iter`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Example
    /// ```
    /// # use kyopro_lib::segtree::SegTree;
    /// // RMQ (with index)
    /// let st = SegTree::build_from_iter((0..5).map(|i|(0,i)), (std::i32::MAX,0), |&a,&b|std::cmp::min(a,b));
    /// ```
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_iter<I: Iterator<Item = T>>(iter: I, id: T, f: F) -> Self {
        use itertools::Itertools;
        Self::build_from_slice(&iter.collect_vec(), id, f)
    }

    /// Returns the number of elements in Segment Tree.
    #[inline]
    pub fn len(&self) -> usize {
        self.n
    }

    /// Returns a reference to an element i.
    /// # Panics
    /// Panics if `len() <= i`.
    /// # Time complexity
    /// Cost is `O(1)`.
    #[inline]
    pub fn get_element(&self, i: usize) -> &T {
        &self.dat[self.n + i - 1]
    }

    /// Extract a slice containing elements.
    /// # Time complexity
    /// Cost is `O(1)`.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.dat[self.n - 1..]
    }

    /// Update element i.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update(&mut self, i: usize, dat: T) {
        let i = self.n + i - 1;
        self.dat[i] = dat;
        self.update_to_bottom_up(i);
    }
    /// Update element i by `f`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update_by<F2: Fn(&mut T)>(&mut self, i: usize, f: F2) {
        let i = self.n + i - 1;
        f(&mut self.dat[i]);
        self.update_to_bottom_up(i);
    }

    #[inline]
    fn update_at(&mut self, i: usize) {
        self.dat[i] = (self.f)(&self.dat[i * 2 + 1], &self.dat[i * 2 + 2]);
    }
    #[inline]
    fn update_to_bottom_up(&mut self, mut i: usize) {
        while i != 0 {
            i = (i - 1) / 2;
            self.update_at(i);
        }
    }

    /// Range query
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn query<R: RangeBounds<usize>>(&self, r: R) -> T {
        self.query_impl(0, &bound_to_range(r, 0..self.n), 0..self.n)
    }
    fn query_impl(&self, k: usize, r: &Range<usize>, a: Range<usize>) -> T {
        if !is_overlap(r, &a) {
            self.id.clone()
        } else if is_include(r, &a) {
            self.dat[k].clone()
        } else {
            let m = (a.start + a.end) / 2;
            (self.f)(
                &self.query_impl(k * 2 + 1, r, a.start..m),
                &self.query_impl(k * 2 + 2, r, m..a.end),
            )
        }
    }
}

#[cfg(test)]
#[test]
fn test_segtree() {
    let mut st = SegTree::build_from_slice(&[1, 2, 3, 4, 5], 0, |&a, &b| a + b);
    assert_eq!(st.len(), 8);
    assert_eq!(st.get_element(2), &3);
    assert_eq!(st.as_slice(), &[1, 2, 3, 4, 5, 0, 0, 0]);
    assert_eq!(st.query(1..4), 9);
    assert_eq!(st.query(1..=4), 14);
    assert_eq!(st.query(..), 15);
    assert_eq!(st.query(..4), 10);
    assert_eq!(st.query(2..), 12);
    assert_eq!(st.query(0..0), 0);

    st.update_by(0, |dat| *dat += 2);
    assert_eq!(st.query(0..4), 12);
    assert_eq!(st.as_slice(), &[3, 2, 3, 4, 5, 0, 0, 0]);
}

pub struct LazySegTree<T, U, F, G, H> {
    n: usize,
    id: T,
    dat: Vec<T>,
    lazy: Vec<Option<U>>,
    f: F,
    g: G,
    h: H,
}

impl<T, U, F, G, H> LazySegTree<T, U, F, G, H>
where
    T: Clone,
    U: Clone,
    F: Fn(&T, &T) -> T,
    G: Fn(&U, &U) -> U,
    H: Fn(&T, &U, usize) -> T,
{
    pub fn new(n: usize, id: T, f: F, g: G, h: H) -> Self {
        let n = n.next_power_of_two();
        Self {
            n: n,
            id: id.clone(),
            dat: vec![id; 2 * n - 1],
            lazy: vec![None; 2 * n - 1],
            f: f,
            g: g,
            h: h,
        }
    }
    pub fn build_from_slice(dat: &[T], id: T, f: F, g: G, h: H) -> Self {
        let mut lst = Self::new(dat.len(), id, f, g, h);
        for i in 0..dat.len() {
            lst.dat[lst.n - 1 + i] = dat[i].clone();
        }
        for i in (0..lst.n - 1).rev() {
            lst.dat[i] = (lst.f)(&lst.dat[i * 2 + 1], &lst.dat[i * 2 + 2]);
        }
        lst
    }
    pub fn build_from_iter<I: Iterator<Item = T>>(iter: I, id: T, f: F, g: G, h: H) -> Self {
        use itertools::Itertools;
        Self::build_from_slice(&iter.collect_vec(), id, f, g, h)
    }

    pub fn len(&self) -> usize {
        self.n
    }

    fn marge_effect(&mut self, k: usize, x: &U) {
        if let Some(y) = self.lazy[k].take() {
            self.lazy[k] = Some((self.g)(&y, x));
        } else {
            self.lazy[k] = Some(x.clone());
        }
    }
    fn eval(&mut self, k: usize, l: usize) {
        if let Some(x) = self.lazy[k].take() {
            self.dat[k] = (self.h)(&self.dat[k], &x, l);
            if k < self.n - 1 {
                self.marge_effect(k * 2 + 1, &x);
                self.marge_effect(k * 2 + 2, &x);
            }
        }
    }

    pub fn update_range<R: RangeBounds<usize>>(&mut self, r: R, x: U) {
        self.update_range_impl(&bound_to_range(r, 0..self.n), 0, 0..self.n, &x)
    }
    fn update_range_impl(&mut self, r: &Range<usize>, k: usize, a: Range<usize>, x: &U) {
        if !is_overlap(r, &a) {
            self.eval(k, a.end - a.start);
            return;
        }
        if is_include(r, &a) {
            self.marge_effect(k, x);
            self.eval(k, a.end - a.start);
            return;
        }
        let m = (a.start + a.end) / 2;
        self.eval(k, a.end - a.start);
        self.update_range_impl(r, k * 2 + 1, a.start..m, x);
        self.update_range_impl(r, k * 2 + 2, m..a.end, x);
        self.dat[k] = (self.f)(&self.dat[k * 2 + 1], &self.dat[k * 2 + 2]);
    }

    pub fn query<R: RangeBounds<usize>>(&mut self, r: R) -> T {
        self.query_impl(&bound_to_range(r, 0..self.n), 0, 0..self.n)
    }
    fn query_impl(&mut self, r: &Range<usize>, k: usize, a: Range<usize>) -> T {
        if !is_overlap(r, &a) {
            self.id.clone()
        } else if is_include(r, &a) {
            self.eval(k, a.end - a.start);
            self.dat[k].clone()
        } else {
            let m = (a.start + a.end) / 2;
            self.eval(k, a.end - a.start);
            let x = self.query_impl(r, k * 2 + 1, a.start..m);
            let y = self.query_impl(r, k * 2 + 2, m..a.end);
            (self.f)(&x, &y)
        }
    }
}

#[cfg(test)]
#[test]
fn test_lazysegtree() {
    let mut lst = LazySegTree::build_from_slice(
        &[1, 2, 3, 4, 5],
        0,
        |&a, &b| a + b,
        |&a, &b| a + b,
        |&a, &b, l| a + b * l as i32,
    );
    assert_eq!(lst.len(), 8);
    assert_eq!(lst.query(1..4), 9);
    assert_eq!(lst.query(..), 15);
    assert_eq!(lst.query(..4), 10);
    assert_eq!(lst.query(2..), 12);
    assert_eq!(lst.query(0..0), 0);

    lst.update_range(.., 1);
    assert_eq!(lst.query(..), 23);
    assert_eq!(lst.query(0..4), 14);

    lst.update_range(.., -1);
    lst.update_range(1..4, 2);
    assert_eq!(lst.query(1..4), 15);
    assert_eq!(lst.query(0..2), 5);
}

#[cfg(test)]
#[test]
fn test_lazysegtree_stress() {
    use rand::distributions::{Distribution, Uniform};
    let n = 10_000;
    let d = Uniform::from(0..n);
    let d2 = Uniform::from(-(n as i64)..=n as i64);
    let mut rng = rand::thread_rng();

    let mut lst = LazySegTree::new(
        n,
        0,
        |&a, &b| a + b,
        |&a, &b| a + b,
        |&a, &b, l| a + b * l as i64,
    );
    let mut stup = vec![0; n];

    for _ in 0..n {
        let mut a = d.sample(&mut rng);
        let mut b = d.sample(&mut rng);
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }

        let c = d2.sample(&mut rng);
        for x in &mut stup[a..b] {
            *x += c;
        }
        lst.update_range(a..b, c);

        let mut a = d.sample(&mut rng);
        let mut b = d.sample(&mut rng);
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        assert_eq!(lst.query(a..b), stup[a..b].iter().sum());
    }
}
