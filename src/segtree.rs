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
    pub fn query<R: std::ops::RangeBounds<usize>>(&self, r: R) -> T {
        use std::ops::Bound;
        let s = match r.start_bound() {
            Bound::Included(&s) => s,
            Bound::Excluded(&s) => s + 1,
            Bound::Unbounded => 0,
        };
        let e = match r.end_bound() {
            Bound::Included(&e) => e + 1,
            Bound::Excluded(&e) => e,
            Bound::Unbounded => self.n,
        };
        self.query_impl(0, s..e, 0..self.n)
    }
    fn query_impl(&self, k: usize, r: std::ops::Range<usize>, a: std::ops::Range<usize>) -> T {
        if r.end <= a.start || a.end <= r.start {
            self.id.clone()
        } else if r.start <= a.start && a.end <= r.end {
            self.dat[k].clone()
        } else {
            let m = (a.start + a.end) / 2;
            (self.f)(
                &self.query_impl(k * 2 + 1, r.clone(), a.start..m),
                &self.query_impl(k * 2 + 2, r, m..a.end),
            )
        }
    }
}

#[test]
fn test_segtree() {
    let mut st = SegTree::build_from_slice(&[1, 2, 3, 4, 5], 0, |&a, &b| a + b);
    assert_eq!(st.len(), 8);
    assert_eq!(st.get_element(2), &3);
    assert_eq!(st.query(1..4), 9);
    assert_eq!(st.query(..), 15);
    assert_eq!(st.query(..4), 10);
    assert_eq!(st.query(2..), 12);
    assert_eq!(st.query(0..1), 1);
    assert_eq!(st.query(0..2), 3);
    assert_eq!(st.query(1..3), 5);
    st.update_by(0, |dat| *dat += 2);
    assert_eq!(st.query(0..4), 12);
}
