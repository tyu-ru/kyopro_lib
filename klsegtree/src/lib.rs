use klalgebra::*;
use std::ops::Range;
use std::ops::RangeBounds;

/// Convert `RangeBound<usize>` to `Range<usize>`.
/// The range of `r` is bound by lim.
#[inline]
fn bound_to_range<R: RangeBounds<usize>>(r: R, lim: Range<usize>) -> Range<usize> {
    use std::ops::Bound;
    let s = match r.start_bound() {
        Bound::Included(&s) => s,
        Bound::Excluded(&s) => s + 1,
        Bound::Unbounded => lim.start,
    };
    let e = match r.end_bound() {
        Bound::Included(&e) => e + 1,
        Bound::Excluded(&e) => e,
        Bound::Unbounded => lim.end,
    };
    std::cmp::max(s, lim.start)..std::cmp::min(e, lim.end)
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

/// Returns `true` if `r1` and `r2` have common range.
fn is_overlap(r1: &Range<usize>, r2: &Range<usize>) -> bool {
    !(r2.end <= r1.start || r1.end <= r2.start)
}
/// Returns `true` if r2 is a sub-range of `r1`
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
/// In this data structure, the number of elements is an power of 2.
/// The number of elements is extended to a smallest power of 2 greater than or equal to specified.
/// (with each additional element filled with identity.)
/// In this docment, treat *N* as the (extended) number of elements.
///
/// # Example
/// ```
/// # use klsegtree::*;
/// # use klalgebra::{self, monoid};
/// // Range Minimum Query
/// let mut st = SegTree::build_from_slice(&[2,4,3,1,5], monoid(std::i32::MAX, |&a, &b|std::cmp::min(a,b)));
/// // Range Minimum Query (used declared monoid)
/// let mut st = SegTree::build_from_slice(&[2,4,3,1,5], klalgebra::predefined::Min::new());
///
/// assert_eq!(st.len(), 8);
///
/// assert_eq!(st.query(..), 1);
/// assert_eq!(st.query(1..3), 3);
///
/// st.update(3, 10);
/// assert_eq!(st.query(..4), 2);
///
/// let st = SegTree::build_from_slice_with_index(&[2, 4, 2, 2, 3], predefined::MinWihtRightIndex::new());
/// assert_eq!(st.query_index(1..), 3);
///
/// ```
pub struct SegTree<M: Monoid> {
    /// element len
    n: usize,
    /// data buf
    dat: Vec<M::T>,
    /// monoid
    m: M,
}

impl<M> SegTree<M>
where
    M: Monoid,
{
    /// Constructs a new Segment Tree, all elements is initialized by `id`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn new(n: usize, m: M) -> Self {
        let n = n.next_power_of_two();
        Self {
            n,
            dat: vec![m.id(); n * 2],
            m,
        }
    }

    /// Constructs a new Segment Tree, initialized by `dat`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_slice(dat: &[M::T], m: M) -> Self {
        let n = dat.len().next_power_of_two();
        let mut v = Vec::with_capacity(2 * n);
        v.resize(n, m.id());
        v.extend_from_slice(dat);
        v.resize(2 * n, m.id());
        let mut st = Self { n, dat: v, m };
        for i in (1..n).rev() {
            st.update_at(i);
        }
        st
    }

    /// Constructs a new Segment Tree, initialized by `iter`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_iter<I: Iterator<Item = M::T>>(iter: I, m: M) -> Self {
        use itertools::Itertools;
        Self::build_from_slice(&iter.collect_vec(), m)
    }

    /// Returns the number of elements in Segment Tree.
    #[inline]
    pub fn len(&self) -> usize {
        self.n
    }

    /// Returns a reference to an element `i`.
    /// # Panics
    /// Panics if `len() <= i`.
    /// # Time complexity
    /// Cost is `O(1)`.
    #[inline]
    pub fn get(&self, i: usize) -> &M::T {
        &self.dat[self.n + i]
    }

    /// Extract a slice containing elements.
    /// # Time complexity
    /// Cost is `O(1)`.
    #[inline]
    pub fn as_slice(&self) -> &[M::T] {
        &self.dat[self.n..]
    }

    /// Update element `i`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update(&mut self, i: usize, dat: M::T) {
        let i = self.n + i;
        self.dat[i] = dat;
        self.update_to_bottom_up(i);
    }
    /// Update element `i` by `f`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update_by<F: Fn(&mut M::T)>(&mut self, i: usize, f: F) {
        let i = self.n + i;
        f(&mut self.dat[i]);
        self.update_to_bottom_up(i);
    }
    /// Update element `i` by x <- M::op(x, y).
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update_by_monoid_op(&mut self, i: usize, y: M::T) {
        let i = self.n + i;
        self.dat[i] = self.m.op(&self.dat[i], &y);
        self.update_to_bottom_up(i);
    }

    #[inline]
    fn update_at(&mut self, i: usize) {
        self.dat[i] = self.m.op(&self.dat[i << 1 | 0], &self.dat[i << 1 | 1]);
    }
    #[inline]
    fn update_to_bottom_up(&mut self, mut i: usize) {
        while i != 1 {
            i >>= 1;
            self.update_at(i);
        }
    }

    /// Range query. Returns `op(r.start .. r.end)`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn query<R: RangeBounds<usize>>(&self, r: R) -> M::T {
        let Range {
            start: mut l,
            end: mut r,
        } = bound_to_range(r, 0..self.n);
        let mut la = self.m.id();
        let mut ra = self.m.id();
        l += self.n;
        r += self.n;
        while l < r {
            if l & 1 == 1 {
                la = self.m.op(&la, &self.dat[l]);
                l += 1;
            }
            if r & 1 == 1 {
                r -= 1;
                ra = self.m.op(&self.dat[r], &ra);
            }
            l >>= 1;
            r >>= 1;
        }
        self.m.op(&la, &ra)
    }

    /// Returns maximum `r` than satisfies `f(query(l..r)) == true`.
    /// # Expect
    /// `f` must be monotonic with respect to increasing `r`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn max_right<F: Fn(&M::T) -> bool>(&self, l: usize, f: F) -> usize {
        // using trailing_zeros() instead of trailing_ones().
        // Because {integer}::trailing_ones() is >= Rust 1.46.0
        if l == self.n || !f(&self.dat[self.n + l]) {
            return l;
        }
        let mut s = self.m.id();
        let mut k = self.n + l;
        while (!k).trailing_zeros() != k.count_ones() {
            let s2 = self.m.op(&s, &self.dat[k]);
            if !f(&s2) {
                break;
            }
            s = s2;
            if k & 1 == 0 {
                k += 1;
            } else {
                k = (k + 1) >> 1;
            }
        }
        if (!k).trailing_zeros() == k.count_ones() {
            return self.n;
        }
        while k < self.n {
            let s2 = self.m.op(&s, &self.dat[k << 1]);
            if f(&s2) {
                s = s2;
                k = k << 1 | 1;
            } else {
                k <<= 1;
            }
        }
        k - self.n
    }

    /// Returns minimum `l` than satisfies `f(query(l..r)) == true`.
    /// # Expect
    /// `f` must be monotonic with respect to decreasing `l`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn min_left<F: Fn(&M::T) -> bool>(&self, r: usize, f: F) -> usize {
        if r == 0 || !f(&self.dat[self.n + r - 1]) {
            return r;
        }
        let mut s = self.m.id();
        let mut k = self.n + r - 1;
        while k.count_ones() != 1 {
            let s2 = self.m.op(&s, &self.dat[k]);
            if !f(&s2) {
                break;
            }
            s = s2;
            if k & 1 == 1 {
                k ^= 1;
            } else {
                k = (k - 1) >> 1;
            }
        }
        if k.count_ones() == 1 {
            return 0;
        }
        while k < self.n {
            let s2 = self.m.op(&s, &self.dat[k << 1 | 1]);
            if f(&s2) {
                s = s2;
                k <<= 1;
            } else {
                k = k << 1 | 1;
            }
        }
        k - self.n + 1
    }
}

impl<M, T> SegTree<M>
where
    M: Monoid<T = (T, usize)>,
    T: Clone,
{
    /// Constructs a new IndexedSegTree, all elements is initialized by (`id`, `index`).
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn new_with_index(n: usize, m: M) -> Self {
        let id = m.id().0;
        Self::build_from_iter((0..n).map(|i| (id.clone(), i)), m)
    }
    /// Constructs a new IndexedSegTree, initialized by (`dat`, index).
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_slice_with_index(dat: &[T], m: M) -> Self {
        Self::build_from_iter(dat.iter().cloned().enumerate().map(|(i, x)| (x, i)), m)
    }
    /// Constructs a new IndexedSegTree, initialized by (`iter`, index).
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_iter_with_index<I: Iterator<Item = T>>(iter: I, m: M) -> Self {
        Self::build_from_iter(iter.enumerate().map(|(i, x)| (x, i)), m)
    }

    /// Returns `.query().1`.
    pub fn query_index<R: RangeBounds<usize>>(&self, r: R) -> usize {
        self.query(r).1
    }
}

#[cfg(test)]
#[test]
fn test_segtree() {
    let mut st = SegTree::build_from_slice(&[1, 2, 3, 4, 5], GenericMonoid::new(0, |&a, &b| a + b));
    assert_eq!(st.len(), 8);
    assert_eq!(st.get(2), &3);
    assert_eq!(st.as_slice(), &[1, 2, 3, 4, 5, 0, 0, 0]);
    assert_eq!(st.query(1..4), 9);
    assert_eq!(st.query(1..=4), 14);
    assert_eq!(st.query(..), 15);
    assert_eq!(st.query(..4), 10);
    assert_eq!(st.query(2..), 12);
    assert_eq!(st.query(0..0), 0);

    st.update(1, 4);
    assert_eq!(st.query(..3), 8);

    st.update_by(0, |dat| *dat += 2);
    st.update_by_monoid_op(1, -6);
    assert_eq!(st.query(0..4), 8);
    assert_eq!(st.as_slice(), &[3, -2, 3, 4, 5, 0, 0, 0]);

    let st = SegTree::build_from_slice(&[1, 2, 3, 4], klalgebra::predefined::Add::new());
    assert_eq!(st.query(2..), 7);
}

#[cfg(test)]
#[test]
fn test_segtree_max_right() {
    let st = SegTree::build_from_slice(&vec![1; 9], klalgebra::predefined::Add::new());

    assert_eq!(st.max_right(1, |&s| s <= 3), 4);
    // assert_eq!(st.max_right(1, |&s| s <= 8), 16); // non-recurcive
    assert_eq!(st.max_right(1, |&s| s <= 1), 2);
    assert_eq!(st.max_right(0, |&s| s < 100), 16);
    assert_eq!(st.max_right(5, |&s| s < 100), 16);
    assert_eq!(st.max_right(0, |&s| s < 1), 0);
    assert_eq!(st.max_right(1, |&s| s < 1), 1);
    assert_eq!(st.max_right(9, |&s| s < 100), 16);
    assert_eq!(st.max_right(16, |&s| s < 100), 16);
}
#[cfg(test)]
#[test]
fn test_segtree_min_left() {
    let st = SegTree::build_from_slice(&vec![1; 9], klalgebra::predefined::Add::new());

    assert_eq!(st.min_left(6, |&s| s <= 3), 3);
    assert_eq!(st.min_left(6, |&s| s <= 6), 0);
    assert_eq!(st.min_left(6, |&s| s <= 1), 5);
    assert_eq!(st.min_left(16, |&s| s < 100), 0);
    assert_eq!(st.min_left(6, |&s| s < 100), 0);
    assert_eq!(st.min_left(16, |&s| s < 1), 9);
    assert_eq!(st.min_left(16, |&s| s < 0), 16);
    assert_eq!(st.min_left(6, |&s| s < 1), 6);
    assert_eq!(st.min_left(0, |&s| s < 100), 0);
}

#[cfg(test)]
#[test]
fn test_segtree_indexed_initialize() {
    let st =
        SegTree::build_from_slice_with_index(&[3, 2, 2, 4, 1], predefined::MinWihtLeftIndex::new());
    assert_eq!(st.query(..), (1, 4));
    assert_eq!(st.query(2..4), (2, 2));
    assert_eq!(st.query(1..4), (2, 1));
    assert_eq!(st.query_index(..), 4);
    assert_eq!(st.query_index(2..4), 2);
    assert_eq!(st.query_index(1..4), 1);
}

#[cfg(test)]
#[test]
fn test_segtree_stress() {
    use rand::distributions::{Distribution, Uniform};
    let n = 10_000;
    let d = Uniform::from(0..n);
    let d2 = Uniform::from(-(n as i64)..=n as i64);
    let mut rng = rand::thread_rng();

    let mut st = SegTree::new(n, klalgebra::predefined::Add::new());
    let mut stup = vec![0; n];

    for _ in 0..n {
        let i = d.sample(&mut rng);
        let c = d2.sample(&mut rng);
        stup[i] = c;
        st.update(i, c);

        let mut a = d.sample(&mut rng);
        let mut b = d.sample(&mut rng);
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        assert_eq!(st.query(a..b), stup[a..b].iter().sum::<i64>());
    }
}

/// Monoid with action trait.
/// Action must be semigroup.
/// # Expect
/// `act(g, act(f, x)) == act(op(g, f), x)` `g, f <- (S, op)`
pub trait MonoidWithAct {
    type M: Monoid;
    type S: Semigroup;

    fn m(&self) -> &Self::M;
    fn s(&self) -> &Self::S;
    /// Action on monoid
    fn act(
        &self,
        lhs: &<Self::M as Semigroup>::T,
        rhs: &<Self::S as Semigroup>::T,
        len: usize,
    ) -> <Self::M as Semigroup>::T;
}

/// Monoid with action that can specifiy the behavior in `Fn(..)`.
/// # Expect
/// - associativity : `op(a, op(b, c)) == op(op(a, b), c)` (`a`, `b`, `c` <- Semigroup)
pub struct GenericMonoidWithAct<M, S, F>
where
    M: Monoid,
    S: Semigroup,
    F: Fn(&M::T, &S::T, usize) -> M::T,
{
    m: M,
    s: S,
    act: F,
}
impl<M, S, F> GenericMonoidWithAct<M, S, F>
where
    M: Monoid,
    S: Semigroup,
    F: Fn(&M::T, &S::T, usize) -> M::T,
{
    pub fn new(m: M, s: S, act: F) -> Self {
        Self { m, s, act }
    }
}
pub fn monoid_with_act<M, S, F>(m: M, s: S, act: F) -> GenericMonoidWithAct<M, S, F>
where
    M: Monoid,
    S: Semigroup,
    F: Fn(&M::T, &S::T, usize) -> M::T,
{
    GenericMonoidWithAct { m, s, act }
}
impl<M, S, F> MonoidWithAct for GenericMonoidWithAct<M, S, F>
where
    M: Monoid,
    S: Semigroup,
    F: Fn(&M::T, &S::T, usize) -> M::T,
{
    type M = M;
    type S = S;

    fn m(&self) -> &M {
        &self.m
    }
    fn s(&self) -> &S {
        &self.s
    }
    fn act(&self, lhs: &M::T, rhs: &S::T, len: usize) -> M::T {
        (self.act)(lhs, rhs, len)
    }
}

/// Lazy evaluate Segment Tree. Supports range update and range query.
///
/// In this data structure, the number of elements is an power of 2.
/// The number of elements is extended to a smallest power of 2 greater than or equal to specified.
/// (with each additional element filled with identity.)
/// In this docment, treat *N* as the (extended) number of elements.
///
/// # Example
/// ```
/// # use klsegtree::*;
/// # use klalgebra::{self, monoid, semigroup};
/// // Range Set Query & Range Minimum Query
/// let mut lst = LazySegTree::build_from_slice(
///     &[2, 4, 3, 1, 5],
///     monoid_with_act(
///         monoid(std::i32::MAX, |a, b| *std::cmp::min(a, b)),
///         semigroup(|a, b| *std::cmp::min(a, b)),
///         |a, _: &i32, _| *a,
///     ),
/// );
/// // Range Set Query & Range Minimum Query (used declared monoid)
/// let mut lst = LazySegTree::build_from_slice(&[2,4,3,1,5], predefined::RSQRMinQ::new());
///
/// assert_eq!(lst.len(), 8);
///
/// assert_eq!(lst.query(..), 1);
/// assert_eq!(lst.query(1..3), 3);
///
/// lst.update_range(2.., 10);
/// assert_eq!(lst.query(1..4), 4);
///
/// let mut lst = LazySegTree::build_from_slice_with_index(
///     &[2, 4, 2, 2, 3],
///     monoid_with_act(
///         predefined::MinWihtRightIndex::new(),
///         predefined::Set::new(),
///         |a, b, _| (*b, a.1),
///     )
/// );
/// assert_eq!(lst.query_index(1..), 3);
/// ```
pub struct LazySegTree<MWA, M, S>
where
    MWA: MonoidWithAct<M = M, S = S>,
    M: Monoid,
    S: Semigroup,
{
    n: usize,
    mwa: MWA,
    dat: Vec<M::T>,
    lazy: Vec<Option<S::T>>,
}

impl<MWA, M, S> LazySegTree<MWA, M, S>
where
    MWA: MonoidWithAct<M = M, S = S>,
    M: Monoid,
    S: Semigroup,
{
    /// Constructs a new Lazy Segment Tree, all elements is initialized by `id`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn new(n: usize, mwa: MWA) -> Self {
        let n = n.next_power_of_two();
        let id = mwa.m().id();
        Self {
            n,
            mwa,
            dat: vec![id; 2 * n],
            lazy: vec![None; 2 * n],
        }
    }

    /// Constructs a new Lazy Segment Tree, initialized by `dat`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_slice(dat: &[M::T], mwa: MWA) -> Self {
        let mut lst = Self::new(dat.len(), mwa);
        for i in 0..dat.len() {
            lst.dat[lst.n + i] = dat[i].clone();
        }
        for i in (1..lst.n).rev() {
            lst.dat[i] = lst.mwa.m().op(&lst.dat[i << 1], &lst.dat[i << 1 | 1]);
        }
        lst
    }

    /// Constructs a new Lazy Segment Tree, initialized by `iter`.
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_iter<I: Iterator<Item = M::T>>(iter: I, mwa: MWA) -> Self {
        use itertools::Itertools;
        Self::build_from_slice(&iter.collect_vec(), mwa)
    }

    /// Returns the number of elements in Segment Tree.
    pub fn len(&self) -> usize {
        self.n
    }

    fn marge_effect(&mut self, k: usize, x: &S::T) {
        if let Some(y) = self.lazy[k].take() {
            self.lazy[k] = Some(self.mwa.s().op(x, &y));
        } else {
            self.lazy[k] = Some(x.clone());
        }
    }
    fn eval(&mut self, k: usize, l: usize) {
        if let Some(x) = self.lazy[k].take() {
            self.dat[k] = self.mwa.act(&self.dat[k], &x, l);
            if k < self.n {
                self.marge_effect(k << 1 | 0, &x);
                self.marge_effect(k << 1 | 1, &x);
            }
        }
    }

    /// Update range `r`
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update_range<R: RangeBounds<usize>>(&mut self, r: R, x: S::T) {
        self.update_range_impl(&bound_to_range(r, 0..self.n), 1, 0..self.n, &x)
    }
    fn update_range_impl(&mut self, r: &Range<usize>, k: usize, a: Range<usize>, x: &S::T) {
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
        self.update_range_impl(r, k << 1 | 0, a.start..m, x);
        self.update_range_impl(r, k << 1 | 1, m..a.end, x);
        self.dat[k] = self
            .mwa
            .m()
            .op(&self.dat[k << 1 | 0], &self.dat[k << 1 | 1]);
    }

    /// Range query. Returns `op(r.start .. r.end)`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn query<R: RangeBounds<usize>>(&mut self, r: R) -> M::T {
        self.query_impl(&bound_to_range(r, 0..self.n), 1, 0..self.n)
    }
    fn query_impl(&mut self, r: &Range<usize>, k: usize, a: Range<usize>) -> M::T {
        if !is_overlap(r, &a) {
            self.mwa.m().id()
        } else if is_include(r, &a) {
            self.eval(k, a.end - a.start);
            self.dat[k].clone()
        } else {
            let m = (a.start + a.end) / 2;
            self.eval(k, a.end - a.start);
            let x = self.query_impl(r, k << 1 | 0, a.start..m);
            let y = self.query_impl(r, k << 1 | 1, m..a.end);
            self.mwa.m().op(&x, &y)
        }
    }
}

impl<MWA, M, S, T> LazySegTree<MWA, M, S>
where
    MWA: MonoidWithAct<M = M, S = S>,
    M: Monoid<T = (T, usize)>,
    S: Semigroup,
    T: Clone,
{
    /// Constructs a new IndexedLazySegTree, all elements is initialized by (`id`, `index`).
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn new_with_index(n: usize, mwa: MWA) -> Self {
        let id = mwa.m().id().0;
        Self::build_from_iter((0..n).map(|i| (id.clone(), i)), mwa)
    }
    /// Constructs a new IndexedLazySegTree, initialized by (`dat`, index).
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_slice_with_index(dat: &[T], mwa: MWA) -> Self {
        Self::build_from_iter(dat.iter().cloned().enumerate().map(|(i, x)| (x, i)), mwa)
    }
    /// Constructs a new IndexedLazySegTree, initialized by (`iter`, index).
    /// The number of elements will be expanded as needed.
    ///
    /// # Time complexity
    /// Cost is `O(N)`.
    pub fn build_from_iter_with_index<I: Iterator<Item = T>>(iter: I, mwa: MWA) -> Self {
        Self::build_from_iter(iter.enumerate().map(|(i, x)| (x, i)), mwa)
    }

    /// Returns `.query().1`.
    pub fn query_index<R: RangeBounds<usize>>(&mut self, r: R) -> usize {
        self.query(r).1
    }
}

#[cfg(test)]
#[test]
fn test_lazysegtree() {
    let mut lst = LazySegTree::build_from_slice(
        &[1, 2, 3, 4, 5],
        monoid_with_act(
            klalgebra::predefined::Add::new(),
            klalgebra::predefined::Add::new(),
            |&a, &b, l| a + b * l as i32,
        ),
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

// #[cfg(test)]
// #[test]
// fn test_lazysegtree_max_right() {
//     let mut lst = LazySegTree::build_from_slice(
//         &vec![1; 9],
//         monoid_with_act(
//             klalgebra::predefined::Add::new(),
//             klalgebra::predefined::Add::new(),
//             |a: &i64, b: &i64, l| a + b * l as i64,
//         ),
//     );

//     assert_eq!(lst.max_right(1, |&s| s <= 3), 4);
//     // assert_eq!(lst.max_right(1, |&s| s <= 8), 16); // non-recurcive
//     assert_eq!(lst.max_right(1, |&s| s <= 1), 2);
//     assert_eq!(lst.max_right(0, |&s| s < 100), 16);
//     assert_eq!(lst.max_right(5, |&s| s < 100), 16);
//     assert_eq!(lst.max_right(0, |&s| s < 1), 0);
//     assert_eq!(lst.max_right(1, |&s| s < 1), 1);
//     assert_eq!(lst.max_right(9, |&s| s < 100), 16);
//     assert_eq!(lst.max_right(16, |&s| s < 100), 16);

//     lst.update_range(2..4, -1);
//     assert_eq!(lst.max_right(0, |&s| s <= 3), 5);
//     lst.update_range(5..7, -1);
//     assert_eq!(lst.max_right(5, |&s| s <= 1), 8);
// }
// #[cfg(test)]
// #[test]
// fn test_lazysegtree_min_left() {
//     let mut lst = LazySegTree::build_from_slice(
//         &vec![1; 9],
//         monoid_with_act(
//             klalgebra::predefined::Add::new(),
//             klalgebra::predefined::Add::new(),
//             |a: &i64, b: &i64, l| a + b * l as i64,
//         ),
//     );

//     assert_eq!(lst.min_left(6, |&s| s <= 3), 3);
//     assert_eq!(lst.min_left(6, |&s| s <= 6), 0);
//     assert_eq!(lst.min_left(6, |&s| s <= 1), 5);
//     assert_eq!(lst.min_left(16, |&s| s < 100), 0);
//     assert_eq!(lst.min_left(6, |&s| s < 100), 0);
//     assert_eq!(lst.min_left(16, |&s| s < 1), 9);
//     assert_eq!(lst.min_left(16, |&s| s < 0), 16);
//     assert_eq!(lst.min_left(6, |&s| s < 1), 6);
//     assert_eq!(lst.min_left(0, |&s| s < 100), 0);

//     lst.update_range(2..4, -1);
//     assert_eq!(lst.min_left(5, |&s| s <= 2), 1);
//     lst.update_range(5..7, -1);
//     assert_eq!(lst.min_left(6, |&s| s <= 1), 4);
// }

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
        monoid_with_act(
            klalgebra::predefined::Add::new(),
            klalgebra::predefined::Add::new(),
            |&a: &i64, &b: &i64, l| a + b * l as i64,
        ),
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

/// Predefined monoids.
pub mod predefined {
    use super::{Monoid, MonoidWithAct, Semigroup};
    use std::cmp::{max, min};
    use std::marker::PhantomData;

    macro_rules! decl_monoid {
        ($doc: expr, $name:ident, [$($traits:path),*], [$id:block], [$lhs:ident,$rhs:ident, $op:block]) => {
            decl_monoid!($doc, $name, T, [$($traits),*], [$id], [$lhs, $rhs, $op]);
        };
        ($doc: expr, $name:ident, $t:ty, [$($traits:path),*], [$id:block], [$lhs:ident, $rhs:ident, $op:block]) => {
            #[doc = $doc]
            pub struct $name<T> where T:Clone, $(T:$traits),* {_mt:PhantomData<T>}
            impl<T> $name<T>
            where
                T: Clone, $(T : $traits),*
            {
                pub fn new() -> Self {
                    Self{_mt:PhantomData}
                }
            }
            impl<T> Semigroup for $name<T>
            where
                T: Clone, $(T : $traits),*
            {
                type T = $t;
                fn op(&self, $lhs: &Self::T, $rhs: &Self::T) -> Self::T {
                    $op
                }
            }
            impl<T> Monoid for $name<T>
            where
                T: Clone, $(T : $traits),*
            {
                fn id(&self) -> Self::T { $id }
            }
        };
    }

    decl_monoid!(
        "Minimun value monoid with leftmost index. <br> # See also <br> `SegTree::new_with_index()`",
        MinWihtLeftIndex,
        (T, usize),
        [num::Bounded, Ord],
        [{ (T::max_value(), 0) }],
        [a, b, { min(a, b).clone() }]
    );
    decl_monoid!(
        "Minimun value monoid with rightmost index. <br> # See also <br> `SegTree::new_with_index()`",
        MinWihtRightIndex,
        (T, usize),
        [num::Bounded, Ord],
        [{ (T::max_value(), 0) }],
        [a, b, {
            if a.0 != b.0 {
                min(a, b).clone()
            } else {
                (a.0.clone(), max(a.1, b.1))
            }
        }]
    );
    decl_monoid!(
        "Maximun value monoid with leftmost index. <br> # See also <br> `SegTree::new_with_index()`",
        MaxWihtLeftIndex,
        (T, usize),
        [num::Bounded, Ord],
        [{ (T::min_value(), 0) }],
        [a, b, {
            if a.0 != b.0 {
                max(a, b).clone()
            } else {
                (a.0.clone(), min(a.1, b.1))
            }
        }]
    );
    decl_monoid!(
        "Maximun value monoid with rightmost index. <br> # See also <br> `SegTree::new_with_index()`",
        MaxWihtRightIndex,
        (T, usize),
        [num::Bounded, Ord],
        [{ (T::min_value(), 0) }],
        [a, b, { max(a, b).clone() }]
    );

    /// Set action
    pub struct Set<T: Clone> {
        _mt: PhantomData<T>,
    }
    impl<T: Clone> Set<T> {
        pub fn new() -> Self {
            Self { _mt: PhantomData }
        }
    }
    impl<T: Clone> Semigroup for Set<T> {
        type T = T;
        fn op(&self, lhs: &T, _: &T) -> T {
            lhs.clone()
        }
    }

    /// Range set query & range min query.
    pub struct RSQRMinQ<T: Clone + Ord + num::Bounded> {
        m: klalgebra::predefined::Min<T>,
        s: Set<T>,
    }
    impl<T: Clone + Ord + num::Bounded> RSQRMinQ<T> {
        pub fn new() -> Self {
            Self {
                m: klalgebra::predefined::Min::new(),
                s: Set::new(),
            }
        }
    }
    impl<T: Clone + Ord + num::Bounded> MonoidWithAct for RSQRMinQ<T> {
        type M = klalgebra::predefined::Min<T>;
        type S = Set<T>;
        fn m(&self) -> &Self::M {
            &self.m
        }
        fn s(&self) -> &Self::S {
            &self.s
        }
        fn act(&self, _: &T, rhs: &T, _: usize) -> T {
            rhs.clone()
        }
    }

    /// Range set query & range max query.
    pub struct RSQRMaxQ<T: Clone + Ord + num::Bounded> {
        m: klalgebra::predefined::Max<T>,
        s: Set<T>,
    }
    impl<T: Clone + Ord + num::Bounded> RSQRMaxQ<T> {
        pub fn new() -> Self {
            Self {
                m: klalgebra::predefined::Max::new(),
                s: Set::new(),
            }
        }
    }
    impl<T: Clone + Ord + num::Bounded> MonoidWithAct for RSQRMaxQ<T> {
        type M = klalgebra::predefined::Max<T>;
        type S = Set<T>;
        fn m(&self) -> &Self::M {
            &self.m
        }
        fn s(&self) -> &Self::S {
            &self.s
        }
        fn act(&self, _: &T, rhs: &T, _: usize) -> T {
            rhs.clone()
        }
    }

    /// Range set query & range add query
    pub struct RSQRAQ<T>
    where
        T: Clone
            + std::ops::Add
            + std::ops::Mul<Output = T>
            + num::Zero
            + num::Bounded
            + num::FromPrimitive,
    {
        m: klalgebra::predefined::Add<T>,
        s: Set<T>,
    }
    impl<T> RSQRAQ<T>
    where
        T: Clone
            + std::ops::Add
            + std::ops::Mul<Output = T>
            + num::Zero
            + num::Bounded
            + num::FromPrimitive,
    {
        pub fn new() -> Self {
            Self {
                m: klalgebra::predefined::Add::new(),
                s: Set::new(),
            }
        }
    }
    impl<T> MonoidWithAct for RSQRAQ<T>
    where
        T: Clone
            + std::ops::Add
            + std::ops::Mul<Output = T>
            + num::Zero
            + num::Bounded
            + num::FromPrimitive,
    {
        type M = klalgebra::predefined::Add<T>;
        type S = Set<T>;

        fn m(&self) -> &Self::M {
            &self.m
        }
        fn s(&self) -> &Self::S {
            &self.s
        }
        fn act(&self, _: &T, rhs: &T, len: usize) -> T {
            rhs.clone() * T::from_usize(len).unwrap()
        }
    }

    /// Range add query & range add query.
    pub struct RAQRSQ<T>
    where
        T: Clone + std::ops::Add + std::ops::Mul<Output = T> + num::Zero + num::FromPrimitive,
    {
        m: klalgebra::predefined::Add<T>,
    }
    impl<T> RAQRSQ<T>
    where
        T: Clone + std::ops::Add + std::ops::Mul<Output = T> + num::Zero + num::FromPrimitive,
    {
        pub fn new() -> Self {
            Self {
                m: klalgebra::predefined::Add::new(),
            }
        }
    }
    impl<T> MonoidWithAct for RAQRSQ<T>
    where
        T: Clone + std::ops::Add + std::ops::Mul<Output = T> + num::Zero + num::FromPrimitive,
    {
        type M = klalgebra::predefined::Add<T>;
        type S = klalgebra::predefined::Add<T>;

        fn m(&self) -> &Self::M {
            &self.m
        }
        fn s(&self) -> &Self::S {
            &self.m
        }

        fn act(&self, lhs: &T, rhs: &T, len: usize) -> T {
            lhs.clone() + rhs.clone() * T::from_usize(len).unwrap()
        }
    }

    /// Range add query & range min query.
    pub struct RAQRMinQ<T: Clone + Ord + num::Bounded + num::Zero> {
        m: klalgebra::predefined::Min<T>,
        s: klalgebra::predefined::Add<T>,
    }
    impl<T: Clone + Ord + num::Bounded + num::Zero> RAQRMinQ<T> {
        pub fn new() -> Self {
            Self {
                m: klalgebra::predefined::Min::new(),
                s: klalgebra::predefined::Add::new(),
            }
        }
    }
    impl<T: Clone + Ord + num::Bounded + num::Zero> MonoidWithAct for RAQRMinQ<T> {
        type M = klalgebra::predefined::Min<T>;
        type S = klalgebra::predefined::Add<T>;
        fn m(&self) -> &Self::M {
            &self.m
        }
        fn s(&self) -> &Self::S {
            &self.s
        }
        fn act(&self, lhs: &T, rhs: &T, _: usize) -> T {
            lhs.clone() + rhs.clone()
        }
    }
    /// Range add query & range max query.
    pub struct RAQRMaxQ<T: Clone + Ord + num::Bounded + num::Zero> {
        m: klalgebra::predefined::Max<T>,
        s: klalgebra::predefined::Add<T>,
    }
    impl<T: Clone + Ord + num::Bounded + num::Zero> RAQRMaxQ<T> {
        pub fn new() -> Self {
            Self {
                m: klalgebra::predefined::Max::new(),
                s: klalgebra::predefined::Add::new(),
            }
        }
    }
    impl<T: Clone + Ord + num::Bounded + num::Zero> MonoidWithAct for RAQRMaxQ<T> {
        type M = klalgebra::predefined::Max<T>;
        type S = klalgebra::predefined::Add<T>;
        fn m(&self) -> &Self::M {
            &self.m
        }
        fn s(&self) -> &Self::S {
            &self.s
        }
        fn act(&self, lhs: &T, rhs: &T, _: usize) -> T {
            lhs.clone() + rhs.clone()
        }
    }
}
