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

pub trait Monoid {
    type T: Clone;
    fn id(&self) -> Self::T;
    fn op(&self, lhs: &Self::T, rhs: &Self::T) -> Self::T;
}

pub struct GenericMonoid<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    id: T,
    op: F,
}

impl<T, F> GenericMonoid<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    pub fn new(id: T, op: F) -> Self {
        Self { id, op }
    }
}

impl<T, F> Monoid for GenericMonoid<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    type T = T;
    fn id(&self) -> Self::T {
        self.id.clone()
    }
    fn op(&self, lhs: &Self::T, rhs: &Self::T) -> Self::T {
        (self.op)(lhs, rhs)
    }
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
/// # use kyopro_lib::segtree::*;
/// // Range Minimum Query
/// let mut st = SegTree::build_from_slice(&[2,4,3,1,5], GenericMonoid::new(std::i32::MAX, |&a, &b|std::cmp::min(a,b)));
/// // Range Minimum Query (used declared monoid)
/// let mut st = SegTree::build_from_slice(&[2,4,3,1,5], monoid::Min::new());
///
/// assert_eq!(st.len(), 8);
///
/// assert_eq!(st.query(..), 1);
/// assert_eq!(st.query(1..3), 3);
///
/// st.update(3, 10);
/// assert_eq!(st.query(..4), 2);
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
    /// # Example
    /// ```
    /// # use kyopro_lib::segtree::{SegTree,GenericMonoid};
    /// // RMQ (with index)
    /// let st = SegTree::build_from_iter((0..5).map(|i|(0,i)), GenericMonoid::new((std::i32::MAX,0), |&a,&b|std::cmp::min(a,b)));
    /// ```
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

    /// Returns a reference to an element i.
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

    /// Update element i.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update(&mut self, i: usize, dat: M::T) {
        let i = self.n + i;
        self.dat[i] = dat;
        self.update_to_bottom_up(i);
    }
    /// Update element i by `f`.
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn update_by<F: Fn(&mut M::T)>(&mut self, i: usize, f: F) {
        let i = self.n + i;
        f(&mut self.dat[i]);
        self.update_to_bottom_up(i);
    }
    /// Update element i by x <- M::op(x, y).
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

    /// Range query
    /// # Time complexity
    /// Cost is `O(log N)`.
    pub fn query<R: RangeBounds<usize>>(&self, r: R) -> M::T {
        self.query_impl(1, &bound_to_range(r, 0..self.n), 0..self.n)
    }
    fn query_impl(&self, k: usize, r: &Range<usize>, a: Range<usize>) -> M::T {
        if !is_overlap(r, &a) {
            self.m.id()
        } else if is_include(r, &a) {
            self.dat[k].clone()
        } else {
            let m = (a.start + a.end) >> 1;
            self.m.op(
                &self.query_impl(k << 1 | 0, r, a.start..m),
                &self.query_impl(k << 1 | 1, r, m..a.end),
            )
        }
    }

    /// binary search
    pub fn max_right<F: Fn(&M::T) -> bool>(&self, l: usize, f: F) -> usize {
        // using trailing_zeros() instead of trailing_ones().
        // Because {integer}::trailing_ones() is >= Rust 1.46.0
        if l == self.n || !f(&self.dat[self.n + l]) {
            return l;
        }
        let mut s = self.m.id();
        let mut k = self.n + l;
        // search
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

    pub fn min_left<F: Fn(&M::T) -> bool>(&self, r: usize, f: F) -> usize {
        if r == 0 || !f(&self.dat[self.n + r - 1]) {
            return r;
        }
        let mut s = self.m.id();
        let mut k = self.n + r - 1;
        // search
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
    pub fn new_with_index(n: usize, m: M) -> Self {
        let id = m.id().0;
        Self::build_from_iter((0..n).map(|i| (id.clone(), i)), m)
    }
    pub fn build_from_slice_with_index(dat: &[T], m: M) -> Self {
        Self::build_from_iter(dat.iter().cloned().enumerate().map(|(i, x)| (x, i)), m)
    }
    pub fn build_from_iter_with_index<I: Iterator<Item = T>>(iter: I, m: M) -> Self {
        Self::build_from_iter(iter.enumerate().map(|(i, x)| (x, i)), m)
    }

    pub fn query_index<R: RangeBounds<usize>>(&self, r: R) -> usize {
        self.query(r).1
    }
}

pub mod monoid {
    use super::Monoid;
    use std::marker::PhantomData;

    macro_rules! decl_monoid {
        ($name:ident, [$($traits:path),*], [$id:block], [$lhs:ident,$rhs:ident, $op:block]) => {
            decl_monoid!($name, T, [$($traits),*], [$id], [$lhs, $rhs, $op]);
        };
        ($name:ident, $t:ty, [$($traits:path),*], [$id:block], [$lhs:ident, $rhs:ident, $op:block]) => {
            pub struct $name<T> where T:Clone, $(T:$traits),* {_mt:PhantomData<T>}
            impl<T> $name<T>
            where
                T: Clone, $(T : $traits),*
            {
                pub fn new() -> Self {
                    Self{_mt:PhantomData}
                }
            }
            impl<T> Monoid for $name<T>
            where
                T: Clone, $(T : $traits),*
            {
                type T = $t;
                fn id(&self) -> Self::T { $id }
                fn op(&self, $lhs: &Self::T, $rhs: &Self::T) -> Self::T {
                    $op
                }
            }
        };
    }

    decl_monoid!(
        Add,
        [num::Zero, std::ops::Add],
        [{ T::zero() }],
        [a, b, { a.clone() + b.clone() }]
    );
    decl_monoid!(
        Mul,
        [num::One, std::ops::Mul],
        [{ T::one() }],
        [a, b, { a.clone() * b.clone() }]
    );
    decl_monoid!(
        GCD,
        [num::Integer],
        [{ T::zero() }],
        [a, b, { num::integer::gcd(a.clone(), b.clone()) }]
    );
    decl_monoid!(
        LCM,
        [num::Integer],
        [{ T::one() }],
        [a, b, { num::integer::lcm(a.clone(), b.clone()) }]
    );

    use std::cmp::{max, min};
    decl_monoid!(
        Min,
        [num::Bounded, Ord],
        [{ T::max_value() }],
        [a, b, { min(a, b).clone() }]
    );
    decl_monoid!(
        Max,
        [num::Bounded, Ord],
        [{ T::min_value() }],
        [a, b, { max(a, b).clone() }]
    );
    decl_monoid!(
        MinPartialOrd,
        [num::Bounded, PartialOrd],
        [{ T::max_value() }],
        [a, b, {
            if a < b {
                a.clone()
            } else {
                b.clone()
            }
        }]
    );
    decl_monoid!(
        MaxPartialOrd,
        [num::Bounded, PartialOrd],
        [{ T::min_value() }],
        [a, b, {
            if a > b {
                a.clone()
            } else {
                b.clone()
            }
        }]
    );

    decl_monoid!(
        MinWihtLeftIndex,
        (T, usize),
        [num::Bounded, Ord],
        [{ (T::max_value(), 0) }],
        [a, b, { min(a, b).clone() }]
    );
    decl_monoid!(
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
        MaxWihtLeftIndex,
        (T, usize),
        [num::Bounded, Ord],
        [{ (T::max_value(), 0) }],
        [a, b, {
            if a.0 != b.0 {
                max(a, b).clone()
            } else {
                (a.0.clone(), min(a.1, b.1))
            }
        }]
    );
    decl_monoid!(
        MaxWihtRightIndex,
        (T, usize),
        [num::Bounded, Ord],
        [{ (T::min_value(), 0) }],
        [a, b, { max(a, b).clone() }]
    );
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

    let st = SegTree::build_from_slice(&[1, 2, 3, 4], monoid::Add::new());
    assert_eq!(st.query(2..), 7);
}

#[cfg(test)]
#[test]
fn test_segtree_max_right() {
    let st = SegTree::build_from_slice(&vec![1; 9], monoid::Add::new());

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
    let st = SegTree::build_from_slice(&vec![1; 9], monoid::Add::new());

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
        SegTree::build_from_slice_with_index(&[3, 2, 2, 4, 1], monoid::MinWihtLeftIndex::new());
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

    let mut st = SegTree::new(n, monoid::Add::new());
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
        assert_eq!(st.query(a..b), stup[a..b].iter().sum());
    }
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

/// Lazy evaluate Segment Tree. Supports range update and range query.
///
/// (`T`, `f`) must be monoid with `id` as identity.
///
/// (`U`, `g`) must be semigroup.
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
