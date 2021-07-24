use itertools::{traits::HomogeneousTuple, Itertools};
use std::iter::{once, DoubleEndedIterator, ExactSizeIterator};
use std::marker::PhantomData;

/// My iterator trait
pub trait MyIterator: Iterator {
    /// `position(|y| y == x)`
    fn position_eq(&mut self, x: Self::Item) -> Option<usize>
    where
        Self: Sized,
        Self::Item: PartialEq,
    {
        self.position(|y| y == x)
    }

    /// `rposition(|y| y == x)`
    fn rposition_eq(&mut self, x: Self::Item) -> Option<usize>
    where
        Self: Sized + ExactSizeIterator + DoubleEndedIterator,
        Self::Item: PartialEq,
    {
        self.rposition(|y| y == x)
    }

    /// `filter(|y| y == x).count()`
    fn eq_count(self, x: Self::Item) -> usize
    where
        Self: Sized,
        Self::Item: PartialEq,
    {
        self.filter(|y| *y == x).count()
    }

    /// `filter(|y| y != x).count()`
    fn neq_count(self, x: Self::Item) -> usize
    where
        Self: Sized,
        Self::Item: PartialEq,
    {
        self.filter(|y| *y != x).count()
    }

    /// `min().unwrap()`
    fn min_unwrap(self) -> Self::Item
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.min().expect("unwrap failed. [::min_unwrap()]")
    }

    /// `max().unwrap()`
    fn max_unwrap(self) -> Self::Item
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.max().expect("unwrap failed. [::max_unwrap()]")
    }

    /// Return an iterator adaptor that iterates over the permutatioins of the elements from an iterator.
    /// Iterator element can be any homogeneous tuple of type Self::Item with size up to 12.
    fn tuple_permutations<T>(self) -> TuplePermutations<Self, T>
    where
        Self: Sized + Iterator<Item = T::Item>,
        Self::Item: Clone,
        T: HomogeneousTuple,
    {
        TuplePermutations {
            iter: self.permutations(T::num_items()),
            _mt: PhantomData,
        }
    }
}

impl<T: ?Sized> MyIterator for T where T: Iterator {}

pub trait MyPeekable {
    type I: Iterator;
    fn next_if(
        &mut self,
        func: impl FnOnce(&<Self::I as Iterator>::Item) -> bool,
    ) -> Option<<Self::I as Iterator>::Item>;
}

impl<I: Iterator> MyPeekable for std::iter::Peekable<I> {
    type I = I;
    fn next_if(
        &mut self,
        func: impl FnOnce(&<I as Iterator>::Item) -> bool,
    ) -> Option<<I as Iterator>::Item> {
        if matches!(self.peek(), Some(item) if func(item)) {
            self.next()
        } else {
            None
        }
    }
}

pub struct TuplePermutations<I, T>
where
    I: Iterator<Item = T::Item>,
    I::Item: Clone,
    T: HomogeneousTuple,
{
    iter: itertools::Permutations<I>,
    _mt: PhantomData<T>,
}

impl<I, T> Iterator for TuplePermutations<I, T>
where
    I: Iterator<Item = T::Item>,
    I::Item: Clone,
    T: HomogeneousTuple,
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .and_then(|v| T::collect_from_iter_no_buf(v.into_iter()))
    }
}

pub fn sandwich<T>(l: T, m: impl Iterator<Item = T>, r: T) -> impl Iterator<Item = T> {
    once(l).chain(m).chain(once(r))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_position_eq() {
        let a = [1, 2, 3, 1];
        assert_eq!(a.iter().position_eq(&3), Some(2));
        assert_eq!(a.iter().position_eq(&4), None);
        assert_eq!(a.iter().rposition_eq(&1), Some(3));
        assert_eq!(a.iter().rposition_eq(&4), None);
    }

    #[test]
    fn test_eq_count() {
        let a = [1, 2, 3, 1];
        assert_eq!(a.iter().eq_count(&1), 2);
        assert_eq!(a.iter().eq_count(&2), 1);
        assert_eq!(a.iter().eq_count(&4), 0);
        assert_eq!(a.iter().neq_count(&1), 2);
        assert_eq!(a.iter().neq_count(&2), 3);
        assert_eq!(a.iter().neq_count(&4), 4);
    }

    #[test]
    fn test_min_max_unwrap() {
        let a = [3, 2, 5, 1, 4];
        assert_eq!(a.iter().min_unwrap(), &1);
        assert_eq!(a.iter().max_unwrap(), &5);
    }
    #[test]
    #[should_panic(expected = "unwrap failed. [::min_unwrap()]")]
    fn test_min_unwrap_panic() {
        let a: Vec<i32> = vec![];
        a.iter().min_unwrap();
    }
    #[test]
    #[should_panic(expected = "unwrap failed. [::max_unwrap()]")]
    fn test_max_unwrap_panic() {
        let a: Vec<i32> = vec![];
        a.iter().max_unwrap();
    }

    #[test]
    fn test_next_if() {
        let mut it = (0..10).peekable();
        assert_eq!(it.next_if(|&x| x == 0), Some(0));
        assert_eq!(it.next_if(|&x| x == 0), None);
        assert_eq!(it.next(), Some(1));
    }

    #[test]
    fn test_tuple_permutations() {
        let mut it = (0..3).tuple_permutations();
        assert_eq!(it.next(), Some((0, 1)));
        assert_eq!(it.next(), Some((0, 2)));
        assert_eq!(it.next(), Some((1, 0)));
        assert_eq!(it.next(), Some((1, 2)));
        assert_eq!(it.next(), Some((2, 0)));
        assert_eq!(it.next(), Some((2, 1)));
        assert_eq!(it.next(), None);

        let mut it = (0..3).tuple_permutations();
        assert_eq!(it.next(), Some((0, 1, 2)));
        assert_eq!(it.next(), Some((0, 2, 1)));
        assert_eq!(it.next(), Some((1, 0, 2)));
        assert_eq!(it.next(), Some((1, 2, 0)));
        assert_eq!(it.next(), Some((2, 0, 1)));
        assert_eq!(it.next(), Some((2, 1, 0)));
        assert_eq!(it.next(), None);
    }
}
