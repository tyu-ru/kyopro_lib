/// Semigroup trait.
/// (`T`, `op`) must be semigroup.
/// # Expect
/// - associativity : `op(a, op(b, c)) == op(op(a, b), c)` (`a`, `b`, `c` <- Semigroup)
pub trait Semigroup {
    /// Type of monoid element.
    type T: Clone;
    /// Binary operation.
    fn op(&self, lhs: &Self::T, rhs: &Self::T) -> Self::T;
}

/// Semigroup that can specifiy the behavior in `Fn(..)`.
/// # Expect
/// - associativity : `op(a, op(b, c)) == op(op(a, b), c)` (`a`, `b`, `c` <- Semigroup)
pub struct GenericSemigroup<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    op: F,
    _mt: std::marker::PhantomData<T>,
}
impl<T, F> GenericSemigroup<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    pub fn new(op: F) -> Self {
        Self {
            op,
            _mt: std::marker::PhantomData,
        }
    }
}
pub fn semigroup<T, F>(op: F) -> GenericSemigroup<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    GenericSemigroup::new(op)
}
impl<T, F> Semigroup for GenericSemigroup<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    type T = T;
    fn op(&self, lhs: &T, rhs: &T) -> T {
        (self.op)(lhs, rhs)
    }
}

/// Monoid trait.
/// (`T`, `op`) must be monoid with `id` as identity.
///
/// # Expect
/// - associativity : `op(a, op(b, c)) == op(op(a, b), c)` (`a`, `b`, `c` <- Monoid)
/// - existence identity element : `op(a, id()) == op(id(), a) == a` && id() <- Monoid
pub trait Monoid: Semigroup {
    /// Returns identity element.
    fn id(&self) -> Self::T;
}

/// Monoid that can specifiy the behavior in `Fn(..)`.
/// # Expect
/// - associativity : `op(a, op(b, c)) == op(op(a, b), c)` (`a`, `b`, `c` <- Monoid)
/// - existence identity element : `op(a, id()) == op(id(), a) == a` && id() <- Monoid
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
    /// Constructs `GenericMonoid`
    /// # Expect
    /// - id: identity element.
    /// - op: binary operation.
    pub fn new(id: T, op: F) -> Self {
        Self { id, op }
    }
}

pub fn monoid<T, F>(id: T, op: F) -> GenericMonoid<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    GenericMonoid::new(id, op)
}

impl<T, F> Semigroup for GenericMonoid<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    type T = T;
    fn op(&self, lhs: &Self::T, rhs: &Self::T) -> Self::T {
        (self.op)(lhs, rhs)
    }
}
impl<T, F> Monoid for GenericMonoid<T, F>
where
    T: Clone,
    F: Fn(&T, &T) -> T,
{
    fn id(&self) -> Self::T {
        self.id.clone()
    }
}

pub mod predefined {
    use super::{Monoid, Semigroup};
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
        "Add monoid",
        Add,
        [num::Zero, std::ops::Add],
        [{ T::zero() }],
        [a, b, { a.clone() + b.clone() }]
    );
    decl_monoid!(
        "Multiple monoid",
        Mul,
        [num::One, std::ops::Mul],
        [{ T::one() }],
        [a, b, { a.clone() * b.clone() }]
    );
    decl_monoid!(
        "Bitwise Or monoid",
        BitOr,
        [num::Zero, std::ops::BitOr<Output = T>],
        [{ T::zero() }],
        [a, b, { a.clone() | b.clone() }]
    );
    decl_monoid!(
        "Bitwise And monoid",
        BitAnd,
        [num::Zero, std::ops::Not<Output = T>, std::ops::BitAnd<Output = T>],
        [{ !T::zero() }],
        [a, b, { a.clone() & b.clone() }]
    );
    decl_monoid!(
        "Bitwise Xor monoid",
        BitXor,
        [num::Zero, std::ops::BitXor<Output = T>],
        [{ T::zero() }],
        [a, b, { a.clone() ^ b.clone() }]
    );
    decl_monoid!(
        "Greatest common divisor moonoid",
        GCD,
        [num::Integer],
        [{ T::zero() }],
        [a, b, { num::integer::gcd(a.clone(), b.clone()) }]
    );
    decl_monoid!(
        "Least common multiple monoid",
        LCM,
        [num::Integer],
        [{ T::one() }],
        [a, b, { num::integer::lcm(a.clone(), b.clone()) }]
    );

    decl_monoid!(
        "Minimum value monoid",
        Min,
        [num::Bounded, Ord],
        [{ T::max_value() }],
        [a, b, { min(a, b).clone() }]
    );
    decl_monoid!(
        "Maximum value monoid",
        Max,
        [num::Bounded, Ord],
        [{ T::min_value() }],
        [a, b, { max(a, b).clone() }]
    );
    decl_monoid!(
        "Minimun value monoid for types for which `Ord` trait is not impl.",
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
        "Maximum value monoid for types for which `Ord` trait is not impl.",
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
}
