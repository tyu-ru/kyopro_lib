use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// Modulation trait
pub trait Modulation: Clone + Copy + PartialEq + Eq {
    const MOD: u64;
}

/// Z/mZ field
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ModInt<M: Modulation> {
    x: u64,
    phantom: PhantomData<M>,
}

impl<M: Modulation> std::str::FromStr for ModInt<M> {
    type Err = <i64 as std::str::FromStr>::Err;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(|x| Self::from_signed(x))
    }
}
impl<M: Modulation> std::fmt::Display for ModInt<M> {
    fn fmt(&self, dest: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(dest, "{}", self.x)
    }
}
impl<M: Modulation> std::fmt::Debug for ModInt<M> {
    fn fmt(&self, dest: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(dest, "{}", self.x)
    }
}

impl<M: Modulation> ModInt<M> {
    #[inline]
    pub fn new(x: u64) -> Self {
        Self {
            x: x.rem_euclid(M::MOD),
            phantom: PhantomData,
        }
    }
    #[inline]
    pub fn from_signed(x: i64) -> Self {
        Self {
            x: x.rem_euclid(M::MOD as i64) as u64,
            phantom: PhantomData,
        }
    }
    #[inline]
    pub fn new_uncheck(x: u64) -> Self {
        Self {
            x,
            phantom: PhantomData,
        }
    }
    #[inline]
    pub fn val(&self) -> u64 {
        self.x
    }
}

macro_rules! def_from_trait {
    (u, $t:ty) => {
        impl<M: Modulation> std::convert::From<$t> for ModInt<M> {
            #[inline]
            fn from(x: $t) -> Self {
                Self::new(x as u64)
            }
        }
    };
    (i, $t:ty) => {
        impl<M: Modulation> std::convert::From<$t> for ModInt<M> {
            #[inline]
            fn from(x: $t) -> Self {
                Self::from_signed(x as i64)
            }
        }
    };
}

def_from_trait!(u, u8);
def_from_trait!(u, u16);
def_from_trait!(u, u32);
def_from_trait!(u, u64);
def_from_trait!(u, usize);
def_from_trait!(i, i8);
def_from_trait!(i, i16);
def_from_trait!(i, i32);
def_from_trait!(i, i64);
def_from_trait!(i, isize);

impl<M: Modulation> num::FromPrimitive for ModInt<M> {
    fn from_i64(n: i64) -> Option<Self> {
        Some(n.into())
    }
    fn from_u64(n: u64) -> Option<Self> {
        Some(n.into())
    }
}

impl<M: Modulation> num::Zero for ModInt<M> {
    fn zero() -> Self {
        Self::new_uncheck(0)
    }
    fn is_zero(&self) -> bool {
        self.x == 0
    }
}

impl<M: Modulation> num::One for ModInt<M> {
    fn one() -> Self {
        Self::new_uncheck(1)
    }
    fn is_one(&self) -> bool {
        self.x == 1
    }
}

impl<M: Modulation> Neg for ModInt<M> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self {
            x: if self.x == 0 { 0 } else { M::MOD - self.x },
            phantom: PhantomData,
        }
    }
}
impl<'a, M: Modulation> Neg for &'a ModInt<M> {
    type Output = ModInt<M>;
    #[inline]
    fn neg(self) -> ModInt<M> {
        -(*self)
    }
}

// from https://github.com/rust-lang/rust/blob/stable/library/core/src/internal_macros.rs
// implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are expected to be `Copy`able
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a, M: Modulation> $imp<ModInt<M>> for &'a ModInt<M> {
            type Output = <ModInt<M> as $imp<ModInt<M>>>::Output;
            #[inline]
            fn $method(self, other: ModInt<M>) -> <ModInt<M> as $imp<ModInt<M>>>::Output {
                $imp::$method(*self, other)
            }
        }
        impl<M: Modulation> $imp<&ModInt<M>> for ModInt<M> {
            type Output = <ModInt<M> as $imp<ModInt<M>>>::Output;
            #[inline]
            fn $method(self, other: &ModInt<M>) -> <ModInt<M> as $imp<ModInt<M>>>::Output {
                $imp::$method(self, *other)
            }
        }
        impl<M: Modulation> $imp<&ModInt<M>> for &ModInt<M> {
            type Output = <ModInt<M> as $imp<ModInt<M>>>::Output;
            #[inline]
            fn $method(self, other: &ModInt<M>) -> <ModInt<M> as $imp<ModInt<M>>>::Output {
                $imp::$method(*self, *other)
            }
        }
    };
}
// from https://github.com/rust-lang/rust/blob/stable/library/core/src/internal_macros.rs
// implements "T op= &U", based on "T op= U"
// where U is expected to be `Copy`able
macro_rules! forward_ref_op_assign {
    (impl $imp:ident, $method:ident) => {
        impl<M: Modulation> $imp<&ModInt<M>> for ModInt<M> {
            #[inline]
            fn $method(&mut self, other: &ModInt<M>) {
                $imp::$method(self, *other);
            }
        }
    };
}

macro_rules! decl_ops_from_op_assign {
    ($(impl $bi_tr:ident, $bi_me:ident from $as_tr:ident, $as_me:ident)*) => {
        $(
            impl<M: Modulation> $bi_tr for ModInt<M> {
                type Output = Self;
                #[inline]
                fn $bi_me(self, rhs: Self) -> Self {
                    let mut res = self;
                    res.$as_me(rhs);
                    res
                }
            }
            forward_ref_op_assign! {impl $as_tr, $as_me}
            forward_ref_binop! {impl $bi_tr, $bi_me}
        )*
    };
}

impl<M: Modulation> AddAssign for ModInt<M> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.x += rhs.x;
        if M::MOD <= self.x {
            self.x -= M::MOD;
        }
    }
}
impl<M: Modulation> SubAssign for ModInt<M> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        if self.x >= rhs.x {
            self.x -= rhs.x;
        } else {
            self.x += M::MOD - rhs.x;
        }
    }
}
impl<M: Modulation> MulAssign for ModInt<M> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        self.x *= rhs.x;
        self.x %= M::MOD;
    }
}
impl<M: Modulation> DivAssign for ModInt<M> {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self *= rhs.inv();
    }
}

decl_ops_from_op_assign! {
    impl Add, add from AddAssign, add_assign
    impl Sub, sub from SubAssign, sub_assign
    impl Mul, mul from MulAssign, mul_assign
    impl Div, div from DivAssign, div_assign
}

impl<M: Modulation> std::iter::Sum for ModInt<M> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new_uncheck(0), |s, x| s + x)
    }
}
impl<'a, M: Modulation> std::iter::Sum<&'a Self> for ModInt<M> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new_uncheck(0), |s, x| s + x)
    }
}
impl<M: Modulation> std::iter::Product for ModInt<M> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new_uncheck(1), |s, x| s * x)
    }
}
impl<'a, M: Modulation> std::iter::Product<&'a Self> for ModInt<M> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new_uncheck(1), |s, x| s * x)
    }
}

impl<M: Modulation> ModInt<M> {
    pub fn pow(&self, mut n: u64) -> Self {
        let mut res = Self::new_uncheck(1);
        let mut d = *self;
        while n != 0 {
            if n & 1 != 0 {
                res *= d;
            }
            d *= d;
            n >>= 1;
        }
        res
    }

    pub fn inv(&self) -> Self {
        let (x, _, _) = super::math::ext_gcd(self.x, M::MOD);
        Self::from(x)
    }

    pub fn gen_factorial(n: u64) -> Factorial<M> {
        let n = n as usize;
        let mut pos = vec![Self::new_uncheck(1); n + 1];
        let mut neg = vec![Self::new_uncheck(1); n + 1];
        for i in 1..n {
            pos[i + 1] = pos[i] * Self::new(i as u64 + 1);
        }
        neg[n] = pos[n].inv();
        for i in (1..n).rev() {
            neg[i] = neg[i + 1] * Self::new(i as u64 + 1);
        }

        Factorial { pos, neg }
    }
    pub fn gen_inv(n: u64) -> Vec<Self> {
        let mut res = vec![Self::new_uncheck(1); (n + 1) as usize];
        for i in 2..=n {
            res[i as usize] = Self::new_uncheck(M::MOD - M::MOD / i) * res[(M::MOD % i) as usize];
        }
        res
    }
}

pub struct Factorial<M: Modulation> {
    pos: Vec<ModInt<M>>,
    neg: Vec<ModInt<M>>,
}
impl<M: Modulation> Factorial<M> {
    pub fn factorial(&self, n: u64) -> ModInt<M> {
        self.pos[n as usize]
    }

    pub fn permutation(&self, n: u64, r: u64) -> ModInt<M> {
        if r > n {
            ModInt::new(0)
        } else {
            self.pos[n as usize] * self.neg[(n - r) as usize]
        }
    }

    pub fn binomial(&self, n: u64, r: u64) -> ModInt<M> {
        if r > n {
            ModInt::new(0)
        } else {
            self.pos[n as usize] * self.neg[r as usize] * self.neg[(n - r) as usize]
        }
    }
    pub fn cmb_with_rep(&self, n: u64, r: u64) -> ModInt<M> {
        self.binomial(n + r - 1, r)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone, Copy, PartialEq, Eq)]
    struct F;
    impl Modulation for F {
        const MOD: u64 = 7;
    }
    type Mint = ModInt<F>;

    #[test]
    fn test_modint_construct() {
        let x = Mint::new(12);
        assert_eq!(x.val(), 5);
        let y = x;
        assert_eq!(x.val(), 5);
        assert_eq!(y.val(), 5);

        let z = Mint::from_signed(-2);
        assert_eq!(z.val(), 5);

        let x = Mint::from(12);
        assert_eq!(x.val(), 5);
        let x = Mint::from(-2);
        assert_eq!(x.val(), 5);
    }
    #[test]
    fn test_modint_add() {
        let mut x = Mint::new(12) + Mint::new(3);
        assert_eq!(x.val(), 1);
        x += Mint::new(6);
        assert_eq!(x.val(), 0);
    }
    #[test]
    fn test_modint_sub() {
        let mut x = Mint::new(2) - Mint::new(5);
        assert_eq!(x.val(), 4);
        x -= Mint::new(5);
        assert_eq!(x.val(), 6);
        x -= Mint::new(1);
        assert_eq!(x.val(), 5);
        x -= Mint::new(6);
        assert_eq!(x.val(), 6);
    }
    #[test]
    fn test_modint_multi() {
        let mut x = Mint::new(2) * Mint::new(5);
        assert_eq!(x.val(), 3);
        x *= Mint::new(5);
        assert_eq!(x.val(), 1);
    }
    #[test]
    fn test_modint_pow() {
        assert_eq!(Mint::new(3).pow(0).val(), 1);
        assert_eq!(Mint::new(3).pow(1).val(), 3);
        assert_eq!(Mint::new(3).pow(2).val(), 2);
        assert_eq!(Mint::new(3).pow(3).val(), 6);
        assert_eq!(Mint::new(3).pow(4).val(), 4);
        assert_eq!(Mint::new(3).pow(5).val(), 5);
        assert_eq!(Mint::new(3).pow(6).val(), 1);
        assert_eq!(Mint::new(3).pow(7).val(), 3);
    }
    #[test]
    fn test_modint_inv() {
        assert_eq!(Mint::new(1).inv().val(), 1);
        assert_eq!(Mint::new(2).inv().val(), 4);
        assert_eq!(Mint::new(3).inv().val(), 5);
        assert_eq!(Mint::new(4).inv().val(), 2);
        assert_eq!(Mint::new(5).inv().val(), 3);
        assert_eq!(Mint::new(6).inv().val(), 6);
    }
    #[test]
    fn test_modint_div() {
        let mut x = Mint::new(2) / Mint::new(5);
        assert_eq!(x.val(), 6);
        x /= Mint::new(4);
        assert_eq!(x.val(), 5);
    }

    #[test]
    fn test_gen_inv() {
        assert_eq!(
            Mint::gen_inv(6).iter().map(|x| x.val()).collect::<Vec<_>>(),
            &[1, 1, 4, 5, 2, 3, 6]
        )
    }

    #[test]
    fn test_modint_factorial() {
        let fac = Mint::gen_factorial(5);
        let pos = fac.pos.iter().map(|x| x.val()).collect::<Vec<_>>();
        let neg = fac.neg.iter().map(|x| x.val()).collect::<Vec<_>>();
        assert_eq!(pos, &[1, 1, 2, 6, 3, 1]);
        assert_eq!(neg, &[1, 1, 4, 6, 5, 1]);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Mint::new(3)), "3");
    }

    #[test]
    fn test_iter_fold() {
        let dat = &[Mint::new(1), Mint::new(2), Mint::new(3), Mint::new(4)];
        assert_eq!(dat.iter().sum::<Mint>(), Mint::new(10));
        assert_eq!(dat.iter().product::<Mint>(), Mint::new(24));
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct F1_000_000_007;
impl Modulation for F1_000_000_007 {
    const MOD: u64 = 1_000_000_007;
}
pub type Mint1_000_000_007 = ModInt<F1_000_000_007>;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct F998_244_353;
impl Modulation for F998_244_353 {
    const MOD: u64 = 998_244_353;
}
pub type Mint998_244_353 = ModInt<F998_244_353>;
