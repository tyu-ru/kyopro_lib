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
    (u, $($t: ty) +) => {
        $(def_from_trait!{u, $t})*
    };
    (i, $($t: ty) +) => {
        $(def_from_trait!{i, $t})*
    };
}

def_from_trait!(u, u8 u16 u32 u64 u128 usize);
def_from_trait!(i, i8 i16 i32 i64 i128 isize);

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
    pub fn pow<T: num::PrimInt + num::Unsigned>(&self, mut n: T) -> Self {
        let mut res = Self::new_uncheck(1);
        let mut d = *self;
        while n != T::zero() {
            if n & T::one() != T::zero() {
                res *= d;
            }
            d *= d;
            n = n >> 1;
        }
        res
    }
    pub fn powi<T: num::PrimInt + num::Signed>(&self, mut n: T) -> Self {
        let mut res = Self::new_uncheck(1);
        let mut d = *self;
        if n.is_negative() {
            d = d.inv();
            n = n.abs();
        }
        while n != T::zero() {
            if n & T::one() != T::zero() {
                res *= d;
            }
            d *= d;
            n = n >> 1;
        }
        res
    }

    pub fn inv(&self) -> Self {
        let (x, _, _) = klmath::ext_gcd(self.x, M::MOD);
        Self::from(x)
    }

    pub fn gen_factorial<T: num::ToPrimitive + num::Unsigned>(n: T) -> Factorial<M> {
        let n = n.to_usize().unwrap();
        let mut pos = vec![Self::new_uncheck(1); n + 1];
        let mut neg = vec![Self::new_uncheck(1); n + 1];
        for i in 1..n {
            pos[i + 1] = pos[i] * Self::from(i + 1);
        }
        neg[n] = pos[n].inv();
        for i in (1..n).rev() {
            neg[i] = neg[i + 1] * Self::from(i + 1);
        }
        Factorial { pos, neg }
    }
    pub fn gen_inv<T: num::ToPrimitive + num::Unsigned>(n: T) -> Vec<Self> {
        let n = n.to_usize().unwrap();
        let mut res = vec![Self::new_uncheck(1); n + 1];
        for i in 2..=n {
            res[i] = Self::new_uncheck(M::MOD - M::MOD / i as u64) * res[M::MOD as usize % i];
        }
        res
    }
}

pub struct Factorial<M: Modulation> {
    pos: Vec<ModInt<M>>,
    neg: Vec<ModInt<M>>,
}
impl<M: Modulation> Factorial<M> {
    pub fn factorial<T: num::ToPrimitive + num::Unsigned>(&self, n: T) -> ModInt<M> {
        self.pos[n.to_usize().unwrap()]
    }

    pub fn permutation<T: num::ToPrimitive + num::Unsigned>(&self, n: T, r: T) -> ModInt<M> {
        let n = n.to_usize().unwrap();
        let r = r.to_usize().unwrap();
        if r > n {
            ModInt::new(0)
        } else {
            self.pos[n] * self.neg[n - r]
        }
    }

    pub fn binomial<T: num::ToPrimitive + num::Unsigned>(&self, n: T, r: T) -> ModInt<M> {
        let n = n.to_usize().unwrap();
        let r = r.to_usize().unwrap();
        if r > n {
            ModInt::new(0)
        } else {
            self.pos[n] * self.neg[r] * self.neg[n - r]
        }
    }
    pub fn cmb_with_rep<T: num::ToPrimitive + num::Unsigned + Clone>(
        &self,
        n: T,
        r: T,
    ) -> ModInt<M> {
        self.binomial(n + r.clone() - T::one(), r)
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
        assert_eq!(Mint::new(3).pow(0u64).val(), 1);
        assert_eq!(Mint::new(3).pow(1u64).val(), 3);
        assert_eq!(Mint::new(3).pow(2u64).val(), 2);
        assert_eq!(Mint::new(3).pow(3u64).val(), 6);
        assert_eq!(Mint::new(3).pow(4u64).val(), 4);
        assert_eq!(Mint::new(3).pow(5u64).val(), 5);
        assert_eq!(Mint::new(3).pow(6u64).val(), 1);
        assert_eq!(Mint::new(3).pow(7u64).val(), 3);

        assert_eq!(Mint::new(3).pow(3u8).val(), 6);
        assert_eq!(Mint::new(3).pow(3u16).val(), 6);
        assert_eq!(Mint::new(3).pow(3u32).val(), 6);
        assert_eq!(Mint::new(3).pow(3u64).val(), 6);
        assert_eq!(Mint::new(3).pow(3usize).val(), 6);
        assert_eq!(Mint::new(3).powi(3i8).val(), 6);
        assert_eq!(Mint::new(3).powi(3i16).val(), 6);
        assert_eq!(Mint::new(3).powi(3i32).val(), 6);
        assert_eq!(Mint::new(3).powi(3i64).val(), 6);
        assert_eq!(Mint::new(3).powi(3isize).val(), 6);
        assert_eq!(Mint::new(3).powi(-2i8).val(), 4);
        assert_eq!(Mint::new(3).powi(-2i16).val(), 4);
        assert_eq!(Mint::new(3).powi(-2i32).val(), 4);
        assert_eq!(Mint::new(3).powi(-2i64).val(), 4);
        assert_eq!(Mint::new(3).powi(-2isize).val(), 4);
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
            Mint::gen_inv(6u64)
                .iter()
                .map(|x| x.val())
                .collect::<Vec<_>>(),
            &[1, 1, 4, 5, 2, 3, 6]
        );
        let _ = Mint::gen_inv(5u8);
        let _ = Mint::gen_inv(5u16);
        let _ = Mint::gen_inv(5u32);
        let _ = Mint::gen_inv(5u64);
        let _ = Mint::gen_inv(5usize);
    }

    #[test]
    fn test_modint_factorial() {
        let fac = Mint::gen_factorial(5u64);
        let pos = fac.pos.iter().map(|x| x.val()).collect::<Vec<_>>();
        let neg = fac.neg.iter().map(|x| x.val()).collect::<Vec<_>>();
        assert_eq!(pos, &[1, 1, 2, 6, 3, 1]);
        assert_eq!(neg, &[1, 1, 4, 6, 5, 1]);

        let _ = Mint::gen_factorial(5u8);
        let _ = Mint::gen_factorial(5u16);
        let _ = Mint::gen_factorial(5u32);
        let _ = Mint::gen_factorial(5u64);
        let _ = Mint::gen_factorial(5usize);
        let _ = fac.factorial(5u8);
        let _ = fac.factorial(5u16);
        let _ = fac.factorial(5u32);
        let _ = fac.factorial(5u64);
        let _ = fac.factorial(5usize);
        let _ = fac.permutation(5u8, 3u8);
        let _ = fac.permutation(5u16, 3u16);
        let _ = fac.permutation(5u32, 3u32);
        let _ = fac.permutation(5u64, 3u64);
        let _ = fac.permutation(5usize, 3usize);
        let _ = fac.binomial(5u8, 3u8);
        let _ = fac.binomial(5u16, 3u16);
        let _ = fac.binomial(5u32, 3u32);
        let _ = fac.binomial(5u64, 3u64);
        let _ = fac.binomial(5usize, 3usize);
        let _ = fac.cmb_with_rep(3u8, 1u8);
        let _ = fac.cmb_with_rep(3u16, 1u16);
        let _ = fac.cmb_with_rep(3u32, 1u32);
        let _ = fac.cmb_with_rep(3u64, 1u64);
        let _ = fac.cmb_with_rep(3usize, 1usize);
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
