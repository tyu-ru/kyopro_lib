pub trait Modulation {
    const MOD: u64 = 1_000_000_007;
}

#[derive(PartialEq)]
pub struct ModInt<M: Modulation> {
    x: u64,
    phantom: std::marker::PhantomData<M>,
}

impl<M: Modulation> Clone for ModInt<M> {
    fn clone(&self) -> Self {
        Self::new_uncheck(self.x)
    }
}
impl<M: Modulation> Copy for ModInt<M> {}

impl<M: Modulation> ModInt<M> {
    #[inline]
    pub fn new(x: u64) -> Self {
        Self {
            x: x % M::MOD,
            phantom: std::marker::PhantomData,
        }
    }
    #[inline]
    pub fn new_uncheck(x: u64) -> Self {
        Self {
            x: x,
            phantom: std::marker::PhantomData,
        }
    }
    #[inline]
    pub fn val(&self) -> u64 {
        self.x
    }
}

impl<M: Modulation> std::ops::AddAssign for ModInt<M> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.x += rhs.x;
        if M::MOD <= self.x {
            self.x -= M::MOD;
        }
    }
}
impl<M: Modulation> std::ops::Add for ModInt<M> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let mut res = self;
        res += rhs;
        res
    }
}
impl<M: Modulation> std::ops::SubAssign for ModInt<M> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        if self.x >= rhs.x {
            self.x -= rhs.x;
        } else {
            self.x += M::MOD - rhs.x;
        }
    }
}
impl<M: Modulation> std::ops::Sub for ModInt<M> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let mut res = self;
        res -= rhs;
        res
    }
}
impl<M: Modulation> std::ops::MulAssign for ModInt<M> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        self.x *= rhs.x;
        self.x %= M::MOD;
    }
}
impl<M: Modulation> std::ops::Mul for ModInt<M> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let mut res = self;
        res *= rhs;
        res
    }
}

/// ax + by = gcd(a,b) を満たす最小のx,yの組 + gcd
/// ```
/// // assert_eq!(ext_gcd(4,6),(-1,1,2));
/// ```
fn ext_gcd(a: u64, b: u64) -> (i64, i64, u64) {
    if b == 0 {
        (1, 0, a)
    } else {
        let (mut y, x, d) = ext_gcd(b, a % b);
        y -= (a / b) as i64 * x;
        (x, y, d)
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
        let (mut x, _, _) = ext_gcd(self.x, M::MOD);
        if x < 0 {
            x %= M::MOD as i64;
            x += M::MOD as i64;
        }
        Self::new(x as u64)
    }

    pub fn gen_factorial(n: u64) -> (Vec<Self>, Vec<Self>) {
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

        (pos, neg)
    }
    pub fn gen_inv(n: u64) -> Vec<Self> {
        let mut res = vec![Self::new_uncheck(1); (n + 1) as usize];
        for i in 2..=n {
            res[i as usize] = Self::new_uncheck(M::MOD - M::MOD / i) * res[(M::MOD % i) as usize];
        }
        res
    }
}

#[cfg(test)]
mod test {
    use crate::modint::*;

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
    fn test_ext_gcd() {
        assert_eq!(ext_gcd(2, 3), (-1, 1, 1));
        assert_eq!(ext_gcd(4, 6), (-1, 1, 2));
        assert_eq!(ext_gcd(6, 4), (1, -1, 2));
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
        let (pos, neg) = Mint::gen_factorial(5);
        let pos = pos.iter().map(|x| x.val()).collect::<Vec<_>>();
        let neg = neg.iter().map(|x| x.val()).collect::<Vec<_>>();
        assert_eq!(pos, &[1, 1, 2, 6, 3, 1]);
        assert_eq!(neg, &[1, 1, 4, 6, 5, 1]);
    }
}

pub struct F1_000_000_007;
impl Modulation for F1_000_000_007 {
    const MOD: u64 = 1_000_000_007;
}
pub type Mint1_000_000_007 = ModInt<F1_000_000_007>;

pub struct F998_244_353;
impl Modulation for F998_244_353 {
    const MOD: u64 = 998_244_353;
}
pub type Mint998_244_353 = ModInt<F998_244_353>;
