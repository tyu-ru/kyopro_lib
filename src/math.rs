/// calcurate (0..n).map(|i|(a*i+b)/m).sum()
pub fn floor_sum(n: i64, m: i64, mut a: i64, mut b: i64) -> i64 {
    let mut res = 0;
    res += b / m * n;
    b %= m;
    res += a / m * n * (n - 1) / 2;
    a %= m;

    let y_max = (n * a + b) / m;
    if y_max == 0 {
        return res;
    }
    let x_max = y_max * m - b;
    res + (n - (x_max + a - 1) / a) * y_max + floor_sum(y_max, a, m, (a - x_max % a) % a)
}

/// a^x mod m
pub fn pow_mod(mut a: u64, mut x: u64, m: u64) -> u64 {
    let mut res = 1;
    a %= m;
    while x != 0 {
        if x & 1 == 1 {
            res = res * a % m;
        }
        a = a * a % m;
        x >>= 1;
    }
    res
}

#[test]
fn test_pow_mod() {
    assert_eq!(pow_mod(2, 0, 100), 1);
    assert_eq!(pow_mod(2, 5, 100), 32);
    assert_eq!(pow_mod(2, 5, 10), 2);
    assert_eq!(pow_mod(10u64.pow(15), 100, 10), 0);
}

pub fn euler_totient(mut x: u64) -> u64 {
    let mut res = 1;
    for p in 2.. {
        if x < p * p {
            break;
        }
        let mut y = 1;
        while x % p == 0 {
            y *= p;
            x /= p;
        }
        res *= y - y / p;
    }
    if x != 1 {
        res *= x - 1;
    }
    res
}

pub fn euler_totient_from_factorized(f: &[(u64, usize)]) -> u64 {
    let mut res = 1;
    for &(p, e) in f {
        let x = p.pow(e as u32 - 1);
        res *= x * p - x;
    }
    res
}

#[test]
fn test_euler_totient() {
    itertools::assert_equal(
        (1..=20).map(|x| euler_totient(x)),
        vec![
            1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8,
        ],
    );

    assert_eq!(
        euler_totient_from_factorized(&[(2, 3), (3, 1), (7, 4), (11149, 1)]),
        183540672
    );
}

pub fn inv_mod(x: u64, m: u64) -> Option<u64> {
    if x == 0 || num::integer::gcd(x, m) != 1 {
        return None;
    }
    let t = euler_totient(m);
    Some(pow_mod(x, t - 1, m))
}

#[test]
fn test_inv_mod() {
    assert_eq!(inv_mod(0, 5), None);
    assert_eq!(inv_mod(1, 5), Some(1));
    assert_eq!(inv_mod(2, 5), Some(3));
    assert_eq!(inv_mod(3, 5), Some(2));
    assert_eq!(inv_mod(4, 5), Some(4));
    assert_eq!(inv_mod(6, 5), Some(1));

    assert_eq!(inv_mod(1, 6), Some(1));
    assert_eq!(inv_mod(2, 6), None);
    assert_eq!(inv_mod(3, 6), None);
    assert_eq!(inv_mod(4, 6), None);
    assert_eq!(inv_mod(5, 6), Some(5));
    assert_eq!(inv_mod(7, 6), Some(1));

    assert_eq!(inv_mod(21, 100), Some(81));
}

/// The smallest x,y pair satisfying `ax + by = gcd(a,b)` and gcd
/// ```
/// # use kyopro_lib::math::ext_gcd;
/// assert_eq!(ext_gcd(4,6), (-1,1,2));
/// ```
pub fn ext_gcd(a: u64, b: u64) -> (i64, i64, u64) {
    if b == 0 {
        (1, 0, a)
    } else {
        let (mut y, x, d) = ext_gcd(b, a % b);
        y -= (a / b) as i64 * x;
        (x, y, d)
    }
}

#[cfg(test)]
#[test]
fn test_ext_gcd() {
    assert_eq!(ext_gcd(2, 3), (-1, 1, 1));
    assert_eq!(ext_gcd(4, 6), (-1, 1, 2));
    assert_eq!(ext_gcd(6, 4), (1, -1, 2));
}
