use klrle::RLE;

pub struct Sieve {
    v: Vec<u64>,
    p: Vec<u64>,
}

impl Sieve {
    pub fn new(n: u64) -> Self {
        let mut s = Self {
            v: vec![0; ((n + 1) / 2) as usize],
            p: Vec::new(),
        };

        s.v[0] = 1;
        s.p.push(2);

        for i in 1..s.v.len() {
            if s.v[i] != 0 {
                continue;
            }
            let p = 2 * i + 1;
            s.v[i] = p as u64;
            let mut j = p * p;
            while (j / 2) < s.v.len() {
                if s.v[j / 2] == 0 {
                    s.v[j / 2] = p as u64;
                }
                j += p * 2;
            }
            s.p.push(p as u64);
        }
        s
    }

    pub fn is_prime(&self, x: u64) -> bool {
        if x & 1 == 0 {
            x == 2
        } else {
            x != 1 && self.v[(x / 2) as usize] == x
        }
    }

    pub fn factorization(&self, mut x: u64) -> RLE<u64> {
        if x == 0 {
            panic!("0 is not natural number!");
        }
        if x == 1 {
            return RLE::new();
        }
        let mut res = RLE::new();
        let y = x.trailing_zeros() as usize;
        x >>= y;
        if y != 0 {
            res.push_n(2, y);
        }
        if x == 1 {
            return res;
        }
        while x != 1 {
            let p = self.v[(x / 2) as usize];
            res.push(p);
            x /= p;
        }
        res
    }
    pub fn primes(&self) -> &Vec<u64> {
        &self.p
    }
}

#[cfg(test)]
mod test {
    use super::Sieve;
    pub fn test_primes(s: &Sieve) {
        assert_eq!(s.is_prime(2), true);
        assert_eq!(s.is_prime(3), true);
        assert_eq!(s.is_prime(5), true);
        assert_eq!(s.is_prime(7), true);
        assert_eq!(s.is_prime(11), true);
        assert_eq!(s.is_prime(13), true);

        assert_eq!(s.is_prime(1), false);
        assert_eq!(s.is_prime(4), false);
        assert_eq!(s.is_prime(6), false);
        assert_eq!(s.is_prime(8), false);
        assert_eq!(s.is_prime(9), false);
        assert_eq!(s.is_prime(10), false);
        assert_eq!(s.is_prime(12), false);
        assert_eq!(s.is_prime(14), false);
        assert_eq!(s.is_prime(15), false);
        assert_eq!(s.is_prime(16), false);
    }
    #[test]
    fn test_sieve() {
        assert_eq!(Sieve::new(16).v, &[1, 3, 5, 7, 3, 11, 13, 3]);
        assert_eq!(Sieve::new(17).v, &[1, 3, 5, 7, 3, 11, 13, 3, 17]);
        assert_eq!(Sieve::new(17).p, &[2, 3, 5, 7, 11, 13, 17]);

        test_primes(&Sieve::new(16));
        test_primes(&Sieve::new(17));

        let s = Sieve::new(140);
        assert_eq!(s.factorization(1).v(), &[]);
        assert_eq!(s.factorization(127).v(), &[(127, 1)]);
        assert_eq!(s.factorization(140).v(), &[(2, 2), (5, 1), (7, 1)]);
    }
    #[test]
    #[should_panic(expected = "0 is not natural number!")]
    fn test_factorization_panic() {
        Sieve::new(10).factorization(0);
    }
}
