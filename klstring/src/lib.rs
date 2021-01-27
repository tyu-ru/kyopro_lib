pub fn z_algorithm<T: PartialEq>(s: &[T]) -> Vec<usize> {
    let mut res = vec![0; s.len()];
    res[0] = s.len();
    let mut i = 1;
    let mut j = 0;
    while i < s.len() {
        while i + j < s.len() && s[j] == s[i + j] {
            j += 1;
        }
        res[i] = j;
        if j == 0 {
            i += 1;
            continue;
        }

        let mut k = 1;
        while k < j && k + res[k] < j {
            res[i + k] = res[k];
            k += 1;
        }
        i += k;
        j -= k;
    }
    res
}

#[cfg(test)]
#[test]
fn test_z_algorithm() {
    assert_eq!(
        z_algorithm("momomosumomomosu".as_bytes()),
        [16, 0, 4, 0, 2, 0, 0, 0, 8, 0, 4, 0, 2, 0, 0, 0]
    );
}



pub struct MP<'a, T> {
    s: &'a [T],
    b: Vec<isize>,
}

impl<'a, T> MP<'a, T>
where
    T: Eq,
{
    pub fn new(s: &'a [T]) -> Self {
        let n = s.len();
        let mut t = vec![0; n + 1];
        t[0] = -1;
        let mut j = -1;
        for i in 0..n {
            while j != -1 && s[i] != s[j as usize] {
                j = t[j as usize];
            }
            j += 1;
            t[i + 1] = j;
        }
        MP { s: s, b: t }
    }

   pub fn find(&self, s: &[T]) -> Vec<usize> {
        let mut res = vec![];
        let mut j = 0;
        for i in 0..s.len() {
            while j != -1 && self.s[j as usize] != s[i] {
                j = self.b[j as usize];
            }
            j += 1;
            if j as usize == self.s.len() {
                res.push(i + 1 - j as usize);
                j = self.b[j as usize];
            }
        }
        res
    }
}
