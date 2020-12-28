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
