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
