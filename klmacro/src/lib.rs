#[macro_export]
macro_rules! chmin {
    ($x:expr, $y: expr) => {
        $x = std::cmp::min($x, $y);
    };
}
#[macro_export]
macro_rules! chmax {
    ($x:expr, $y: expr) => {
        $x = std::cmp::max($x, $y);
    };
}
