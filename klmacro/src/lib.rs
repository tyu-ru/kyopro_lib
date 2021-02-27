#[macro_export]
macro_rules! chmin {
    ($x:expr, $y: expr) => {
        if $y < $x {
            $x = $y;
            true
        } else {
            false
        }
    };
    ($x:expr, $($y:expr),+) => {
        $(chmin!($x, $y)) || *
    };
}

#[macro_export]
macro_rules! chmax {
    ($x:expr, $y: expr) => {
        if $y > $x {
            $x = $y;
            true
        } else {
            false
        }
    };
    ($x:expr, $($y:expr),+) => {
        $(chmax!($x, $y)) || *
    };
}

#[cfg(test)]
#[test]
fn test() {
    let mut x = 2;
    assert_eq!(chmin!(x, 4), false);
    assert_eq!(x, 2);
    assert_eq!(chmin!(x, 1), true);
    assert_eq!(x, 1);
    assert_eq!(chmin!(x, 1), false);
    assert_eq!(x, 1);

    let mut y = 4;
    assert_eq!(chmax!(y, 4, 1, 2, 3), false);
    assert_eq!(y, 4);
    assert_eq!(chmax!(y, 4, 1, 6, 5, 2, 3), true);
    assert_eq!(y, 6);
}
