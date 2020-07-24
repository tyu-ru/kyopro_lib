pub mod bit;
pub mod grid;
pub mod misc;
pub mod modint;
pub mod rle;
pub mod segtree;
pub mod sieve;
pub mod string;
pub mod tree;
pub mod unionfind;

#[macro_use]
#[allow(unused_macros)]
macro_rules! dp {
    ($to:expr, $op:tt, $from:expr) => {
        let x = $from;
        $to $op x;
    };
}
