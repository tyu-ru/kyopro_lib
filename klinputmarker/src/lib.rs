use proconio::{input, source::Readable};
use std::marker::PhantomData;

pub struct DigitVec<T>(PhantomData<T>);

macro_rules! decl_digit_vec_readable {
    ($t:ty) => {
        impl Readable for DigitVec<$t> {
            type Output = Vec<$t>;
            fn read<R: std::io::BufRead, S: proconio::source::Source<R>>(
                source: &mut S,
            ) -> Self::Output {
                input! { from source, x: proconio::marker::Bytes }
                x.into_iter().map(|c| (c - b'0') as $t).collect()
            }
        }
    };
    ($($t:ty),*) => {
        $(decl_digit_vec_readable!($t);)*
    };
}

decl_digit_vec_readable!(u8, u16, u32, u64, usize);
decl_digit_vec_readable!(i8, i16, i32, i64, isize);

#[cfg(test)]
#[test]
fn test_digit_vec() {
    use proconio::source::auto::AutoSource;
    let source = AutoSource::from("123");
    input! { from source, x: DigitVec<usize> }
    assert_eq!(x, vec![1usize, 2, 3]);

    let source = AutoSource::from("123");
    input! { from source, x: DigitVec<u64> }
    assert_eq!(x, vec![1u64, 2, 3]);
}

macro_rules! decl_alphabets {
    ($t:ty, $zero:expr) => {
        impl Readable for $t {
            type Output = Vec<usize>;
            fn read<R: std::io::BufRead, S: proconio::source::Source<R>>(
                source: &mut S,
            ) -> Self::Output {
                input! { from source, x: proconio::marker::Bytes }
                x.into_iter().map(|c| (c - $zero) as usize).collect()
            }
        }
    };
}
pub struct UpperAlphabets;
pub struct LowerAlphabets;
decl_alphabets!(UpperAlphabets, b'A');
decl_alphabets!(LowerAlphabets, b'a');

pub struct Rational64FromDecimal;

impl Readable for Rational64FromDecimal {
    type Output = num::rational::Rational64;

    fn read<R: std::io::BufRead, S: proconio::source::Source<R>>(source: &mut S) -> Self::Output {
        input! { from source, x: String }
        let mut iter = x.splitn(2, '.');
        let mut x = Self::Output::new(iter.next().unwrap().parse().unwrap(), 1);
        if let Some(y) = iter.next() {
            x += Self::Output::new(y.parse().unwrap(), 10i64.pow(y.len() as u32));
        }
        x
    }
}

#[cfg(test)]
#[test]
fn test_ratio_from_decimal() {
    use num::rational::Rational64;
    use proconio::source::auto::AutoSource;
    let source = AutoSource::from("123");
    input! { from source, x: Rational64FromDecimal }
    assert_eq!(x, Rational64::new(123, 1));

    let source = AutoSource::from("1.25");
    input! { from source, x: Rational64FromDecimal }
    assert_eq!(x, Rational64::new(5, 4));
}
