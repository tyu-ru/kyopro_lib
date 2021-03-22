
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum InfType<T> {
    NegInfinity,
    Finit(T),
    Infinity,
}

impl<T> InfType<T> {
    pub fn finit_or(self, other: T) -> T {
        match self {
            InfType::Finit(x) => x,
            _ => other,
        }
    }
    pub fn is_finite(&self) -> bool {
        matches!(self, InfType::Finit(_))
    }
    pub fn is_infinite(&self) -> bool {
        !self.is_finite()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use InfType::*;
    type T = InfType<i32>;

    #[test]
    fn is_func() {
        assert!(Finit(12).is_finite());
        assert!(!Finit(12).is_infinite());
        assert!(!T::Infinity.is_finite());
        assert!(T::Infinity.is_infinite());
        assert!(!T::NegInfinity.is_finite());
        assert!(T::NegInfinity.is_infinite());
    }

    #[test]
    fn ord() {
        assert!(NegInfinity < Finit(12));
        assert!(Finit(12) < Infinity);
        assert!(T::NegInfinity < T::Infinity);
    }
}
