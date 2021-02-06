pub trait BoolThen {
    fn then_some1<T>(self, t: T) -> Option<T>;
    fn then1<T, F: FnOnce() -> T>(self, f: F) -> Option<T>;
}

impl BoolThen for bool {
    fn then_some1<T>(self, t: T) -> Option<T> {
        if self {
            Some(t)
        } else {
            None
        }
    }

    fn then1<T, F: FnOnce() -> T>(self, f: F) -> Option<T> {
        if self {
            Some(f())
        } else {
            None
        }
    }
}
