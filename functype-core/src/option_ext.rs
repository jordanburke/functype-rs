use crate::either::Either;
use crate::non_empty_vec::NonEmptyVec;
use crate::validated::Validated;

/// Extension trait adding functional combinators to `Option<T>`.
pub trait OptionExt<T> {
    /// Returns the contained value or computes it from a closure.
    fn get_or_else<F: FnOnce() -> T>(&self, f: F) -> T
    where
        T: Clone;

    /// Returns the option if it contains a value, otherwise calls `f`.
    fn or_else_lazy<F: FnOnce() -> Option<T>>(&self, f: F) -> Option<T>
    where
        T: Clone;

    /// Folds the option into a single value.
    fn fold<U, FN: FnOnce() -> U, FS: FnOnce(&T) -> U>(&self, on_none: FN, on_some: FS) -> U;

    /// Converts to `Either<L, T>`, using `left_value` for `None`.
    fn to_either<L, F: FnOnce() -> L>(&self, left_value: F) -> Either<L, T>
    where
        T: Clone;

    /// Converts to `Validated<E, T>`, using `error` for `None`.
    fn to_validated<E, F: FnOnce() -> E>(&self, error: F) -> Validated<E, T>
    where
        T: Clone;

    /// Converts `Some(value)` to a `NonEmptyVec` with a single element.
    fn to_non_empty_vec(&self) -> Option<NonEmptyVec<T>>
    where
        T: Clone;

    /// Applies a side-effect if `Some`.
    fn tap_some<F: FnOnce(&T)>(&self, f: F) -> &Self;

    /// Applies a side-effect if `None`.
    fn tap_none<F: FnOnce()>(&self, f: F) -> &Self;

    /// Returns `true` if `Some` and the value satisfies the predicate.
    fn contains_where<F: FnOnce(&T) -> bool>(&self, f: F) -> bool;

    /// Zips two options with a combining function.
    fn zip_with<U, V, F: FnOnce(&T, &U) -> V>(&self, other: &Option<U>, f: F) -> Option<V>;
}

impl<T> OptionExt<T> for Option<T> {
    fn get_or_else<F: FnOnce() -> T>(&self, f: F) -> T
    where
        T: Clone,
    {
        match self {
            Some(v) => v.clone(),
            None => f(),
        }
    }

    fn or_else_lazy<F: FnOnce() -> Option<T>>(&self, f: F) -> Option<T>
    where
        T: Clone,
    {
        match self {
            Some(v) => Some(v.clone()),
            None => f(),
        }
    }

    fn fold<U, FN: FnOnce() -> U, FS: FnOnce(&T) -> U>(&self, on_none: FN, on_some: FS) -> U {
        match self {
            Some(v) => on_some(v),
            None => on_none(),
        }
    }

    fn to_either<L, F: FnOnce() -> L>(&self, left_value: F) -> Either<L, T>
    where
        T: Clone,
    {
        match self {
            Some(v) => Either::Right(v.clone()),
            None => Either::Left(left_value()),
        }
    }

    fn to_validated<E, F: FnOnce() -> E>(&self, error: F) -> Validated<E, T>
    where
        T: Clone,
    {
        match self {
            Some(v) => Validated::Valid(v.clone()),
            None => Validated::invalid(error()),
        }
    }

    fn to_non_empty_vec(&self) -> Option<NonEmptyVec<T>>
    where
        T: Clone,
    {
        self.as_ref().map(|v| NonEmptyVec::new(v.clone()))
    }

    fn tap_some<F: FnOnce(&T)>(&self, f: F) -> &Self {
        if let Some(v) = self {
            f(v);
        }
        self
    }

    fn tap_none<F: FnOnce()>(&self, f: F) -> &Self {
        if self.is_none() {
            f();
        }
        self
    }

    fn contains_where<F: FnOnce(&T) -> bool>(&self, f: F) -> bool {
        match self {
            Some(v) => f(v),
            None => false,
        }
    }

    fn zip_with<U, V, F: FnOnce(&T, &U) -> V>(&self, other: &Option<U>, f: F) -> Option<V> {
        match (self, other) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }
}

/// Creates an `Option<T>` based on a condition.
pub fn when<T>(condition: bool, value: impl FnOnce() -> T) -> Option<T> {
    if condition {
        Some(value())
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_or_else_some() {
        let opt = Some(42);
        assert_eq!(opt.get_or_else(|| 0), 42);
    }

    #[test]
    fn get_or_else_none() {
        let opt: Option<i32> = None;
        assert_eq!(opt.get_or_else(|| 0), 0);
    }

    #[test]
    fn or_else_lazy_some() {
        let opt = Some(42);
        assert_eq!(opt.or_else_lazy(|| Some(0)), Some(42));
    }

    #[test]
    fn or_else_lazy_none() {
        let opt: Option<i32> = None;
        assert_eq!(opt.or_else_lazy(|| Some(99)), Some(99));
    }

    #[test]
    fn fold_some() {
        let opt = Some(42);
        assert_eq!(opt.fold(|| "none".to_string(), |v| format!("some: {}", v)), "some: 42");
    }

    #[test]
    fn fold_none() {
        let opt: Option<i32> = None;
        assert_eq!(opt.fold(|| "none".to_string(), |v| format!("some: {}", v)), "none");
    }

    #[test]
    fn to_either_some() {
        let opt = Some(42);
        assert_eq!(opt.to_either(|| "missing"), Either::Right(42));
    }

    #[test]
    fn to_either_none() {
        let opt: Option<i32> = None;
        assert_eq!(opt.to_either(|| "missing"), Either::Left("missing"));
    }

    #[test]
    fn to_validated_some() {
        let opt = Some(42);
        assert_eq!(opt.to_validated(|| "missing"), Validated::Valid(42));
    }

    #[test]
    fn to_validated_none() {
        let opt: Option<i32> = None;
        let v = opt.to_validated(|| "missing");
        assert!(v.is_invalid());
    }

    #[test]
    fn to_non_empty_vec_some() {
        let opt = Some(42);
        let nev = opt.to_non_empty_vec().unwrap();
        assert_eq!(*nev.head(), 42);
        assert_eq!(nev.len(), 1);
    }

    #[test]
    fn to_non_empty_vec_none() {
        let opt: Option<i32> = None;
        assert!(opt.to_non_empty_vec().is_none());
    }

    #[test]
    fn tap_some_runs_side_effect() {
        let opt = Some(42);
        let mut seen = 0;
        opt.tap_some(|v| seen = *v);
        assert_eq!(seen, 42);
    }

    #[test]
    fn tap_none_runs_side_effect() {
        let opt: Option<i32> = None;
        let mut called = false;
        opt.tap_none(|| called = true);
        assert!(called);
    }

    #[test]
    fn contains_where_true() {
        let opt = Some(42);
        assert!(opt.contains_where(|v| *v > 0));
    }

    #[test]
    fn contains_where_false() {
        let opt = Some(-1);
        assert!(!opt.contains_where(|v| *v > 0));
    }

    #[test]
    fn contains_where_none() {
        let opt: Option<i32> = None;
        assert!(!opt.contains_where(|_| true));
    }

    #[test]
    fn zip_with_both_some() {
        let a = Some(2);
        let b = Some(3);
        assert_eq!(a.zip_with(&b, |x, y| x * y), Some(6));
    }

    #[test]
    fn zip_with_one_none() {
        let a = Some(2);
        let b: Option<i32> = None;
        assert_eq!(a.zip_with(&b, |x, y| x * y), None);
    }

    #[test]
    fn when_true() {
        assert_eq!(when(true, || 42), Some(42));
    }

    #[test]
    fn when_false() {
        assert_eq!(when(false, || 42), None);
    }
}
