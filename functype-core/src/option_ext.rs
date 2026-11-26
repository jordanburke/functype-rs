use crate::either::Either;
use crate::non_empty_vec::NonEmptyVec;
use crate::validated::Validated;

/// Conversions from `Option<T>` that std lacks.
///
/// Everything else maps to std; see the mapping doc. TS `getOrElse` → `unwrap_or_else`,
/// `orElse` → `or_else`, `fold` → `map_or_else`. The removed functype-rs methods map as:
/// `tap_some` → `inspect`, `contains_where` → `is_some_and`, `zip_with(&b, f)` →
/// `a.zip(b).map(|(a, b)| f(a, b))`, and `when(cond, f)` → `cond.then(f)`.
pub trait OptionExt<T> {
    /// Converts to `Either<L, T>`, using `left_value` for `None`.
    fn to_either<L, F: FnOnce() -> L>(self, left_value: F) -> Either<L, T>;

    /// Converts to `Validated<E, T>`, using `error` for `None`.
    fn to_validated<E, F: FnOnce() -> E>(self, error: F) -> Validated<E, T>;

    /// Converts `Some(value)` to a `NonEmptyVec` with a single element.
    fn to_non_empty_vec(self) -> Option<NonEmptyVec<T>>;

    /// Runs a side effect if `None`, and returns the option unchanged. std has `inspect` for
    /// the `Some` case only.
    fn tap_none<F: FnOnce()>(self, f: F) -> Self;
}

impl<T> OptionExt<T> for Option<T> {
    fn to_either<L, F: FnOnce() -> L>(self, left_value: F) -> Either<L, T> {
        match self {
            Some(v) => Either::Right(v),
            None => Either::Left(left_value()),
        }
    }

    fn to_validated<E, F: FnOnce() -> E>(self, error: F) -> Validated<E, T> {
        match self {
            Some(v) => Validated::Valid(v),
            None => Validated::invalid(error()),
        }
    }

    fn to_non_empty_vec(self) -> Option<NonEmptyVec<T>> {
        self.map(NonEmptyVec::new)
    }

    fn tap_none<F: FnOnce()>(self, f: F) -> Self {
        if self.is_none() {
            f();
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_either_some() {
        assert_eq!(Some(42).to_either(|| "missing"), Either::Right(42));
    }

    #[test]
    fn to_either_none() {
        let opt: Option<i32> = None;
        assert_eq!(opt.to_either(|| "missing"), Either::Left("missing"));
    }

    #[test]
    fn to_either_moves_without_clone() {
        struct NoClone(i32);
        let e: Either<&str, NoClone> = Some(NoClone(1)).to_either(|| "missing");
        assert!(matches!(e, Either::Right(NoClone(1))));
    }

    #[test]
    fn to_validated_some() {
        assert_eq!(Some(42).to_validated(|| "missing"), Validated::Valid(42));
    }

    #[test]
    fn to_validated_none() {
        let opt: Option<i32> = None;
        assert!(opt.to_validated(|| "missing").is_invalid());
    }

    #[test]
    fn to_non_empty_vec_some() {
        let nev = Some(42).to_non_empty_vec().unwrap();
        assert_eq!(*nev.head(), 42);
        assert_eq!(nev.len(), 1);
    }

    #[test]
    fn to_non_empty_vec_none() {
        let opt: Option<i32> = None;
        assert!(opt.to_non_empty_vec().is_none());
    }

    #[test]
    fn tap_none_runs_only_for_none() {
        let mut called = false;
        let opt: Option<i32> = None;
        assert_eq!(opt.tap_none(|| called = true), None);
        assert!(called);

        let mut called = false;
        assert_eq!(Some(1).tap_none(|| called = true), Some(1));
        assert!(!called);
    }
}
