use crate::either::Either;
use crate::validated::Validated;

/// Extension trait adding functional combinators to `Result<T, E>`.
pub trait ResultExt<T, E> {
    /// Returns the ok value or computes it from the error.
    fn get_or_else<F: FnOnce(&E) -> T>(&self, f: F) -> T
    where
        T: Clone;

    /// Folds the result into a single value.
    fn fold<U, FE: FnOnce(&E) -> U, FT: FnOnce(&T) -> U>(&self, on_err: FE, on_ok: FT) -> U;

    /// Converts to `Either<E, T>`.
    fn to_either(self) -> Either<E, T>;

    /// Converts to `Validated<E, T>`.
    fn to_validated(self) -> Validated<E, T>;

    /// Applies a side-effect if `Ok`.
    fn tap_ok<F: FnOnce(&T)>(&self, f: F) -> &Self;

    /// Applies a side-effect if `Err`.
    fn tap_err<F: FnOnce(&E)>(&self, f: F) -> &Self;

    /// Maps over both sides simultaneously.
    fn bimap<A, B, FE: FnOnce(&E) -> B, FT: FnOnce(&T) -> A>(&self, on_ok: FT, on_err: FE) -> Result<A, B>;

    /// Recovers from an error by applying a function.
    fn recover<F: FnOnce(&E) -> T>(&self, f: F) -> T
    where
        T: Clone;

    /// Recovers from an error by applying a function that returns a `Result`.
    fn recover_with<F: FnOnce(&E) -> Result<T, E>>(&self, f: F) -> Result<T, E>
    where
        T: Clone,
        E: Clone;

    /// Swaps `Ok` and `Err`.
    fn swap(self) -> Result<E, T>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn get_or_else<F: FnOnce(&E) -> T>(&self, f: F) -> T
    where
        T: Clone,
    {
        match self {
            Ok(v) => v.clone(),
            Err(e) => f(e),
        }
    }

    fn fold<U, FE: FnOnce(&E) -> U, FT: FnOnce(&T) -> U>(&self, on_err: FE, on_ok: FT) -> U {
        match self {
            Ok(v) => on_ok(v),
            Err(e) => on_err(e),
        }
    }

    fn to_either(self) -> Either<E, T> {
        Either::from_result(self)
    }

    fn to_validated(self) -> Validated<E, T> {
        Validated::from_result(self)
    }

    fn tap_ok<F: FnOnce(&T)>(&self, f: F) -> &Self {
        if let Ok(v) = self {
            f(v);
        }
        self
    }

    fn tap_err<F: FnOnce(&E)>(&self, f: F) -> &Self {
        if let Err(e) = self {
            f(e);
        }
        self
    }

    fn bimap<A, B, FE: FnOnce(&E) -> B, FT: FnOnce(&T) -> A>(&self, on_ok: FT, on_err: FE) -> Result<A, B> {
        match self {
            Ok(v) => Ok(on_ok(v)),
            Err(e) => Err(on_err(e)),
        }
    }

    fn recover<F: FnOnce(&E) -> T>(&self, f: F) -> T
    where
        T: Clone,
    {
        match self {
            Ok(v) => v.clone(),
            Err(e) => f(e),
        }
    }

    fn recover_with<F: FnOnce(&E) -> Result<T, E>>(&self, f: F) -> Result<T, E>
    where
        T: Clone,
        E: Clone,
    {
        match self {
            Ok(v) => Ok(v.clone()),
            Err(e) => f(e),
        }
    }

    fn swap(self) -> Result<E, T> {
        match self {
            Ok(v) => Err(v),
            Err(e) => Ok(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_or_else_ok() {
        let r: Result<i32, &str> = Ok(42);
        assert_eq!(r.get_or_else(|_| 0), 42);
    }

    #[test]
    fn get_or_else_err() {
        let r: Result<i32, &str> = Err("fail");
        assert_eq!(r.get_or_else(|_| 0), 0);
    }

    #[test]
    fn fold_ok() {
        let r: Result<i32, &str> = Ok(42);
        assert_eq!(r.fold(|e| format!("err: {}", e), |v| format!("ok: {}", v)), "ok: 42");
    }

    #[test]
    fn fold_err() {
        let r: Result<i32, &str> = Err("fail");
        assert_eq!(r.fold(|e| format!("err: {}", e), |v| format!("ok: {}", v)), "err: fail");
    }

    #[test]
    fn to_either_ok() {
        let r: Result<i32, &str> = Ok(42);
        assert_eq!(r.to_either(), Either::Right(42));
    }

    #[test]
    fn to_either_err() {
        let r: Result<i32, &str> = Err("fail");
        assert_eq!(r.to_either(), Either::Left("fail"));
    }

    #[test]
    fn to_validated_ok() {
        let r: Result<i32, String> = Ok(42);
        assert_eq!(r.to_validated(), Validated::Valid(42));
    }

    #[test]
    fn to_validated_err() {
        let r: Result<i32, String> = Err("fail".to_string());
        assert!(r.to_validated().is_invalid());
    }

    #[test]
    fn tap_ok_side_effect() {
        let r: Result<i32, &str> = Ok(42);
        let mut seen = 0;
        r.tap_ok(|v| seen = *v);
        assert_eq!(seen, 42);
    }

    #[test]
    fn tap_err_side_effect() {
        let r: Result<i32, &str> = Err("fail");
        let mut seen = "";
        r.tap_err(|e| seen = e);
        assert_eq!(seen, "fail");
    }

    #[test]
    fn bimap_ok() {
        let r: Result<i32, &str> = Ok(42);
        let mapped = r.bimap(|v| v.to_string(), |e| e.len());
        assert_eq!(mapped, Ok("42".to_string()));
    }

    #[test]
    fn bimap_err() {
        let r: Result<i32, &str> = Err("fail");
        let mapped = r.bimap(|v| v.to_string(), |e| e.len());
        assert_eq!(mapped, Err(4));
    }

    #[test]
    fn recover_ok() {
        let r: Result<i32, &str> = Ok(42);
        assert_eq!(r.recover(|_| 0), 42);
    }

    #[test]
    fn recover_err() {
        let r: Result<i32, &str> = Err("fail");
        assert_eq!(r.recover(|_| 99), 99);
    }

    #[test]
    fn recover_with_ok() {
        let r: Result<i32, &str> = Ok(42);
        assert_eq!(r.recover_with(|_| Ok(0)), Ok(42));
    }

    #[test]
    fn recover_with_err_success() {
        let r: Result<i32, &str> = Err("fail");
        assert_eq!(r.recover_with(|_| Ok(99)), Ok(99));
    }

    #[test]
    fn recover_with_err_failure() {
        let r: Result<i32, &str> = Err("fail");
        assert_eq!(r.recover_with(|_| Err("still fail")), Err("still fail"));
    }

    #[test]
    fn swap_ok() {
        let r: Result<i32, &str> = Ok(42);
        assert_eq!(r.swap(), Err(42));
    }

    #[test]
    fn swap_err() {
        let r: Result<i32, &str> = Err("fail");
        assert_eq!(r.swap(), Ok("fail"));
    }
}
