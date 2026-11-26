use crate::either::Either;
use crate::validated::Validated;

/// Conversions on `Result<T, E>` that std lacks.
///
/// Everything else maps to std; see the mapping doc. TS `getOrElse` → `unwrap_or_else`,
/// `fold` → `map_or_else`, `tap`/`tapLeft` → `inspect`/`inspect_err`, `recover` →
/// `or_else(|e| Ok(f(e)))`, `recoverWith` → `or_else`, and
/// `bimap(fl, fr)` → `.map_err(fl).map(fr)`.
pub trait ResultExt<T, E> {
    /// Converts to `Either<E, T>`.
    fn to_either(self) -> Either<E, T>;

    /// Converts to `Validated<E, T>`.
    fn to_validated(self) -> Validated<E, T>;

    /// Swaps `Ok` and `Err`. TS: `Either.swap`.
    fn swap(self) -> Result<E, T>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn to_either(self) -> Either<E, T> {
        Either::from_result(self)
    }

    fn to_validated(self) -> Validated<E, T> {
        Validated::from_result(self)
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
