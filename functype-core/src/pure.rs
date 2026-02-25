use crate::either::Either;
use crate::validated::Validated;

/// A trait for lifting a value into a monadic/applicative context.
///
/// Equivalent to Haskell's `pure` / `return` or Scala's `Some`, `Right`, etc.
///
/// # Examples
/// ```
/// use functype_core::pure::Pure;
///
/// let opt: Option<i32> = Pure::pure(42);
/// assert_eq!(opt, Some(42));
///
/// let res: Result<i32, String> = Pure::pure(42);
/// assert_eq!(res, Ok(42));
/// ```
pub trait Pure<A> {
    fn pure(a: A) -> Self;
}

impl<A> Pure<A> for Option<A> {
    fn pure(a: A) -> Self {
        Some(a)
    }
}

impl<A, E> Pure<A> for Result<A, E> {
    fn pure(a: A) -> Self {
        Ok(a)
    }
}

impl<L, A> Pure<A> for Either<L, A> {
    fn pure(a: A) -> Self {
        Either::Right(a)
    }
}

impl<E, A> Pure<A> for Validated<E, A> {
    fn pure(a: A) -> Self {
        Validated::Valid(a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_option() {
        let opt: Option<i32> = Pure::pure(42);
        assert_eq!(opt, Some(42));
    }

    #[test]
    fn pure_result() {
        let res: Result<i32, String> = Pure::pure(42);
        assert_eq!(res, Ok(42));
    }

    #[test]
    fn pure_either() {
        let e: Either<String, i32> = Pure::pure(42);
        assert_eq!(e, Either::Right(42));
    }

    #[test]
    fn pure_validated() {
        let v: Validated<String, i32> = Pure::pure(42);
        assert_eq!(v, Validated::Valid(42));
    }
}
