use std::any::Any;
use std::fmt;
use std::panic::{catch_unwind, AssertUnwindSafe, UnwindSafe};

use crate::either::Either;

/// Error type representing a captured panic.
#[derive(Debug)]
pub struct TryError {
    message: String,
    payload: Option<Box<dyn Any + Send>>,
}

impl TryError {
    /// Creates a new `TryError` from a panic payload.
    pub fn from_panic(payload: Box<dyn Any + Send>) -> Self {
        let message = if let Some(s) = payload.downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "unknown panic".to_string()
        };
        TryError {
            message,
            payload: Some(payload),
        }
    }

    /// Returns the panic message.
    pub fn message(&self) -> &str {
        &self.message
    }

    /// Takes the raw panic payload, if still available.
    pub fn take_payload(&mut self) -> Option<Box<dyn Any + Send>> {
        self.payload.take()
    }
}

impl fmt::Display for TryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Panicked: {}", self.message)
    }
}

impl std::error::Error for TryError {}

/// A type alias for `Result<T, TryError>`, representing a computation that may panic.
pub type Try<T> = Result<T, TryError>;

/// Captures a closure, converting any panics into `TryError`.
///
/// The closure must be `UnwindSafe`. For closures that are not, use `try_catch_unchecked`.
///
/// # Examples
/// ```
/// use functype_core::try_type::try_catch;
///
/// let result = try_catch(|| 42);
/// assert_eq!(result.unwrap(), 42);
///
/// let result = try_catch(|| panic!("oops"));
/// assert!(result.is_err());
/// ```
pub fn try_catch<T>(f: impl FnOnce() -> T + UnwindSafe) -> Try<T> {
    catch_unwind(f).map_err(TryError::from_panic)
}

/// Captures a closure, converting any panics into `TryError`.
///
/// This wraps the closure in `AssertUnwindSafe`, which is useful for closures
/// that capture mutable references or other non-UnwindSafe types.
///
/// # Examples
/// ```
/// use functype_core::try_type::try_catch_unchecked;
///
/// let mut counter = 0;
/// let result = try_catch_unchecked(|| {
///     counter += 1;
///     counter
/// });
/// assert_eq!(result.unwrap(), 1);
/// ```
pub fn try_catch_unchecked<T>(f: impl FnOnce() -> T) -> Try<T> {
    catch_unwind(AssertUnwindSafe(f)).map_err(TryError::from_panic)
}

/// Extension trait for `Try<T>` providing functional combinators.
///
/// Method names are chosen to avoid conflicts with `Result`'s built-in methods.
pub trait TryExt<T> {
    /// Returns `true` if the computation succeeded.
    fn is_success(&self) -> bool;

    /// Returns `true` if the computation failed (panicked).
    fn is_failure(&self) -> bool;

    /// Converts to `Either<TryError, T>`.
    fn to_either(self) -> Either<TryError, T>;

    /// Recovers from a failure by applying a function to the error.
    fn recover<F: FnOnce(&TryError) -> T>(self, f: F) -> T;

    /// Recovers from a failure by applying a function that returns a `Try<T>`.
    fn recover_with<F: FnOnce(&TryError) -> Try<T>>(self, f: F) -> Try<T>;

    /// Folds the `Try` into a single value.
    fn try_fold<U, FE: FnOnce(&TryError) -> U, FS: FnOnce(T) -> U>(self, on_failure: FE, on_success: FS) -> U;

    /// Returns the success value, or computes a default from the error.
    fn get_or_else<F: FnOnce(&TryError) -> T>(self, f: F) -> T;
}

impl<T> TryExt<T> for Try<T> {
    fn is_success(&self) -> bool {
        self.is_ok()
    }

    fn is_failure(&self) -> bool {
        self.is_err()
    }

    fn to_either(self) -> Either<TryError, T> {
        Either::from_result(self)
    }

    fn recover<F: FnOnce(&TryError) -> T>(self, f: F) -> T {
        match self {
            Ok(v) => v,
            Err(ref e) => f(e),
        }
    }

    fn recover_with<F: FnOnce(&TryError) -> Try<T>>(self, f: F) -> Try<T> {
        match self {
            Ok(v) => Ok(v),
            Err(ref e) => f(e),
        }
    }

    fn try_fold<U, FE: FnOnce(&TryError) -> U, FS: FnOnce(T) -> U>(self, on_failure: FE, on_success: FS) -> U {
        match self {
            Ok(v) => on_success(v),
            Err(ref e) => on_failure(e),
        }
    }

    fn get_or_else<F: FnOnce(&TryError) -> T>(self, f: F) -> T {
        match self {
            Ok(v) => v,
            Err(ref e) => f(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_catch_success() {
        let result = try_catch(|| 42);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn try_catch_captures_str_panic() {
        let result = try_catch(|| -> i32 { panic!("something went wrong") });
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.message(), "something went wrong");
    }

    #[test]
    fn try_catch_captures_string_panic() {
        let result = try_catch(|| -> i32 { panic!("{}", "formatted panic".to_string()) });
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.message(), "formatted panic");
    }

    #[test]
    fn try_catch_captures_unknown_panic() {
        let result = try_catch(|| -> i32 {
            std::panic::panic_any(42i32);
        });
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.message(), "unknown panic");
    }

    #[test]
    fn try_catch_unchecked_with_mutable_state() {
        let mut counter = 0;
        let result = try_catch_unchecked(|| {
            counter += 1;
            counter
        });
        assert_eq!(result.unwrap(), 1);
    }

    #[test]
    fn try_catch_unchecked_captures_panic() {
        let result = try_catch_unchecked(|| -> i32 { panic!("unchecked panic") });
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().message(), "unchecked panic");
    }

    #[test]
    fn is_success_and_failure() {
        let success: Try<i32> = try_catch(|| 42);
        assert!(success.is_success());
        assert!(!success.is_failure());

        let failure: Try<i32> = try_catch(|| panic!("fail"));
        assert!(!failure.is_success());
        assert!(failure.is_failure());
    }

    #[test]
    fn to_either_converts() {
        let success: Try<i32> = try_catch(|| 42);
        let either = success.to_either();
        assert!(either.is_right());
        assert_eq!(either.right_value(), Some(&42));

        let failure: Try<i32> = try_catch(|| panic!("fail"));
        let either = failure.to_either();
        assert!(either.is_left());
    }

    #[test]
    fn recover_from_failure() {
        let failure: Try<i32> = try_catch(|| panic!("fail"));
        let recovered = failure.recover(|_| 0);
        assert_eq!(recovered, 0);
    }

    #[test]
    fn recover_passes_through_success() {
        let success: Try<i32> = try_catch(|| 42);
        let result = success.recover(|_| 0);
        assert_eq!(result, 42);
    }

    #[test]
    fn recover_with_chains() {
        let failure: Try<i32> = try_catch(|| panic!("fail"));
        let recovered = failure.recover_with(|_| Ok(99));
        assert_eq!(recovered.unwrap(), 99);
    }

    #[test]
    fn recover_with_can_fail_again() {
        let failure: Try<i32> = try_catch(|| panic!("first"));
        let still_failed = failure.recover_with(|e| {
            Err(TryError {
                message: format!("recovered from: {}", e.message()),
                payload: None,
            })
        });
        assert!(still_failed.is_err());
        assert_eq!(still_failed.unwrap_err().message(), "recovered from: first");
    }

    #[test]
    fn try_fold_on_success() {
        let success: Try<i32> = try_catch(|| 42);
        let result = success.try_fold(|e| format!("err: {}", e.message()), |v| format!("ok: {}", v));
        assert_eq!(result, "ok: 42");
    }

    #[test]
    fn try_fold_on_failure() {
        let failure: Try<i32> = try_catch(|| panic!("boom"));
        let result = failure.try_fold(|e| format!("err: {}", e.message()), |v| format!("ok: {}", v));
        assert_eq!(result, "err: boom");
    }

    #[test]
    fn get_or_else_returns_success() {
        let success: Try<i32> = try_catch(|| 42);
        assert_eq!(success.get_or_else(|_| 0), 42);
    }

    #[test]
    fn get_or_else_computes_from_error() {
        let failure: Try<i32> = try_catch(|| panic!("fail"));
        assert_eq!(failure.get_or_else(|_| -1), -1);
    }

    #[test]
    fn display_formatting() {
        let err = TryError {
            message: "test error".to_string(),
            payload: None,
        };
        assert_eq!(format!("{}", err), "Panicked: test error");
    }

    #[test]
    fn take_payload() {
        let result: Try<i32> = try_catch(|| panic!("payload test"));
        let mut err = result.unwrap_err();
        let payload = err.take_payload();
        assert!(payload.is_some());
        assert!(err.take_payload().is_none());
    }
}
