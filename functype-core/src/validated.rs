use crate::either::Either;
use crate::non_empty_vec::NonEmptyVec;
use std::fmt;

/// An applicative validation type that accumulates errors.
///
/// Unlike `Either` which short-circuits on the first error, `Validated` collects
/// all errors using `NonEmptyVec<E>`, providing a type-level guarantee that
/// invalid values always have at least one error.
///
/// # Examples
/// ```
/// use functype_core::validated::Validated;
/// use functype_core::nev;
///
/// let valid: Validated<String, i32> = Validated::valid(42);
/// assert!(valid.is_valid());
///
/// let result = Validated::<String, i32>::valid(1).zip(&Validated::valid(2));
/// assert_eq!(result.map(|(a, b)| a + b), Validated::valid(3));
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Validated<E, A> {
    Valid(A),
    Invalid(NonEmptyVec<E>),
}

impl<E, A> Validated<E, A> {
    /// Creates a valid value.
    pub fn valid(value: A) -> Self {
        Validated::Valid(value)
    }

    /// Creates an invalid value with a single error.
    pub fn invalid(error: E) -> Self {
        Validated::Invalid(NonEmptyVec::new(error))
    }

    /// Creates an invalid value with multiple errors.
    pub fn invalid_many(errors: NonEmptyVec<E>) -> Self {
        Validated::Invalid(errors)
    }

    /// Creates a `Validated` from a `Result`.
    pub fn from_result(result: Result<A, E>) -> Self {
        match result {
            Ok(a) => Validated::Valid(a),
            Err(e) => Validated::Invalid(NonEmptyVec::new(e)),
        }
    }

    /// Creates a `Validated` from an `Option`, using the provided error for `None`.
    pub fn from_option(option: Option<A>, error: impl FnOnce() -> E) -> Self {
        match option {
            Some(a) => Validated::Valid(a),
            None => Validated::Invalid(NonEmptyVec::new(error())),
        }
    }

    /// Validates a value against a predicate, returning an error if it fails.
    pub fn ensure(value: A, predicate: impl FnOnce(&A) -> bool, error: impl FnOnce(&A) -> E) -> Self {
        if predicate(&value) {
            Validated::Valid(value)
        } else {
            let e = error(&value);
            Validated::Invalid(NonEmptyVec::new(e))
        }
    }

    /// Returns `true` if this is `Valid`.
    pub fn is_valid(&self) -> bool {
        matches!(self, Validated::Valid(_))
    }

    /// Returns `true` if this is `Invalid`.
    pub fn is_invalid(&self) -> bool {
        matches!(self, Validated::Invalid(_))
    }

    /// Maps over the valid value.
    pub fn map<B, F: FnOnce(A) -> B>(self, f: F) -> Validated<E, B> {
        match self {
            Validated::Valid(a) => Validated::Valid(f(a)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    /// Maps over the error values.
    pub fn map_error<F2, G: Fn(&E) -> F2>(self, f: G) -> Validated<F2, A> {
        match self {
            Validated::Valid(a) => Validated::Valid(a),
            Validated::Invalid(errors) => Validated::Invalid(errors.map(f)),
        }
    }

    /// Folds the `Validated` into a single value.
    pub fn fold<B, FI: FnOnce(&NonEmptyVec<E>) -> B, FV: FnOnce(A) -> B>(self, on_invalid: FI, on_valid: FV) -> B {
        match self {
            Validated::Valid(a) => on_valid(a),
            Validated::Invalid(ref errors) => on_invalid(errors),
        }
    }

    /// Converts to a `Result`, using the `NonEmptyVec<E>` as the error type.
    pub fn to_result(self) -> Result<A, NonEmptyVec<E>> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(errors) => Err(errors),
        }
    }

    /// Converts to an `Either`.
    pub fn to_either(self) -> Either<NonEmptyVec<E>, A> {
        match self {
            Validated::Valid(a) => Either::Right(a),
            Validated::Invalid(errors) => Either::Left(errors),
        }
    }

    /// Chains a computation, short-circuiting on error (like Either's flat_map).
    pub fn and_then<B, F: FnOnce(A) -> Validated<E, B>>(self, f: F) -> Validated<E, B> {
        match self {
            Validated::Valid(a) => f(a),
            Validated::Invalid(errors) => Validated::Invalid(errors),
        }
    }

    /// Combines two `Validated` values, accumulating errors from both.
    pub fn zip<B>(self, other: &Validated<E, B>) -> Validated<E, (A, B)>
    where
        A: Clone,
        B: Clone,
        E: Clone,
    {
        match (self, other) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid((a, b.clone())),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.append(e2)),
            (Validated::Invalid(e), _) => Validated::Invalid(e),
            (_, Validated::Invalid(e)) => Validated::Invalid(e.clone()),
        }
    }

    /// Combines three `Validated` values, accumulating errors from all.
    pub fn zip3<B, C>(self, b: &Validated<E, B>, c: &Validated<E, C>) -> Validated<E, (A, B, C)>
    where
        A: Clone,
        B: Clone,
        C: Clone,
        E: Clone,
    {
        let mut errors: Option<NonEmptyVec<E>> = None;

        let a_val = match self {
            Validated::Valid(a) => Some(a),
            Validated::Invalid(e) => {
                errors = Some(e);
                None
            }
        };

        let b_val = match b {
            Validated::Valid(b) => Some(b.clone()),
            Validated::Invalid(e) => {
                errors = Some(match errors {
                    Some(existing) => existing.append(e),
                    None => e.clone(),
                });
                None
            }
        };

        let c_val = match c {
            Validated::Valid(c) => Some(c.clone()),
            Validated::Invalid(e) => {
                errors = Some(match errors {
                    Some(existing) => existing.append(e),
                    None => e.clone(),
                });
                None
            }
        };

        match (a_val, b_val, c_val, errors) {
            (Some(a), Some(b), Some(c), None) => Validated::Valid((a, b, c)),
            (_, _, _, Some(errors)) => Validated::Invalid(errors),
            _ => unreachable!(),
        }
    }

    /// Combines four `Validated` values, accumulating errors from all.
    pub fn zip4<B, C, D>(
        self,
        b: &Validated<E, B>,
        c: &Validated<E, C>,
        d: &Validated<E, D>,
    ) -> Validated<E, (A, B, C, D)>
    where
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
        E: Clone,
    {
        let mut errors: Option<NonEmptyVec<E>> = None;

        let a_val = match self {
            Validated::Valid(a) => Some(a),
            Validated::Invalid(e) => {
                errors = Some(e);
                None
            }
        };

        let b_val = match b {
            Validated::Valid(b) => Some(b.clone()),
            Validated::Invalid(e) => {
                errors = Some(match errors {
                    Some(existing) => existing.append(e),
                    None => e.clone(),
                });
                None
            }
        };

        let c_val = match c {
            Validated::Valid(c) => Some(c.clone()),
            Validated::Invalid(e) => {
                errors = Some(match errors {
                    Some(existing) => existing.append(e),
                    None => e.clone(),
                });
                None
            }
        };

        let d_val = match d {
            Validated::Valid(d) => Some(d.clone()),
            Validated::Invalid(e) => {
                errors = Some(match errors {
                    Some(existing) => existing.append(e),
                    None => e.clone(),
                });
                None
            }
        };

        match (a_val, b_val, c_val, d_val, errors) {
            (Some(a), Some(b), Some(c), Some(d), None) => Validated::Valid((a, b, c, d)),
            (_, _, _, _, Some(errors)) => Validated::Invalid(errors),
            _ => unreachable!(),
        }
    }
}

/// Collects an iterator of `Validated` values, accumulating all errors.
///
/// If all values are valid, returns `Valid(Vec<A>)`.
/// If any are invalid, returns `Invalid` with all accumulated errors.
pub fn sequence<E: Clone, A>(iter: impl IntoIterator<Item = Validated<E, A>>) -> Validated<E, Vec<A>> {
    let mut values = Vec::new();
    let mut errors: Option<NonEmptyVec<E>> = None;

    for item in iter {
        match item {
            Validated::Valid(a) => {
                if errors.is_none() {
                    values.push(a);
                }
            }
            Validated::Invalid(e) => {
                errors = Some(match errors {
                    Some(existing) => existing.append(&e),
                    None => e,
                });
            }
        }
    }

    match errors {
        None => Validated::Valid(values),
        Some(errors) => Validated::Invalid(errors),
    }
}

impl<E: fmt::Debug, A: fmt::Debug> fmt::Debug for Validated<E, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Validated::Valid(a) => f.debug_tuple("Valid").field(a).finish(),
            Validated::Invalid(e) => f.debug_tuple("Invalid").field(e).finish(),
        }
    }
}

impl<E: fmt::Display, A: fmt::Display> fmt::Display for Validated<E, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Validated::Valid(a) => write!(f, "Valid({})", a),
            Validated::Invalid(e) => write!(f, "Invalid({})", e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nev;

    #[test]
    fn valid_creation() {
        let v: Validated<String, i32> = Validated::valid(42);
        assert!(v.is_valid());
        assert!(!v.is_invalid());
    }

    #[test]
    fn invalid_creation() {
        let v: Validated<String, i32> = Validated::invalid("error".to_string());
        assert!(v.is_invalid());
        assert!(!v.is_valid());
    }

    #[test]
    fn invalid_many_creation() {
        let v: Validated<&str, i32> = Validated::invalid_many(nev!["e1", "e2"]);
        assert!(v.is_invalid());
    }

    #[test]
    fn from_result_ok() {
        let v = Validated::<String, i32>::from_result(Ok(42));
        assert_eq!(v, Validated::Valid(42));
    }

    #[test]
    fn from_result_err() {
        let v = Validated::<String, i32>::from_result(Err("error".to_string()));
        assert!(v.is_invalid());
    }

    #[test]
    fn from_option_some() {
        let v = Validated::<String, i32>::from_option(Some(42), || "missing".to_string());
        assert_eq!(v, Validated::Valid(42));
    }

    #[test]
    fn from_option_none() {
        let v = Validated::<String, i32>::from_option(None, || "missing".to_string());
        assert!(v.is_invalid());
    }

    #[test]
    fn ensure_passing() {
        let v = Validated::<String, i32>::ensure(42, |x| *x > 0, |x| format!("{} is not positive", x));
        assert_eq!(v, Validated::Valid(42));
    }

    #[test]
    fn ensure_failing() {
        let v = Validated::<String, i32>::ensure(-1, |x| *x > 0, |x| format!("{} is not positive", x));
        assert!(v.is_invalid());
    }

    #[test]
    fn map_valid() {
        let v = Validated::<String, i32>::valid(21);
        let mapped = v.map(|x| x * 2);
        assert_eq!(mapped, Validated::Valid(42));
    }

    #[test]
    fn map_invalid() {
        let v = Validated::<String, i32>::invalid("error".to_string());
        let mapped = v.map(|x| x * 2);
        assert!(mapped.is_invalid());
    }

    #[test]
    fn map_error() {
        let v = Validated::<String, i32>::invalid("error".to_string());
        let mapped = v.map_error(|e| e.len());
        match mapped {
            Validated::Invalid(errors) => assert_eq!(*errors.head(), 5),
            _ => panic!("expected Invalid"),
        }
    }

    #[test]
    fn fold_valid() {
        let v = Validated::<String, i32>::valid(42);
        let result = v.fold(|_| "invalid".to_string(), |a| format!("valid: {}", a));
        assert_eq!(result, "valid: 42");
    }

    #[test]
    fn fold_invalid() {
        let v = Validated::<String, i32>::invalid("error".to_string());
        let result = v.fold(
            |errors| format!("errors: {}", errors.len()),
            |a| format!("valid: {}", a),
        );
        assert_eq!(result, "errors: 1");
    }

    #[test]
    fn to_result_valid() {
        let v = Validated::<String, i32>::valid(42);
        assert_eq!(v.to_result(), Ok(42));
    }

    #[test]
    fn to_result_invalid() {
        let v = Validated::<String, i32>::invalid("error".to_string());
        assert!(v.to_result().is_err());
    }

    #[test]
    fn to_either_valid() {
        let v = Validated::<String, i32>::valid(42);
        assert_eq!(v.to_either(), Either::Right(42));
    }

    #[test]
    fn to_either_invalid() {
        let v = Validated::<String, i32>::invalid("error".to_string());
        assert!(v.to_either().is_left());
    }

    #[test]
    fn and_then_valid() {
        let v = Validated::<String, i32>::valid(42);
        let result = v.and_then(|x| Validated::valid(x * 2));
        assert_eq!(result, Validated::Valid(84));
    }

    #[test]
    fn and_then_invalid() {
        let v = Validated::<String, i32>::invalid("first".to_string());
        let result = v.and_then(|x| Validated::valid(x * 2));
        assert!(result.is_invalid());
    }

    #[test]
    fn zip_valid_valid() {
        let a = Validated::<String, i32>::valid(1);
        let b = Validated::<String, i32>::valid(2);
        let result = a.zip(&b);
        assert_eq!(result, Validated::Valid((1, 2)));
    }

    #[test]
    fn zip_valid_invalid() {
        let a = Validated::<String, i32>::valid(1);
        let b = Validated::<String, i32>::invalid("error".to_string());
        let result = a.zip(&b);
        assert!(result.is_invalid());
    }

    #[test]
    fn zip_invalid_invalid_accumulates() {
        let a = Validated::<String, i32>::invalid("error1".to_string());
        let b = Validated::<String, i32>::invalid("error2".to_string());
        let result = a.zip(&b);
        match result {
            Validated::Invalid(errors) => {
                assert_eq!(errors.len(), 2);
                assert_eq!(errors.to_vec(), vec!["error1".to_string(), "error2".to_string()]);
            }
            _ => panic!("expected Invalid"),
        }
    }

    #[test]
    fn zip3_all_valid() {
        let a = Validated::<String, i32>::valid(1);
        let b = Validated::<String, i32>::valid(2);
        let c = Validated::<String, i32>::valid(3);
        let result = a.zip3(&b, &c);
        assert_eq!(result, Validated::Valid((1, 2, 3)));
    }

    #[test]
    fn zip3_accumulates_all_errors() {
        let a = Validated::<String, i32>::invalid("e1".to_string());
        let b = Validated::<String, i32>::invalid("e2".to_string());
        let c = Validated::<String, i32>::invalid("e3".to_string());
        let result = a.zip3(&b, &c);
        match result {
            Validated::Invalid(errors) => {
                assert_eq!(errors.len(), 3);
                assert_eq!(errors.to_vec(), vec!["e1", "e2", "e3"]);
            }
            _ => panic!("expected Invalid"),
        }
    }

    #[test]
    fn zip4_all_valid() {
        let a = Validated::<String, i32>::valid(1);
        let b = Validated::<String, i32>::valid(2);
        let c = Validated::<String, i32>::valid(3);
        let d = Validated::<String, i32>::valid(4);
        let result = a.zip4(&b, &c, &d);
        assert_eq!(result, Validated::Valid((1, 2, 3, 4)));
    }

    #[test]
    fn zip4_accumulates_all_errors() {
        let a = Validated::<String, i32>::invalid("e1".to_string());
        let b = Validated::<String, i32>::invalid("e2".to_string());
        let c = Validated::<String, i32>::invalid("e3".to_string());
        let d = Validated::<String, i32>::invalid("e4".to_string());
        let result = a.zip4(&b, &c, &d);
        match result {
            Validated::Invalid(errors) => {
                assert_eq!(errors.len(), 4);
                assert_eq!(errors.to_vec(), vec!["e1", "e2", "e3", "e4"]);
            }
            _ => panic!("expected Invalid"),
        }
    }

    #[test]
    fn sequence_all_valid() {
        let items = vec![
            Validated::<String, i32>::valid(1),
            Validated::valid(2),
            Validated::valid(3),
        ];
        let result = sequence(items);
        assert_eq!(result, Validated::Valid(vec![1, 2, 3]));
    }

    #[test]
    fn sequence_all_invalid() {
        let items = vec![
            Validated::<String, i32>::invalid("e1".to_string()),
            Validated::invalid("e2".to_string()),
        ];
        let result = sequence(items);
        match result {
            Validated::Invalid(errors) => assert_eq!(errors.len(), 2),
            _ => panic!("expected Invalid"),
        }
    }

    #[test]
    fn sequence_mixed() {
        let items = vec![
            Validated::<String, i32>::valid(1),
            Validated::invalid("e1".to_string()),
            Validated::valid(3),
            Validated::invalid("e2".to_string()),
        ];
        let result = sequence(items);
        match result {
            Validated::Invalid(errors) => {
                assert_eq!(errors.len(), 2);
                assert_eq!(errors.to_vec(), vec!["e1", "e2"]);
            }
            _ => panic!("expected Invalid"),
        }
    }

    #[test]
    fn sequence_empty() {
        let items: Vec<Validated<String, i32>> = vec![];
        let result = sequence(items);
        assert_eq!(result, Validated::Valid(vec![]));
    }

    #[test]
    fn display_formatting() {
        let valid = Validated::<String, i32>::valid(42);
        assert_eq!(format!("{}", valid), "Valid(42)");

        let invalid = Validated::<String, i32>::invalid("error".to_string());
        assert_eq!(format!("{}", invalid), "Invalid([error])");
    }

    #[test]
    fn debug_formatting() {
        let valid = Validated::<String, i32>::valid(42);
        assert_eq!(format!("{:?}", valid), "Valid(42)");
    }

    #[test]
    fn zip_then_map_pattern() {
        let name = Validated::<String, String>::valid("Jordan".to_string());
        let age = Validated::<String, i32>::valid(30);
        let result = name.zip(&age).map(|(n, a)| format!("{} is {}", n, a));
        assert_eq!(result, Validated::Valid("Jordan is 30".to_string()));
    }
}

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn error_count_additive(
            n1 in 1usize..5,
            n2 in 1usize..5,
        ) {
            let errors1: Vec<String> = (0..n1).map(|i| format!("e{}", i)).collect();
            let errors2: Vec<String> = (0..n2).map(|i| format!("f{}", i)).collect();

            let v1 = Validated::<String, i32>::invalid_many(
                NonEmptyVec::from_vec(errors1).unwrap()
            );
            let v2 = Validated::<String, i32>::invalid_many(
                NonEmptyVec::from_vec(errors2).unwrap()
            );

            let result = v1.zip(&v2);
            match result {
                Validated::Invalid(errors) => {
                    prop_assert_eq!(errors.len(), n1 + n2);
                }
                _ => prop_assert!(false, "expected Invalid"),
            }
        }

        #[test]
        fn valid_zip_preserves_values(a in any::<i32>(), b in any::<i32>()) {
            let va = Validated::<String, i32>::valid(a);
            let vb = Validated::<String, i32>::valid(b);
            let result = va.zip(&vb);
            prop_assert_eq!(result, Validated::Valid((a, b)));
        }
    }
}
