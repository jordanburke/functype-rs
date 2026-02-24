use std::fmt;

/// A right-biased disjoint union type, equivalent to Scala's `Either`.
///
/// `Either<L, R>` represents a value of one of two possible types.
/// By convention, `Right` is the "success" case and `Left` is the "error" case,
/// mirroring Scala's right-biased Either.
///
/// # Examples
/// ```
/// use functype_core::either::Either;
///
/// let right: Either<String, i32> = Either::right(42);
/// let result = right.map(|x| x * 2);
/// assert_eq!(result.right_value(), Some(&84));
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<L, R> Either<L, R> {
    /// Creates a `Left` value.
    pub fn left(value: L) -> Self {
        Either::Left(value)
    }

    /// Creates a `Right` value.
    pub fn right(value: R) -> Self {
        Either::Right(value)
    }

    /// Creates an `Either` from a `Result`.
    pub fn from_result(result: Result<R, L>) -> Self {
        match result {
            Ok(r) => Either::Right(r),
            Err(l) => Either::Left(l),
        }
    }

    /// Creates an `Either` from an `Option`, using `left_value` for `None`.
    pub fn from_option(option: Option<R>, left_value: impl FnOnce() -> L) -> Self {
        match option {
            Some(r) => Either::Right(r),
            None => Either::Left(left_value()),
        }
    }

    /// Returns `true` if this is a `Left`.
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Returns `true` if this is a `Right`.
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Returns the `Left` value, if present.
    pub fn left_value(&self) -> Option<&L> {
        match self {
            Either::Left(l) => Some(l),
            Either::Right(_) => None,
        }
    }

    /// Returns the `Right` value, if present.
    pub fn right_value(&self) -> Option<&R> {
        match self {
            Either::Left(_) => None,
            Either::Right(r) => Some(r),
        }
    }

    /// Applies one of two functions depending on the variant.
    pub fn fold<T, FL: FnOnce(&L) -> T, FR: FnOnce(&R) -> T>(&self, on_left: FL, on_right: FR) -> T {
        match self {
            Either::Left(l) => on_left(l),
            Either::Right(r) => on_right(r),
        }
    }

    /// Maps over the `Right` value (right-biased).
    pub fn map<U, F: FnOnce(&R) -> U>(&self, f: F) -> Either<L, U>
    where
        L: Clone,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    /// Maps over the `Left` value.
    pub fn map_left<U, F: FnOnce(&L) -> U>(&self, f: F) -> Either<U, R>
    where
        R: Clone,
    {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(r.clone()),
        }
    }

    /// Maps over both sides simultaneously.
    pub fn bimap<A, B, FL: FnOnce(&L) -> A, FR: FnOnce(&R) -> B>(&self, on_left: FL, on_right: FR) -> Either<A, B> {
        match self {
            Either::Left(l) => Either::Left(on_left(l)),
            Either::Right(r) => Either::Right(on_right(r)),
        }
    }

    /// Chains a computation over the `Right` value (right-biased).
    pub fn flat_map<U, F: FnOnce(&R) -> Either<L, U>>(&self, f: F) -> Either<L, U>
    where
        L: Clone,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => f(r),
        }
    }

    /// Alias for `flat_map`, compatible with `and_then` convention (Option/Result).
    pub fn and_then<U, F: FnOnce(&R) -> Either<L, U>>(&self, f: F) -> Either<L, U>
    where
        L: Clone,
    {
        self.flat_map(f)
    }

    /// Swaps `Left` and `Right`.
    pub fn swap(self) -> Either<R, L> {
        match self {
            Either::Left(l) => Either::Right(l),
            Either::Right(r) => Either::Left(r),
        }
    }

    /// Returns the `Right` value, or computes a default from the `Left`.
    pub fn get_or_else<F: FnOnce(&L) -> R>(&self, f: F) -> R
    where
        R: Clone,
    {
        match self {
            Either::Left(l) => f(l),
            Either::Right(r) => r.clone(),
        }
    }

    /// Applies a side-effect to whichever variant is present, then returns self.
    pub fn tap<FL: FnOnce(&L), FR: FnOnce(&R)>(&self, on_left: FL, on_right: FR) -> &Self {
        match self {
            Either::Left(l) => on_left(l),
            Either::Right(r) => on_right(r),
        }
        self
    }

    /// Applies a side-effect if `Right`.
    pub fn tap_right<F: FnOnce(&R)>(&self, f: F) -> &Self {
        if let Either::Right(r) = self {
            f(r);
        }
        self
    }

    /// Applies a side-effect if `Left`.
    pub fn tap_left<F: FnOnce(&L)>(&self, f: F) -> &Self {
        if let Either::Left(l) = self {
            f(l);
        }
        self
    }

    /// Converts to a `Result<R, L>`.
    pub fn to_result(self) -> Result<R, L> {
        match self {
            Either::Left(l) => Err(l),
            Either::Right(r) => Ok(r),
        }
    }

    /// Converts to an `Option<R>`, discarding any `Left` value.
    pub fn to_option(self) -> Option<R> {
        match self {
            Either::Left(_) => None,
            Either::Right(r) => Some(r),
        }
    }

    /// Flattens a nested `Either<L, Either<L, R>>` into `Either<L, R>`.
    pub fn flatten(self) -> Either<L, R>
    where
        R: Into<Either<L, R>>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => r.into(),
        }
    }

    /// Applies a function wrapped in an `Either` to this `Either`'s value.
    pub fn ap<U, F>(&self, ef: &Either<L, F>) -> Either<L, U>
    where
        L: Clone,
        R: Clone,
        F: Fn(&R) -> U,
    {
        match (self, ef) {
            (Either::Right(r), Either::Right(f)) => Either::Right(f(r)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    /// Zips two `Either` values together, returning `Left` if either is `Left`.
    pub fn zip<'a, U>(&'a self, other: &'a Either<L, U>) -> Either<L, (&'a R, &'a U)>
    where
        L: Clone,
    {
        match (self, other) {
            (Either::Right(r), Either::Right(u)) => Either::Right((r, u)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    /// Filters the `Right` value, converting to `Left` if the predicate fails.
    pub fn filter_or_else<F: FnOnce(&R) -> bool, G: FnOnce(&R) -> L>(&self, pred: F, or_else: G) -> Either<L, R>
    where
        R: Clone,
        L: Clone,
    {
        match self {
            Either::Right(r) if pred(r) => Either::Right(r.clone()),
            Either::Right(r) => Either::Left(or_else(r)),
            Either::Left(l) => Either::Left(l.clone()),
        }
    }

    /// Returns `true` if `Right` and the value satisfies the predicate.
    pub fn exists<F: FnOnce(&R) -> bool>(&self, f: F) -> bool {
        match self {
            Either::Right(r) => f(r),
            Either::Left(_) => false,
        }
    }

    /// Returns `true` if `Left`, or if `Right` and the predicate holds.
    pub fn for_all<F: FnOnce(&R) -> bool>(&self, f: F) -> bool {
        match self {
            Either::Right(r) => f(r),
            Either::Left(_) => true,
        }
    }

    /// Returns an iterator over the `Right` value (0 or 1 elements).
    pub fn iter(&self) -> EitherIter<'_, R> {
        EitherIter {
            value: self.right_value(),
        }
    }
}

/// Iterator over the `Right` value of an `Either` (0 or 1 elements).
pub struct EitherIter<'a, R> {
    value: Option<&'a R>,
}

impl<'a, R> Iterator for EitherIter<'a, R> {
    type Item = &'a R;

    fn next(&mut self) -> Option<Self::Item> {
        self.value.take()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.value.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<'a, R> ExactSizeIterator for EitherIter<'a, R> {}

impl<L, R> IntoIterator for Either<L, R> {
    type Item = R;
    type IntoIter = std::option::IntoIter<R>;

    fn into_iter(self) -> Self::IntoIter {
        self.to_option().into_iter()
    }
}

impl<L, R> From<Result<R, L>> for Either<L, R> {
    fn from(result: Result<R, L>) -> Self {
        Either::from_result(result)
    }
}

impl<L, R> From<Either<L, R>> for Result<R, L> {
    fn from(either: Either<L, R>) -> Self {
        either.to_result()
    }
}

impl<L: fmt::Debug, R: fmt::Debug> fmt::Debug for Either<L, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(l) => f.debug_tuple("Left").field(l).finish(),
            Either::Right(r) => f.debug_tuple("Right").field(r).finish(),
        }
    }
}

impl<L: fmt::Display, R: fmt::Display> fmt::Display for Either<L, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(l) => write!(f, "Left({})", l),
            Either::Right(r) => write!(f, "Right({})", r),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn left_creation() {
        let e: Either<&str, i32> = Either::left("error");
        assert!(e.is_left());
        assert!(!e.is_right());
        assert_eq!(e.left_value(), Some(&"error"));
        assert_eq!(e.right_value(), None);
    }

    #[test]
    fn right_creation() {
        let e: Either<&str, i32> = Either::right(42);
        assert!(!e.is_left());
        assert!(e.is_right());
        assert_eq!(e.left_value(), None);
        assert_eq!(e.right_value(), Some(&42));
    }

    #[test]
    fn from_result_ok() {
        let result: Result<i32, &str> = Ok(42);
        let e = Either::from_result(result);
        assert_eq!(e, Either::Right(42));
    }

    #[test]
    fn from_result_err() {
        let result: Result<i32, &str> = Err("fail");
        let e = Either::from_result(result);
        assert_eq!(e, Either::Left("fail"));
    }

    #[test]
    fn from_option_some() {
        let e = Either::from_option(Some(42), || "missing");
        assert_eq!(e, Either::Right(42));
    }

    #[test]
    fn from_option_none() {
        let e = Either::<&str, i32>::from_option(None, || "missing");
        assert_eq!(e, Either::Left("missing"));
    }

    #[test]
    fn fold_extracts_both_sides() {
        let left: Either<i32, i32> = Either::left(10);
        let right: Either<i32, i32> = Either::right(20);

        assert_eq!(left.fold(|l| l * 2, |r| r * 3), 20);
        assert_eq!(right.fold(|l| l * 2, |r| r * 3), 60);
    }

    #[test]
    fn map_transforms_right() {
        let e: Either<&str, i32> = Either::right(21);
        let mapped = e.map(|x| x * 2);
        assert_eq!(mapped, Either::Right(42));
    }

    #[test]
    fn map_preserves_left() {
        let e: Either<&str, i32> = Either::left("error");
        let mapped = e.map(|x| x * 2);
        assert_eq!(mapped, Either::Left("error"));
    }

    #[test]
    fn map_identity_law() {
        let e: Either<&str, i32> = Either::right(42);
        let mapped = e.map(|x| *x);
        assert_eq!(mapped, Either::Right(42));
    }

    #[test]
    fn map_left_transforms_left() {
        let e: Either<i32, &str> = Either::left(42);
        let mapped = e.map_left(|x| x.to_string());
        assert_eq!(mapped, Either::Left("42".to_string()));
    }

    #[test]
    fn bimap_transforms_both() {
        let left: Either<i32, &str> = Either::left(42);
        let right: Either<i32, &str> = Either::right("hello");

        assert_eq!(
            left.bimap(|l| l.to_string(), |r| r.len()),
            Either::Left("42".to_string())
        );
        assert_eq!(right.bimap(|l| l.to_string(), |r| r.len()), Either::Right(5));
    }

    #[test]
    fn flat_map_chains_right() {
        let e: Either<&str, i32> = Either::right(42);
        let result = e.flat_map(|x| {
            if *x > 0 {
                Either::right(x.to_string())
            } else {
                Either::left("non-positive")
            }
        });
        assert_eq!(result, Either::Right("42".to_string()));
    }

    #[test]
    fn flat_map_preserves_left() {
        let e: Either<&str, i32> = Either::left("error");
        let result = e.flat_map(|x| Either::right(x.to_string()));
        assert_eq!(result, Either::Left("error"));
    }

    #[test]
    fn flat_map_associativity() {
        let e: Either<&str, i32> = Either::right(10);
        let f = |x: &i32| -> Either<&str, i32> { Either::right(x + 1) };
        let g = |x: &i32| -> Either<&str, i32> { Either::right(x * 2) };

        // (m >>= f) >>= g  ==  m >>= (x -> f(x) >>= g)
        let left = e.flat_map(f).flat_map(g);
        let right = e.flat_map(|x| f(x).flat_map(g));
        assert_eq!(left, right);
    }

    #[test]
    fn and_then_is_flat_map_alias() {
        let e: Either<&str, i32> = Either::right(42);
        let fm = e.flat_map(|x| Either::right(x + 1));
        let at = e.and_then(|x| Either::right(x + 1));
        assert_eq!(fm, at);
    }

    #[test]
    fn swap_roundtrip() {
        let e: Either<&str, i32> = Either::right(42);
        let swapped = e.clone().swap().swap();
        assert_eq!(e, swapped);
    }

    #[test]
    fn swap_changes_variant() {
        let e: Either<&str, i32> = Either::right(42);
        let swapped = e.swap();
        assert_eq!(swapped, Either::Left(42));
    }

    #[test]
    fn get_or_else_returns_right() {
        let e: Either<&str, i32> = Either::right(42);
        assert_eq!(e.get_or_else(|_| 0), 42);
    }

    #[test]
    fn get_or_else_computes_from_left() {
        let e: Either<i32, i32> = Either::left(5);
        assert_eq!(e.get_or_else(|l| l * 2), 10);
    }

    #[test]
    fn tap_right_side_effect() {
        let e: Either<&str, i32> = Either::right(42);
        let mut seen = 0;
        e.tap_right(|x| seen = *x);
        assert_eq!(seen, 42);
    }

    #[test]
    fn tap_left_side_effect() {
        let e: Either<&str, i32> = Either::left("error");
        let mut seen = "";
        e.tap_left(|l| seen = l);
        assert_eq!(seen, "error");
    }

    #[test]
    fn to_result_roundtrip() {
        let original: Result<i32, &str> = Ok(42);
        let either = Either::from_result(original);
        let result: Result<i32, &str> = either.to_result();
        assert_eq!(result, Ok(42));
    }

    #[test]
    fn to_option_some_for_right() {
        let e: Either<&str, i32> = Either::right(42);
        assert_eq!(e.to_option(), Some(42));
    }

    #[test]
    fn to_option_none_for_left() {
        let e: Either<&str, i32> = Either::left("error");
        assert_eq!(e.to_option(), None);
    }

    #[test]
    fn ap_applies_function() {
        let value: Either<&str, i32> = Either::right(21);
        let f: Either<&str, Box<dyn Fn(&i32) -> i32>> = Either::right(Box::new(|x| x * 2));
        let result = value.ap(&f);
        assert_eq!(result, Either::Right(42));
    }

    #[test]
    fn ap_left_value_propagates() {
        let value: Either<&str, i32> = Either::left("error");
        let f: Either<&str, fn(&i32) -> i32> = Either::right(|x| x * 2);
        let result = value.ap(&f);
        assert_eq!(result, Either::Left("error"));
    }

    #[test]
    fn zip_combines_rights() {
        let a: Either<&str, i32> = Either::right(1);
        let b: Either<&str, &str> = Either::right("hello");
        let zipped = a.zip(&b);
        assert_eq!(zipped, Either::Right((&1, &"hello")));
    }

    #[test]
    fn zip_propagates_left() {
        let a: Either<&str, i32> = Either::left("error");
        let b: Either<&str, &str> = Either::right("hello");
        let zipped = a.zip(&b);
        assert_eq!(zipped, Either::Left("error"));
    }

    #[test]
    fn filter_or_else_passes() {
        let e: Either<&str, i32> = Either::right(42);
        let result = e.filter_or_else(|x| *x > 0, |_| "non-positive");
        assert_eq!(result, Either::Right(42));
    }

    #[test]
    fn filter_or_else_fails() {
        let e: Either<&str, i32> = Either::right(-1);
        let result = e.filter_or_else(|x| *x > 0, |_| "non-positive");
        assert_eq!(result, Either::Left("non-positive"));
    }

    #[test]
    fn exists_checks_right() {
        let right: Either<&str, i32> = Either::right(42);
        let left: Either<&str, i32> = Either::left("error");
        assert!(right.exists(|x| *x == 42));
        assert!(!right.exists(|x| *x == 0));
        assert!(!left.exists(|_| true));
    }

    #[test]
    fn for_all_vacuously_true_for_left() {
        let left: Either<&str, i32> = Either::left("error");
        assert!(left.for_all(|_| false));
    }

    #[test]
    fn iter_over_right() {
        let e: Either<&str, i32> = Either::right(42);
        let collected: Vec<&i32> = e.iter().collect();
        assert_eq!(collected, vec![&42]);
    }

    #[test]
    fn iter_empty_for_left() {
        let e: Either<&str, i32> = Either::left("error");
        let collected: Vec<&i32> = e.iter().collect();
        assert!(collected.is_empty());
    }

    #[test]
    fn into_iter_for_right() {
        let e: Either<&str, i32> = Either::right(42);
        let collected: Vec<i32> = e.into_iter().collect();
        assert_eq!(collected, vec![42]);
    }

    #[test]
    fn from_trait_result_to_either() {
        let e: Either<&str, i32> = Ok(42).into();
        assert_eq!(e, Either::Right(42));
    }

    #[test]
    fn from_trait_either_to_result() {
        let r: Result<i32, &str> = Either::right(42).into();
        assert_eq!(r, Ok(42));
    }

    #[test]
    fn display_formatting() {
        let left: Either<&str, i32> = Either::left("error");
        let right: Either<&str, i32> = Either::right(42);
        assert_eq!(format!("{}", left), "Left(error)");
        assert_eq!(format!("{}", right), "Right(42)");
    }

    #[test]
    fn debug_formatting() {
        let left: Either<&str, i32> = Either::left("error");
        let right: Either<&str, i32> = Either::right(42);
        assert_eq!(format!("{:?}", left), "Left(\"error\")");
        assert_eq!(format!("{:?}", right), "Right(42)");
    }
}

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;

    fn arb_either() -> impl Strategy<Value = Either<String, i32>> {
        prop_oneof![
            any::<i32>().prop_map(Either::right),
            "[a-z]{1,10}".prop_map(Either::left),
        ]
    }

    proptest! {
        #[test]
        fn map_identity(e in arb_either()) {
            let mapped = e.map(|x| *x);
            if let Either::Right(r) = &e {
                prop_assert_eq!(mapped.right_value(), Some(r));
            }
        }

        #[test]
        fn flat_map_associativity(x in any::<i32>()) {
            let e: Either<String, i32> = Either::right(x);
            let f = |v: &i32| -> Either<String, i32> { Either::right(v.wrapping_add(1)) };
            let g = |v: &i32| -> Either<String, i32> { Either::right(v.wrapping_mul(2)) };

            let left = e.flat_map(f).flat_map(g);
            let right = e.flat_map(|v| f(v).flat_map(g));
            prop_assert_eq!(left, right);
        }

        #[test]
        fn swap_roundtrip(e in arb_either()) {
            let double_swapped = e.clone().swap().swap();
            prop_assert_eq!(e, double_swapped);
        }

        #[test]
        fn result_conversion_roundtrip(e in arb_either()) {
            let result: Result<i32, String> = e.clone().to_result();
            let back = Either::from_result(result);
            prop_assert_eq!(e, back);
        }

        #[test]
        fn right_left_exclusive(e in arb_either()) {
            prop_assert_ne!(e.is_left(), e.is_right());
        }
    }
}
