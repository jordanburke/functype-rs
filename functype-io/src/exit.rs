use functype_core::try_type::TryError;

/// How an effect ended: the Rust form of TS functype's `Exit<E, A>`.
///
/// A plain `.await` gives `Result<A, E>`, where a panic unwinds and a dropped future reports
/// nothing. [`run_exit`](crate::run_exit) reports all four outcomes as values instead.
///
/// | TS | Rust |
/// |---|---|
/// | `Success(value)` | `Exit::Success(a)` |
/// | `Failure(error)` | `Exit::Failure(e)` |
/// | `Die(defect)` | `Exit::Die(TryError)`, a caught panic |
/// | `Interrupted` | `Exit::Interrupted`, cancelled before it finished |
///
/// `fold` and `match` from TS become a Rust `match` on the variants.
///
/// # Examples
///
/// ```
/// use functype_io::Exit;
///
/// let exit: Exit<String, i32> = Exit::Success(21);
/// assert_eq!(exit.map(|n| n * 2).ok(), Some(42));
///
/// let failed: Exit<String, i32> = Exit::Failure("boom".into());
/// assert!(failed.is_failure());
/// assert_eq!(failed.unwrap_or_else(|| 0), 0);
/// ```
#[derive(Debug)]
pub enum Exit<E, A> {
    /// The effect produced a value.
    Success(A),
    /// The effect returned `Err`.
    Failure(E),
    /// The effect panicked. The panic was caught and holds its message and payload.
    Die(TryError),
    /// The effect was cancelled before it finished.
    Interrupted,
}

impl<E, A> Exit<E, A> {
    /// Returns `true` for [`Exit::Success`].
    pub fn is_success(&self) -> bool {
        matches!(self, Exit::Success(_))
    }

    /// Returns `true` for [`Exit::Failure`].
    pub fn is_failure(&self) -> bool {
        matches!(self, Exit::Failure(_))
    }

    /// Returns `true` for [`Exit::Die`].
    pub fn is_die(&self) -> bool {
        matches!(self, Exit::Die(_))
    }

    /// Returns `true` for [`Exit::Interrupted`].
    pub fn is_interrupted(&self) -> bool {
        matches!(self, Exit::Interrupted)
    }

    /// Maps the success value. TS: `map`.
    pub fn map<B>(self, f: impl FnOnce(A) -> B) -> Exit<E, B> {
        match self {
            Exit::Success(a) => Exit::Success(f(a)),
            Exit::Failure(e) => Exit::Failure(e),
            Exit::Die(d) => Exit::Die(d),
            Exit::Interrupted => Exit::Interrupted,
        }
    }

    /// Maps the error value. TS: `mapError`.
    pub fn map_err<E2>(self, f: impl FnOnce(E) -> E2) -> Exit<E2, A> {
        match self {
            Exit::Success(a) => Exit::Success(a),
            Exit::Failure(e) => Exit::Failure(f(e)),
            Exit::Die(d) => Exit::Die(d),
            Exit::Interrupted => Exit::Interrupted,
        }
    }

    /// Chains on the success value. TS: `flatMap`.
    pub fn and_then<B>(self, f: impl FnOnce(A) -> Exit<E, B>) -> Exit<E, B> {
        match self {
            Exit::Success(a) => f(a),
            Exit::Failure(e) => Exit::Failure(e),
            Exit::Die(d) => Exit::Die(d),
            Exit::Interrupted => Exit::Interrupted,
        }
    }

    /// Returns the success value, if any. TS: `toOption`.
    pub fn ok(self) -> Option<A> {
        match self {
            Exit::Success(a) => Some(a),
            _ => None,
        }
    }

    /// Returns the typed error, if any. A `Die` or `Interrupted` gives `None`.
    pub fn err(self) -> Option<E> {
        match self {
            Exit::Failure(e) => Some(e),
            _ => None,
        }
    }

    /// Returns the success value, or calls `default` for any other outcome. TS: `getOrElse`.
    pub fn unwrap_or_else(self, default: impl FnOnce() -> A) -> A {
        match self {
            Exit::Success(a) => a,
            _ => default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn die() -> Exit<String, i32> {
        Exit::Die(TryError::from_panic(Box::new("bad")))
    }

    #[test]
    fn predicates_match_one_variant_each() {
        let all: [Exit<String, i32>; 4] = [Exit::Success(1), Exit::Failure("e".into()), die(), Exit::Interrupted];
        let flags: Vec<[bool; 4]> = all
            .iter()
            .map(|x| [x.is_success(), x.is_failure(), x.is_die(), x.is_interrupted()])
            .collect();
        for (i, row) in flags.iter().enumerate() {
            for (j, flag) in row.iter().enumerate() {
                assert_eq!(*flag, i == j, "variant {i}, predicate {j}");
            }
        }
    }

    #[test]
    fn map_touches_only_success() {
        assert_eq!(Exit::<String, i32>::Success(2).map(|n| n * 10).ok(), Some(20));
        assert_eq!(
            Exit::<String, i32>::Failure("e".into()).map(|n| n * 10).err(),
            Some("e".to_string())
        );
        assert!(die().map(|n| n * 10).is_die());
        assert!(Exit::<String, i32>::Interrupted.map(|n| n * 10).is_interrupted());
    }

    #[test]
    fn map_err_touches_only_failure() {
        assert_eq!(
            Exit::<String, i32>::Failure("e".into()).map_err(|e| e.len()).err(),
            Some(1)
        );
        assert_eq!(Exit::<String, i32>::Success(3).map_err(|e| e.len()).ok(), Some(3));
        assert!(die().map_err(|e| e.len()).is_die());
    }

    #[test]
    fn and_then_chains_success() {
        let chained: Exit<String, i32> =
            Exit::<String, i32>::Success(2).and_then(|n| Exit::Failure(format!("got {n}")));
        assert_eq!(chained.err(), Some("got 2".to_string()));
        assert!(die().and_then(Exit::<String, i32>::Success).is_die());
    }

    #[test]
    fn die_keeps_panic_message() {
        match die() {
            Exit::Die(d) => assert_eq!(d.message(), "bad"),
            _ => unreachable!(),
        }
    }

    #[test]
    fn unwrap_or_else_is_lazy() {
        let mut called = false;
        let v = Exit::<String, i32>::Success(5).unwrap_or_else(|| {
            called = true;
            0
        });
        assert_eq!(v, 5);
        assert!(!called);
        assert_eq!(Exit::<String, i32>::Interrupted.unwrap_or_else(|| 9), 9);
    }
}
