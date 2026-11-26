//! Bounded repeat-on-success policies. TS: `io.repeatUntil` / `io.repeatWhile`.
//!
//! These repeat on `Ok` values that haven't met a condition yet. The retry helpers repeat on
//! `Err`. The first `Err` here stops the loop and is returned unchanged.

use std::fmt;
use std::future::Future;
use std::time::Duration;

/// The repeat bound was reached before the condition held. TS: `RepeatExhausted<A>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepeatExhausted<A> {
    /// The bound that was reached.
    pub max: usize,
    /// The last value produced, or `None` when `max` was 0 and nothing ran.
    pub last_value: Option<A>,
}

impl<A> fmt::Display for RepeatExhausted<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Repeat exhausted after {} iterations", self.max)
    }
}

impl<A: fmt::Debug> std::error::Error for RepeatExhausted<A> {}

/// The error from [`repeat_until`] and [`repeat_while`]. TS: `E | RepeatExhausted<A>`.
///
/// Rust has no union types, so the two cases are variants. To widen into a module error enum,
/// implement `From<RepeatError<E, A>>` for it and use `?`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepeatError<E, A> {
    /// An iteration returned `Err`.
    Failure(E),
    /// The bound was reached first.
    Exhausted(RepeatExhausted<A>),
}

impl<E: fmt::Display, A> fmt::Display for RepeatError<E, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RepeatError::Failure(e) => e.fmt(f),
            RepeatError::Exhausted(x) => x.fmt(f),
        }
    }
}

impl<E: fmt::Debug + fmt::Display, A: fmt::Debug> std::error::Error for RepeatError<E, A> {}

/// Runs the factory until `done(&value)` holds, at most `max` times.
/// TS: `io.repeatUntil(done, { max, delayMs })`.
///
/// - Returns the first value that satisfies `done`.
/// - The first `Err` is returned at once, as `RepeatError::Failure`.
/// - After `max` values that don't satisfy `done`, returns `RepeatError::Exhausted` with the
///   last value. With `max == 0` the factory never runs and `last_value` is `None`.
/// - `delay`, when given, is slept between iterations.
///
/// # Examples
///
/// ```
/// use functype_io::{repeat_until, RepeatError};
/// use std::cell::Cell;
///
/// # tokio::runtime::Runtime::new().unwrap().block_on(async {
/// let polls = Cell::new(0);
/// let poll_job = || async {
///     polls.set(polls.get() + 1);
///     Ok::<_, String>(polls.get())
/// };
/// let done = repeat_until(20, None, |n| *n >= 3, poll_job).await;
/// assert_eq!(done, Ok(3));
///
/// let polls = Cell::new(0);
/// let never = repeat_until(2, None, |_: &i32| false, || async {
///     polls.set(polls.get() + 1);
///     Ok::<_, String>(polls.get())
/// })
/// .await;
/// assert!(matches!(never, Err(RepeatError::Exhausted(x)) if x.last_value == Some(2)));
/// # });
/// ```
pub async fn repeat_until<A, E, F, Fut, D>(
    max: usize,
    delay: Option<Duration>,
    mut done: D,
    mut factory: F,
) -> Result<A, RepeatError<E, A>>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
    D: FnMut(&A) -> bool,
{
    if max == 0 {
        return Err(RepeatError::Exhausted(RepeatExhausted { max, last_value: None }));
    }
    let mut remaining = max;
    loop {
        let value = factory().await.map_err(RepeatError::Failure)?;
        if done(&value) {
            return Ok(value);
        }
        if remaining <= 1 {
            return Err(RepeatError::Exhausted(RepeatExhausted {
                max,
                last_value: Some(value),
            }));
        }
        remaining -= 1;
        if let Some(d) = delay {
            tokio::time::sleep(d).await;
        }
    }
}

/// Runs the factory while `keep_going(&value)` holds, at most `max` times.
/// TS: `io.repeatWhile(cont, { max, delayMs })`.
///
/// The same as [`repeat_until`] with the condition negated.
pub async fn repeat_while<A, E, F, Fut, C>(
    max: usize,
    delay: Option<Duration>,
    mut keep_going: C,
    factory: F,
) -> Result<A, RepeatError<E, A>>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
    C: FnMut(&A) -> bool,
{
    repeat_until(max, delay, |a| !keep_going(a), factory).await
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use tokio::time::Instant;

    async fn counter(calls: &Cell<usize>) -> Result<usize, String> {
        calls.set(calls.get() + 1);
        Ok(calls.get())
    }

    #[tokio::test]
    async fn max_zero_never_runs() {
        let calls = Cell::new(0);
        let r = repeat_until(0, None, |_| true, || counter(&calls)).await;
        assert_eq!(
            r,
            Err(RepeatError::Exhausted(RepeatExhausted {
                max: 0,
                last_value: None
            }))
        );
        assert_eq!(calls.get(), 0);
    }

    #[tokio::test]
    async fn runs_exactly_max_times_then_exhausts_with_last_value() {
        let calls = Cell::new(0);
        let r = repeat_until(3, None, |_| false, || counter(&calls)).await;
        assert_eq!(
            r,
            Err(RepeatError::Exhausted(RepeatExhausted {
                max: 3,
                last_value: Some(3)
            }))
        );
        assert_eq!(calls.get(), 3);
    }

    #[tokio::test]
    async fn returns_first_satisfying_value() {
        let calls = Cell::new(0);
        let r = repeat_until(10, None, |n| *n == 4, || counter(&calls)).await;
        assert_eq!(r, Ok(4));
        assert_eq!(calls.get(), 4);
    }

    #[tokio::test]
    async fn first_failure_short_circuits() {
        let calls = Cell::new(0);
        let r = repeat_until(
            10,
            None,
            |_: &usize| false,
            || async {
                calls.set(calls.get() + 1);
                if calls.get() == 2 {
                    Err("broke".to_string())
                } else {
                    Ok(calls.get())
                }
            },
        )
        .await;
        assert_eq!(r, Err(RepeatError::Failure("broke".to_string())));
        assert_eq!(calls.get(), 2);
    }

    #[tokio::test(start_paused = true)]
    async fn delay_is_slept_between_iterations_only() {
        let calls = Cell::new(0);
        let start = Instant::now();
        let r = repeat_until(3, Some(Duration::from_millis(50)), |_| false, || counter(&calls)).await;
        assert!(r.is_err());
        assert_eq!(start.elapsed(), Duration::from_millis(100));
    }

    #[tokio::test]
    async fn repeat_while_negates_the_condition() {
        let calls = Cell::new(0);
        let r = repeat_while(10, None, |n| *n < 3, || counter(&calls)).await;
        assert_eq!(r, Ok(3));
    }

    #[test]
    fn display_matches_ts_message() {
        let x = RepeatExhausted::<i32> {
            max: 5,
            last_value: None,
        };
        assert_eq!(x.to_string(), "Repeat exhausted after 5 iterations");
    }
}
