//! Retry policies with TS functype's defaults.
//!
//! A Rust future runs once, so every helper takes a **factory**: a closure that builds a fresh
//! future for each attempt. The factory is always the last argument.
//!
//! These helpers retry on `Err` only. A panic is not retried; it unwinds through them as it
//! would through `.await`. TS recovers defects too, so a TS step that throws and is expected
//! to be retried must return `Err` in Rust.
//!
//! Delays use `tokio::time::sleep`, so they need a Tokio runtime with time enabled.

use std::collections::hash_map::RandomState;
use std::future::Future;
use std::hash::{BuildHasher, Hasher};
use std::time::Duration;

use functype_core::non_empty_vec::NonEmptyVec;

/// Runs the factory once, then retries up to `n` times on `Err`, with no delay.
/// TS: `io.retry(n)`.
///
/// Makes at most `n + 1` attempts. Returns the first `Ok`, or the last `Err`.
///
/// # Examples
///
/// ```
/// use functype_io::retry;
/// use std::cell::Cell;
///
/// # tokio::runtime::Runtime::new().unwrap().block_on(async {
/// let calls = Cell::new(0);
/// let result = retry(3, || async {
///     calls.set(calls.get() + 1);
///     if calls.get() < 3 { Err("not yet") } else { Ok(calls.get()) }
/// })
/// .await;
/// assert_eq!(result, Ok(3));
/// # });
/// ```
pub async fn retry<A, E, F, Fut>(n: usize, factory: F) -> Result<A, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
{
    run_retries(n, factory, |_, _| true, |_| None).await
}

/// Like [`retry`], sleeping `delay` before each retry. TS: `io.retryWithDelay(n, delayMs)`.
pub async fn retry_with_delay<A, E, F, Fut>(n: usize, delay: Duration, factory: F) -> Result<A, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
{
    run_retries(n, factory, |_, _| true, |_| Some(delay)).await
}

/// Retries up to `n` times while `retry_if(&error, attempt)` holds.
/// TS: `io.retryWhile({ n, while, delayMs })`.
///
/// `attempt` is 1 for the first retry. The predicate runs before any delay. When it returns
/// `false`, the current error is returned at once. `delay`, when given, is slept before each
/// retry.
///
/// # Examples
///
/// ```
/// use functype_io::retry_while;
/// use std::cell::Cell;
///
/// #[derive(Debug, PartialEq)]
/// enum HttpError { Server(u16), Client(u16) }
///
/// # tokio::runtime::Runtime::new().unwrap().block_on(async {
/// let calls = Cell::new(0);
/// let result: Result<(), HttpError> = retry_while(
///     3,
///     None,
///     |e, _attempt| matches!(e, HttpError::Server(_)),
///     || async {
///         calls.set(calls.get() + 1);
///         Err(HttpError::Client(404))
///     },
/// )
/// .await;
/// assert_eq!(result, Err(HttpError::Client(404)));
/// assert_eq!(calls.get(), 1); // a 4xx is not retried
/// # });
/// ```
pub async fn retry_while<A, E, F, Fut, P>(n: usize, delay: Option<Duration>, retry_if: P, factory: F) -> Result<A, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
    P: FnMut(&E, usize) -> bool,
{
    run_retries(n, factory, retry_if, |_| delay).await
}

/// An exponential backoff policy. TS: the options of `io.retryWithBackoff`.
///
/// The delay before retry `attempt` (1-indexed) is `min(max, base * factor^(attempt - 1))`.
/// With `jitter`, the actual delay is 50–100% of that, chosen at random.
///
/// [`Backoff::new`] sets the TS defaults: `max` 30 s, `factor` 2, `jitter` on.
///
/// # Examples
///
/// ```
/// use functype_io::Backoff;
/// use std::time::Duration;
///
/// // TS: { n: 3, baseMs: 250 }
/// let policy = Backoff::new(3, Duration::from_millis(250));
/// assert_eq!(policy.max, Duration::from_secs(30));
///
/// let fixed = policy.with_jitter(false);
/// assert_eq!(fixed.delay_for(1), Duration::from_millis(250));
/// assert_eq!(fixed.delay_for(3), Duration::from_millis(1000));
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Backoff {
    /// Maximum number of retries.
    pub n: usize,
    /// Delay before the first retry.
    pub base: Duration,
    /// Cap on each delay.
    pub max: Duration,
    /// Multiplier per retry.
    pub factor: f64,
    /// Whether to apply jitter (50–100% of the computed delay).
    pub jitter: bool,
}

impl Backoff {
    /// A policy with `n` retries starting at `base`, and the TS defaults for the rest.
    pub fn new(n: usize, base: Duration) -> Self {
        Backoff {
            n,
            base,
            max: Duration::from_secs(30),
            factor: 2.0,
            jitter: true,
        }
    }

    /// Sets the cap on each delay. TS: `maxMs`.
    pub fn with_max(self, max: Duration) -> Self {
        Backoff { max, ..self }
    }

    /// Sets the multiplier per retry. TS: `factor`.
    pub fn with_factor(self, factor: f64) -> Self {
        Backoff { factor, ..self }
    }

    /// Turns jitter on or off. TS: `jitter`.
    pub fn with_jitter(self, jitter: bool) -> Self {
        Backoff { jitter, ..self }
    }

    /// The delay before retry `attempt` (1-indexed), without jitter. `attempt` 0 is treated as 1.
    ///
    /// Never panics: a huge `attempt`, `factor` or `base` is capped at `max`, and a negative or
    /// non-finite result becomes zero.
    pub fn delay_for(&self, attempt: usize) -> Duration {
        let exponent = i32::try_from(attempt.saturating_sub(1)).unwrap_or(i32::MAX);
        let computed = self.base.as_secs_f64() * self.factor.powi(exponent);
        self.clamp(computed)
    }

    fn jittered(&self, attempt: usize) -> Duration {
        let computed = self.delay_for(attempt);
        if !self.jitter {
            return computed;
        }
        self.clamp(computed.as_secs_f64() * (0.5 + random_unit() * 0.5))
    }

    fn clamp(&self, secs: f64) -> Duration {
        if secs.is_nan() || secs <= 0.0 {
            return Duration::ZERO;
        }
        let max = self.max.as_secs_f64();
        if secs >= max {
            return self.max;
        }
        Duration::try_from_secs_f64(secs).unwrap_or(self.max)
    }
}

/// Retries with exponential backoff. TS: `io.retryWithBackoff({ n, baseMs, ... })`.
///
/// # Examples
///
/// ```
/// use functype_io::{retry_with_backoff, Backoff};
/// use std::time::Duration;
///
/// # tokio::runtime::Runtime::new().unwrap().block_on(async {
/// let policy = Backoff::new(2, Duration::from_millis(1));
/// let result: Result<(), &str> = retry_with_backoff(policy, || async { Err("down") }).await;
/// assert_eq!(result, Err("down"));
/// # });
/// ```
pub async fn retry_with_backoff<A, E, F, Fut>(policy: Backoff, factory: F) -> Result<A, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
{
    run_retries(policy.n, factory, |_, _| true, |attempt| Some(policy.jittered(attempt))).await
}

/// Retries with exponential backoff while `retry_if(&error, attempt)` holds.
/// TS: `io.retryWithBackoff({ n, baseMs, while, ... })`.
///
/// The predicate runs before the delay, as in [`retry_while`].
pub async fn retry_with_backoff_while<A, E, F, Fut, P>(policy: Backoff, retry_if: P, factory: F) -> Result<A, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
    P: FnMut(&E, usize) -> bool,
{
    run_retries(policy.n, factory, retry_if, |attempt| Some(policy.jittered(attempt))).await
}

/// Runs each factory in order and returns the first `Ok`, or the last `Err` when all fail.
/// TS: `IO.firstSuccessOf(effects)`.
///
/// The factories run one after another, never at once; later ones run only after earlier ones
/// fail. The list is a [`NonEmptyVec`], so an empty list fails to compile; TS dies at run time.
///
/// Every factory in the list has one type. Mapping one closure over a list of inputs gives that
/// (first example). For different effects, box them (second example).
///
/// # Examples
///
/// ```
/// use functype_core::nev;
/// use functype_io::first_success_of;
///
/// async fn fetch(mirror: &'static str) -> Result<String, String> {
///     if mirror == "b" { Ok(format!("from {mirror}")) } else { Err(format!("{mirror} down")) }
/// }
///
/// # tokio::runtime::Runtime::new().unwrap().block_on(async {
/// let mirrors = nev!["a", "b", "c"];
/// let result = first_success_of(mirrors.map(|&m| move || fetch(m))).await;
/// assert_eq!(result, Ok("from b".to_string()));
///
/// // Different effects: box each factory and its future.
/// use functype_core::non_empty_vec::NonEmptyVec;
/// use functype_io::BoxIO;
///
/// async fn from_cache() -> Result<String, String> { Err("miss".into()) }
/// async fn from_db() -> Result<String, String> { Ok("row".into()) }
///
/// type Factory = Box<dyn FnOnce() -> BoxIO<'static, String, String> + Send>;
/// let sources: NonEmptyVec<Factory> = nev![
///     Box::new(|| Box::pin(from_cache()) as BoxIO<'static, String, String>) as Factory,
///     Box::new(|| Box::pin(from_db()) as BoxIO<'static, String, String>),
/// ];
/// assert_eq!(first_success_of(sources).await, Ok("row".to_string()));
/// # });
/// ```
pub async fn first_success_of<A, E, F, Fut>(factories: NonEmptyVec<F>) -> Result<A, E>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = Result<A, E>>,
{
    let mut factories = factories.into_iter();
    let first = factories.next().expect("a NonEmptyVec yields at least one item");
    let mut result = first().await;
    for factory in factories {
        if result.is_ok() {
            break;
        }
        result = factory().await;
    }
    result
}

async fn run_retries<A, E, F, Fut, P, D>(n: usize, mut factory: F, mut retry_if: P, mut delay: D) -> Result<A, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<A, E>>,
    P: FnMut(&E, usize) -> bool,
    D: FnMut(usize) -> Option<Duration>,
{
    let mut attempt = 1;
    loop {
        let error = match factory().await {
            Ok(a) => return Ok(a),
            Err(e) => e,
        };
        if attempt > n || !retry_if(&error, attempt) {
            return Err(error);
        }
        if let Some(d) = delay(attempt) {
            tokio::time::sleep(d).await;
        }
        attempt += 1;
    }
}

/// A random number in `[0, 1)`, from std's per-instance random hasher keys.
fn random_unit() -> f64 {
    let bits = RandomState::new().build_hasher().finish();
    (bits >> 11) as f64 / (1u64 << 53) as f64
}

#[cfg(test)]
mod tests {
    use super::*;
    use functype_core::nev;
    use std::cell::{Cell, RefCell};
    use tokio::time::Instant;

    async fn failing_until(calls: &Cell<usize>, ok_on: usize) -> Result<usize, String> {
        calls.set(calls.get() + 1);
        if calls.get() >= ok_on {
            Ok(calls.get())
        } else {
            Err(format!("fail {}", calls.get()))
        }
    }

    #[tokio::test]
    async fn retry_zero_runs_once() {
        let calls = Cell::new(0);
        let r = retry(0, || failing_until(&calls, 99)).await;
        assert_eq!(r, Err("fail 1".to_string()));
        assert_eq!(calls.get(), 1);
    }

    #[tokio::test]
    async fn retry_makes_n_plus_one_attempts_and_returns_last_error() {
        let calls = Cell::new(0);
        let r = retry(3, || failing_until(&calls, 99)).await;
        assert_eq!(r, Err("fail 4".to_string()));
        assert_eq!(calls.get(), 4);
    }

    #[tokio::test]
    async fn retry_stops_at_first_success() {
        let calls = Cell::new(0);
        let r = retry(5, || failing_until(&calls, 2)).await;
        assert_eq!(r, Ok(2));
        assert_eq!(calls.get(), 2);
    }

    #[tokio::test(start_paused = true)]
    async fn retry_with_delay_sleeps_before_each_retry() {
        let calls = Cell::new(0);
        let start = Instant::now();
        let r = retry_with_delay(2, Duration::from_millis(100), || failing_until(&calls, 99)).await;
        assert!(r.is_err());
        assert_eq!(calls.get(), 3);
        assert_eq!(start.elapsed(), Duration::from_millis(200));
    }

    #[tokio::test]
    async fn retry_while_passes_error_and_one_indexed_attempt() {
        let calls = Cell::new(0);
        let seen = RefCell::new(Vec::new());
        let r = retry_while(
            5,
            None,
            |e: &String, attempt| {
                seen.borrow_mut().push((e.clone(), attempt));
                attempt < 3
            },
            || failing_until(&calls, 99),
        )
        .await;
        assert_eq!(r, Err("fail 3".to_string()));
        assert_eq!(
            *seen.borrow(),
            vec![
                ("fail 1".to_string(), 1),
                ("fail 2".to_string(), 2),
                ("fail 3".to_string(), 3)
            ]
        );
    }

    #[tokio::test(start_paused = true)]
    async fn retry_while_false_returns_without_delay() {
        let calls = Cell::new(0);
        let start = Instant::now();
        let r = retry_while(
            3,
            Some(Duration::from_secs(5)),
            |_, _| false,
            || failing_until(&calls, 99),
        )
        .await;
        assert_eq!(r, Err("fail 1".to_string()));
        assert_eq!(start.elapsed(), Duration::ZERO);
    }

    #[test]
    fn backoff_defaults_match_ts() {
        let p = Backoff::new(3, Duration::from_millis(250));
        assert_eq!(p.max, Duration::from_secs(30));
        assert_eq!(p.factor, 2.0);
        assert!(p.jitter);
    }

    #[test]
    fn backoff_delay_grows_and_caps() {
        let p = Backoff::new(10, Duration::from_millis(100)).with_jitter(false);
        assert_eq!(p.delay_for(1), Duration::from_millis(100));
        assert_eq!(p.delay_for(2), Duration::from_millis(200));
        assert_eq!(p.delay_for(4), Duration::from_millis(800));
        assert_eq!(
            p.with_max(Duration::from_millis(300)).delay_for(4),
            Duration::from_millis(300)
        );
    }

    #[test]
    fn backoff_never_panics_on_extreme_input() {
        let p = Backoff::new(1, Duration::from_secs(1)).with_jitter(false);
        assert_eq!(p.delay_for(usize::MAX), p.max);
        assert_eq!(p.with_factor(f64::INFINITY).delay_for(2), p.max);
        assert_eq!(p.with_factor(-2.0).delay_for(2), Duration::ZERO);
        assert_eq!(p.with_factor(f64::NAN).delay_for(2), Duration::ZERO);
        let zero = Backoff::new(1, Duration::ZERO).with_factor(f64::INFINITY);
        assert_eq!(zero.delay_for(5), Duration::ZERO);
        assert_eq!(p.with_max(Duration::MAX).delay_for(usize::MAX), Duration::MAX);
    }

    #[test]
    fn jitter_stays_within_half_to_full() {
        let p = Backoff::new(1, Duration::from_millis(1000));
        for _ in 0..500 {
            let d = p.jittered(1);
            assert!(
                d >= Duration::from_millis(500) && d <= Duration::from_millis(1000),
                "{d:?}"
            );
        }
    }

    #[test]
    fn random_unit_varies_and_stays_in_range() {
        let samples: Vec<f64> = (0..100).map(|_| random_unit()).collect();
        assert!(samples.iter().all(|x| (0.0..1.0).contains(x)));
        assert!(samples.windows(2).any(|w| w[0] != w[1]));
    }

    #[tokio::test(start_paused = true)]
    async fn retry_with_backoff_sleeps_the_schedule() {
        let calls = Cell::new(0);
        let start = Instant::now();
        let policy = Backoff::new(3, Duration::from_millis(100)).with_jitter(false);
        let r = retry_with_backoff(policy, || failing_until(&calls, 99)).await;
        assert!(r.is_err());
        assert_eq!(calls.get(), 4);
        assert_eq!(start.elapsed(), Duration::from_millis(100 + 200 + 400));
    }

    #[tokio::test(start_paused = true)]
    async fn retry_with_backoff_while_checks_before_sleeping() {
        let calls = Cell::new(0);
        let start = Instant::now();
        let policy = Backoff::new(3, Duration::from_millis(100)).with_jitter(false);
        let r = retry_with_backoff_while(policy, |_, attempt| attempt < 2, || failing_until(&calls, 99)).await;
        assert_eq!(r, Err("fail 2".to_string()));
        assert_eq!(start.elapsed(), Duration::from_millis(100));
    }

    #[tokio::test]
    #[should_panic(expected = "not retried")]
    async fn retry_does_not_catch_panics() {
        let calls = Cell::new(0);
        let _ = retry(3, || async {
            calls.set(calls.get() + 1);
            if calls.get() == 1 {
                panic!("not retried");
            }
            Ok::<(), String>(())
        })
        .await;
    }

    #[tokio::test]
    async fn first_success_of_runs_in_order_and_stops() {
        let order = RefCell::new(Vec::new());
        let make = |name: &'static str, ok: bool| {
            let order = &order;
            move || async move {
                order.borrow_mut().push(name);
                if ok {
                    Ok(name)
                } else {
                    Err(name)
                }
            }
        };
        let r = first_success_of(nev![make("a", false), make("b", true), make("c", true)]).await;
        assert_eq!(r, Ok("b"));
        assert_eq!(*order.borrow(), vec!["a", "b"]);
    }

    #[tokio::test]
    async fn first_success_of_returns_last_error() {
        let make = |name: &'static str| move || async move { Err::<(), _>(name) };
        let r = first_success_of(nev![make("a"), make("b"), make("c")]).await;
        assert_eq!(r, Err("c"));
    }

    #[tokio::test]
    async fn retry_while_skips_the_predicate_once_n_is_spent() {
        let calls = Cell::new(0);
        let checks = Cell::new(0);
        let r = retry_while(
            2,
            None,
            |_, _| {
                checks.set(checks.get() + 1);
                true
            },
            || failing_until(&calls, 99),
        )
        .await;
        assert_eq!(r, Err("fail 3".to_string()));
        assert_eq!(calls.get(), 3);
        assert_eq!(checks.get(), 2);
    }

    #[tokio::test(start_paused = true)]
    async fn retry_with_backoff_jitter_stays_within_the_schedule() {
        let calls = Cell::new(0);
        let start = Instant::now();
        let policy = Backoff::new(3, Duration::from_millis(100));
        let r = retry_with_backoff(policy, || failing_until(&calls, 99)).await;
        assert!(r.is_err());
        assert_eq!(calls.get(), 4);
        let full = Duration::from_millis(100 + 200 + 400);
        let elapsed = start.elapsed();
        assert!(elapsed >= full / 2 && elapsed <= full, "{elapsed:?}");
    }

    #[tokio::test]
    async fn first_success_of_single_item() {
        let only = || async { Err::<(), _>("only") };
        assert_eq!(first_success_of(nev![only]).await, Err("only"));
    }

    #[test]
    fn helper_futures_are_send_when_their_inputs_are() {
        fn assert_send<T: Send>(_: &T) {}
        let factory = || async { Ok::<u32, String>(1) };
        assert_send(&retry(1, factory));
        assert_send(&retry_with_delay(1, Duration::ZERO, factory));
        assert_send(&retry_while(1, None, |_, _| true, factory));
        assert_send(&retry_with_backoff(Backoff::new(1, Duration::ZERO), factory));
        assert_send(&retry_with_backoff_while(
            Backoff::new(1, Duration::ZERO),
            |_, _| true,
            factory,
        ));
        assert_send(&first_success_of(nev![factory]));
    }

    #[test]
    fn delay_for_zero_is_base() {
        let p = Backoff::new(1, Duration::from_millis(100)).with_jitter(false);
        assert_eq!(p.delay_for(0), p.delay_for(1));
    }
}
