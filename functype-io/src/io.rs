use std::fmt;

use anyhow;
use functype_core::either::Either;
use functype_core::pure::Pure;

/// A lazy, composable IO effect type.
///
/// `IO<A>` represents a computation that, when executed, performs side effects
/// and produces a value of type `A` (or fails with an error).
///
/// Nothing executes until `.run()` is called — this gives referential transparency,
/// deferred execution, and composable effect descriptions.
///
/// # Design
///
/// - **One type parameter**: `IO<A>` keeps signatures clean. Errors are type-erased
///   via `anyhow::Error` and surfaced at `.run()` boundaries. For typed errors,
///   use `IO<Result<A, E>>` — opt-in, not mandatory.
/// - **`Send + 'static`**: Compatible with tokio and thread pools.
/// - **`FnOnce`**: Consumed exactly once.
///
/// # Examples
///
/// ```
/// use functype_io::IO;
///
/// let io = IO::succeed(42);
/// assert_eq!(io.run().unwrap(), 42);
///
/// let io = IO::effect(|| 1 + 2).map(|x| x * 10);
/// assert_eq!(io.run().unwrap(), 30);
/// ```
pub struct IO<A> {
    thunk: Box<dyn FnOnce() -> Result<A, anyhow::Error> + Send + 'static>,
}

impl<A: fmt::Debug> fmt::Debug for IO<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IO").finish_non_exhaustive()
    }
}

/// Alias for familiarity (ZIO convention).
pub type Task<A> = IO<A>;

// ============================================================
// Constructors
// ============================================================

impl<A: Send + 'static> IO<A> {
    /// Creates an IO that succeeds with the given value.
    pub fn succeed(a: A) -> IO<A> {
        IO {
            thunk: Box::new(move || Ok(a)),
        }
    }

    /// Creates an IO that fails with the given error.
    pub fn fail(e: impl Into<anyhow::Error> + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || Err(e.into())),
        }
    }

    /// Creates an IO from an infallible side effect.
    pub fn effect(f: impl FnOnce() -> A + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || Ok(f())),
        }
    }

    /// Creates an IO from a fallible side effect (primary constructor).
    pub fn effect_result(f: impl FnOnce() -> Result<A, anyhow::Error> + Send + 'static) -> IO<A> {
        IO { thunk: Box::new(f) }
    }

    /// Lifts a `Result` into an `IO`.
    pub fn from_result(result: Result<A, impl Into<anyhow::Error> + Send + 'static>) -> IO<A> {
        IO {
            thunk: Box::new(move || result.map_err(Into::into)),
        }
    }

    /// Lifts an `Option` into an `IO`, using the provided closure for the `None` case.
    pub fn from_option(option: Option<A>, on_none: impl FnOnce() -> anyhow::Error + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || option.ok_or_else(on_none)),
        }
    }

    /// Lifts an `Either` into an `IO`. `Left` becomes the error, `Right` becomes the value.
    pub fn from_either(either: Either<impl Into<anyhow::Error> + Send + 'static, A>) -> IO<A> {
        IO {
            thunk: Box::new(move || match either {
                Either::Left(e) => Err(e.into()),
                Either::Right(a) => Ok(a),
            }),
        }
    }
}

// ============================================================
// Execution
// ============================================================

impl<A> IO<A> {
    /// Consumes and executes this IO, returning the result.
    pub fn run(self) -> Result<A, anyhow::Error> {
        (self.thunk)()
    }

    /// Executes this IO, panicking on error.
    pub fn run_or_panic(self) -> A
    where
        A: fmt::Debug,
    {
        self.run().expect("IO::run_or_panic failed")
    }
}

// ============================================================
// Monadic combinators
// ============================================================

impl<A: Send + 'static> IO<A> {
    /// Transforms the success value.
    pub fn map<B: Send + 'static>(self, f: impl FnOnce(A) -> B + Send + 'static) -> IO<B> {
        IO {
            thunk: Box::new(move || (self.thunk)().map(f)),
        }
    }

    /// Chains a computation that depends on the success value.
    pub fn flat_map<B: Send + 'static>(self, f: impl FnOnce(A) -> IO<B> + Send + 'static) -> IO<B> {
        IO {
            thunk: Box::new(move || {
                let a = (self.thunk)()?;
                f(a).run()
            }),
        }
    }

    /// Alias for `flat_map` (for `fdo!` macro compatibility).
    pub fn and_then<B: Send + 'static>(self, f: impl FnOnce(A) -> IO<B> + Send + 'static) -> IO<B> {
        self.flat_map(f)
    }

    /// Combines two IOs into a tuple.
    pub fn zip<B: Send + 'static>(self, other: IO<B>) -> IO<(A, B)> {
        IO {
            thunk: Box::new(move || {
                let a = (self.thunk)()?;
                let b = (other.thunk)()?;
                Ok((a, b))
            }),
        }
    }

    /// Combines two IOs with a function.
    pub fn zip_with<B: Send + 'static, C: Send + 'static>(
        self,
        other: IO<B>,
        f: impl FnOnce(A, B) -> C + Send + 'static,
    ) -> IO<C> {
        IO {
            thunk: Box::new(move || {
                let a = (self.thunk)()?;
                let b = (other.thunk)()?;
                Ok(f(a, b))
            }),
        }
    }

    /// Sequences two IOs, discarding the first result (ZIO's `*>`).
    pub fn then<B: Send + 'static>(self, other: IO<B>) -> IO<B> {
        IO {
            thunk: Box::new(move || {
                let _a = (self.thunk)()?;
                (other.thunk)()
            }),
        }
    }

    /// Runs a side effect on the success value, returning the original value.
    pub fn tap(self, f: impl FnOnce(&A) + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || {
                let a = (self.thunk)()?;
                f(&a);
                Ok(a)
            }),
        }
    }
}

// ============================================================
// Error handling
// ============================================================

impl<A: Send + 'static> IO<A> {
    /// Transforms the error.
    pub fn map_error(self, f: impl FnOnce(anyhow::Error) -> anyhow::Error + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || (self.thunk)().map_err(f)),
        }
    }

    /// Recovers from an error by producing a new IO.
    pub fn catch(self, f: impl FnOnce(anyhow::Error) -> IO<A> + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || match (self.thunk)() {
                Ok(a) => Ok(a),
                Err(e) => f(e).run(),
            }),
        }
    }

    /// Falls back to another IO on error.
    pub fn or_else(self, other: IO<A>) -> IO<A> {
        IO {
            thunk: Box::new(move || match (self.thunk)() {
                Ok(a) => Ok(a),
                Err(_) => (other.thunk)(),
            }),
        }
    }

    /// Makes this IO infallible by wrapping the result in `Either`.
    /// Errors become `Left`, successes become `Right`.
    pub fn either(self) -> IO<Either<anyhow::Error, A>> {
        IO {
            thunk: Box::new(move || {
                Ok(match (self.thunk)() {
                    Ok(a) => Either::Right(a),
                    Err(e) => Either::Left(e),
                })
            }),
        }
    }

    /// Retries a factory function up to `n` times on failure.
    ///
    /// This is an associated function (not a method) because IO is `FnOnce` —
    /// the factory creates a fresh IO on each attempt.
    pub fn retry(factory: impl Fn() -> IO<A> + Send + 'static, n: usize) -> IO<A> {
        IO {
            thunk: Box::new(move || {
                let mut last_err = None;
                for _ in 0..=n {
                    match factory().run() {
                        Ok(a) => return Ok(a),
                        Err(e) => last_err = Some(e),
                    }
                }
                Err(last_err.unwrap())
            }),
        }
    }
}

// ============================================================
// Resource safety
// ============================================================

impl IO<()> {
    /// Acquires a resource, uses it, and guarantees release even on failure.
    ///
    /// - `acquire`: IO that produces the resource
    /// - `use_fn`: Function that uses the resource (receives a reference)
    /// - `release`: Cleanup function that always runs after `use_fn` (on both success and error)
    ///
    /// If `acquire` fails, neither `use_fn` nor `release` run.
    pub fn bracket<R: Send + 'static, B: Send + 'static>(
        acquire: IO<R>,
        use_fn: impl FnOnce(&R) -> IO<B> + Send + 'static,
        release: impl FnOnce(&R) + Send + 'static,
    ) -> IO<B> {
        IO {
            thunk: Box::new(move || {
                let resource = acquire.run()?;
                let result = use_fn(&resource).run();
                release(&resource);
                result
            }),
        }
    }
}

impl<A: Send + 'static> IO<A> {
    /// Guarantees that the finalizer runs after this IO, regardless of success or failure.
    pub fn ensuring(self, finalizer: impl FnOnce() + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || {
                let result = (self.thunk)();
                finalizer();
                result
            }),
        }
    }
}

// ============================================================
// Async interop
// ============================================================

impl<A: Send + 'static> IO<A> {
    /// Creates an IO from a future. Blocks on the current tokio runtime.
    ///
    /// Must be called from within a tokio runtime context. Uses `block_in_place`
    /// to avoid panicking when called from an async context (requires multi-thread runtime).
    pub fn from_future(future: impl std::future::Future<Output = Result<A, anyhow::Error>> + Send + 'static) -> IO<A> {
        IO {
            thunk: Box::new(move || {
                let handle = tokio::runtime::Handle::current();
                tokio::task::block_in_place(|| handle.block_on(future))
            }),
        }
    }

    /// Converts this IO into a future.
    pub async fn to_future(self) -> Result<A, anyhow::Error> {
        self.run()
    }
}

// ============================================================
// Pure trait
// ============================================================

impl<A: Send + 'static> Pure<A> for IO<A> {
    fn pure(a: A) -> Self {
        IO::succeed(a)
    }
}

// ============================================================
// Tests
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;

    // ===== Step 1: Core type + constructors + execution =====

    #[test]
    fn succeed_returns_value() {
        let io = IO::succeed(42);
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn succeed_with_string() {
        let io = IO::succeed("hello".to_string());
        assert_eq!(io.run().unwrap(), "hello");
    }

    #[test]
    fn fail_returns_error() {
        let io: IO<i32> = IO::fail(anyhow::anyhow!("boom"));
        let err = io.run().unwrap_err();
        assert_eq!(err.to_string(), "boom");
    }

    #[test]
    fn effect_captures_side_effect() {
        let counter = Arc::new(AtomicUsize::new(0));
        let c = counter.clone();
        let io = IO::effect(move || {
            c.fetch_add(1, Ordering::SeqCst);
            42
        });
        assert_eq!(counter.load(Ordering::SeqCst), 0, "effect should be lazy");
        assert_eq!(io.run().unwrap(), 42);
        assert_eq!(counter.load(Ordering::SeqCst), 1, "effect should have run");
    }

    #[test]
    fn laziness_verified() {
        let ran = Arc::new(AtomicBool::new(false));
        let r = ran.clone();
        let _io = IO::effect(move || {
            r.store(true, Ordering::SeqCst);
        });
        assert!(!ran.load(Ordering::SeqCst), "should not run until .run()");
    }

    #[test]
    fn effect_result_success() {
        let io = IO::effect_result(|| Ok(42));
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn effect_result_failure() {
        let io: IO<i32> = IO::effect_result(|| Err(anyhow::anyhow!("fail")));
        assert!(io.run().is_err());
    }

    #[test]
    fn from_result_ok() {
        let io = IO::from_result(Ok::<i32, anyhow::Error>(42));
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn from_result_err() {
        let io = IO::from_result(Err::<i32, _>(anyhow::anyhow!("nope")));
        assert!(io.run().is_err());
    }

    #[test]
    fn from_option_some() {
        let io = IO::from_option(Some(42), || anyhow::anyhow!("missing"));
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn from_option_none() {
        let io = IO::from_option(None::<i32>, || anyhow::anyhow!("missing"));
        let err = io.run().unwrap_err();
        assert_eq!(err.to_string(), "missing");
    }

    #[test]
    fn from_either_right() {
        let either: Either<anyhow::Error, i32> = Either::Right(42);
        let io = IO::from_either(either);
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn from_either_left() {
        let either: Either<anyhow::Error, i32> = Either::Left(anyhow::anyhow!("left error"));
        let io = IO::from_either(either);
        assert_eq!(io.run().unwrap_err().to_string(), "left error");
    }

    #[test]
    fn run_or_panic_success() {
        let io = IO::succeed(42);
        assert_eq!(io.run_or_panic(), 42);
    }

    #[test]
    #[should_panic(expected = "IO::run_or_panic failed")]
    fn run_or_panic_failure() {
        let io: IO<i32> = IO::fail(anyhow::anyhow!("boom"));
        io.run_or_panic();
    }

    // ===== Step 2: Monadic combinators =====

    #[test]
    fn map_transforms_value() {
        let io = IO::succeed(21).map(|x| x * 2);
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn map_preserves_error() {
        let io: IO<i32> = IO::<i32>::fail(anyhow::anyhow!("err")).map(|x| x * 2);
        assert_eq!(io.run().unwrap_err().to_string(), "err");
    }

    #[test]
    fn flat_map_chains() {
        let io = IO::succeed(10).flat_map(|x| IO::succeed(x + 5));
        assert_eq!(io.run().unwrap(), 15);
    }

    #[test]
    fn flat_map_short_circuits_on_first_error() {
        let ran = Arc::new(AtomicBool::new(false));
        let r = ran.clone();
        let io: IO<i32> = IO::fail(anyhow::anyhow!("first")).flat_map(move |x| {
            r.store(true, Ordering::SeqCst);
            IO::succeed(x)
        });
        assert!(io.run().is_err());
        assert!(!ran.load(Ordering::SeqCst));
    }

    #[test]
    fn flat_map_short_circuits_on_second_error() {
        let io = IO::succeed(10).flat_map(|_| IO::<i32>::fail(anyhow::anyhow!("second")));
        assert_eq!(io.run().unwrap_err().to_string(), "second");
    }

    #[test]
    fn and_then_is_flat_map_alias() {
        let io = IO::succeed(10).and_then(|x| IO::succeed(x + 1));
        assert_eq!(io.run().unwrap(), 11);
    }

    #[test]
    fn zip_combines_two_ios() {
        let io = IO::succeed(1).zip(IO::succeed(2));
        assert_eq!(io.run().unwrap(), (1, 2));
    }

    #[test]
    fn zip_short_circuits_first() {
        let io = IO::<i32>::fail(anyhow::anyhow!("first")).zip(IO::succeed(2));
        assert!(io.run().is_err());
    }

    #[test]
    fn zip_short_circuits_second() {
        let io = IO::succeed(1).zip(IO::<i32>::fail(anyhow::anyhow!("second")));
        assert!(io.run().is_err());
    }

    #[test]
    fn zip_with_combines_with_function() {
        let io = IO::succeed(10).zip_with(IO::succeed(20), |a, b| a + b);
        assert_eq!(io.run().unwrap(), 30);
    }

    #[test]
    fn then_discards_first() {
        let io = IO::succeed(1).then(IO::succeed(2));
        assert_eq!(io.run().unwrap(), 2);
    }

    #[test]
    fn then_short_circuits_on_first_error() {
        let io = IO::<i32>::fail(anyhow::anyhow!("err")).then(IO::succeed(2));
        assert!(io.run().is_err());
    }

    #[test]
    fn tap_runs_side_effect() {
        let seen = Arc::new(AtomicUsize::new(0));
        let s = seen.clone();
        let io = IO::succeed(42).tap(move |x| {
            s.store(*x as usize, Ordering::SeqCst);
        });
        assert_eq!(io.run().unwrap(), 42);
        assert_eq!(seen.load(Ordering::SeqCst), 42);
    }

    #[test]
    fn tap_does_not_run_on_error() {
        let ran = Arc::new(AtomicBool::new(false));
        let r = ran.clone();
        let io: IO<i32> = IO::fail(anyhow::anyhow!("err")).tap(move |_| {
            r.store(true, Ordering::SeqCst);
        });
        assert!(io.run().is_err());
        assert!(!ran.load(Ordering::SeqCst));
    }

    // Monad laws

    #[test]
    fn monad_left_identity() {
        // pure(a).flat_map(f) == f(a)
        let f = |x: i32| IO::succeed(x + 1);
        let left = IO::succeed(10).flat_map(f);
        let right = f(10);
        assert_eq!(left.run().unwrap(), right.run().unwrap());
    }

    #[test]
    fn monad_right_identity() {
        // m.flat_map(pure) == m
        let m = IO::succeed(42);
        let result = IO::succeed(42).flat_map(IO::succeed);
        assert_eq!(m.run().unwrap(), result.run().unwrap());
    }

    #[test]
    fn monad_associativity() {
        // (m.flat_map(f)).flat_map(g) == m.flat_map(|x| f(x).flat_map(g))
        let f = |x: i32| IO::succeed(x + 1);
        let g = |x: i32| IO::succeed(x * 2);

        let left = IO::succeed(10).flat_map(f).flat_map(g);
        let f2 = |x: i32| IO::succeed(x + 1);
        let g2 = |x: i32| IO::succeed(x * 2);
        let right = IO::succeed(10).flat_map(move |x| f2(x).flat_map(g2));
        assert_eq!(left.run().unwrap(), right.run().unwrap());
    }

    // ===== Step 3: Error handling =====

    #[test]
    fn map_error_transforms_error() {
        let io: IO<i32> = IO::fail(anyhow::anyhow!("original")).map_error(|_| anyhow::anyhow!("transformed"));
        assert_eq!(io.run().unwrap_err().to_string(), "transformed");
    }

    #[test]
    fn map_error_preserves_success() {
        let io = IO::succeed(42).map_error(|_| anyhow::anyhow!("nope"));
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn catch_recovers_from_error() {
        let io: IO<i32> = IO::fail(anyhow::anyhow!("err")).catch(|_| IO::succeed(99));
        assert_eq!(io.run().unwrap(), 99);
    }

    #[test]
    fn catch_preserves_success() {
        let io = IO::succeed(42).catch(|_| IO::succeed(99));
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn or_else_falls_back() {
        let io: IO<i32> = IO::fail(anyhow::anyhow!("err")).or_else(IO::succeed(99));
        assert_eq!(io.run().unwrap(), 99);
    }

    #[test]
    fn or_else_preserves_success() {
        let io = IO::succeed(42).or_else(IO::succeed(99));
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn either_wraps_success() {
        let io = IO::succeed(42).either();
        let result = io.run().unwrap();
        assert!(result.is_right());
        assert_eq!(result.right_value(), Some(&42));
    }

    #[test]
    fn either_wraps_error() {
        let io: IO<i32> = IO::fail(anyhow::anyhow!("err"));
        let result = io.either().run().unwrap();
        assert!(result.is_left());
        let msg = result.fold(|e| e.to_string(), |_| String::new());
        assert_eq!(msg, "err");
    }

    #[test]
    fn retry_succeeds_on_nth_attempt() {
        let counter = Arc::new(AtomicUsize::new(0));
        let c = counter.clone();
        let io = IO::retry(
            move || {
                let count = c.fetch_add(1, Ordering::SeqCst);
                if count < 2 {
                    IO::fail(anyhow::anyhow!("not yet"))
                } else {
                    IO::succeed(42)
                }
            },
            3,
        );
        assert_eq!(io.run().unwrap(), 42);
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn retry_exhausts_attempts() {
        let counter = Arc::new(AtomicUsize::new(0));
        let c = counter.clone();
        let io: IO<i32> = IO::retry(
            move || {
                c.fetch_add(1, Ordering::SeqCst);
                IO::fail(anyhow::anyhow!("always fails"))
            },
            2,
        );
        assert!(io.run().is_err());
        assert_eq!(counter.load(Ordering::SeqCst), 3); // initial + 2 retries
    }

    // ===== Step 4: Resource safety =====

    #[test]
    fn bracket_runs_all_three() {
        let order = Arc::new(std::sync::Mutex::new(Vec::new()));
        let o1 = order.clone();
        let o2 = order.clone();
        let o3 = order.clone();

        let io = IO::bracket(
            IO::effect(move || {
                o1.lock().unwrap().push("acquire");
                "resource"
            }),
            move |r| {
                o2.lock().unwrap().push("use");
                IO::succeed(r.len())
            },
            move |_r| {
                o3.lock().unwrap().push("release");
            },
        );

        assert_eq!(io.run().unwrap(), 8); // "resource".len()
        assert_eq!(*order.lock().unwrap(), vec!["acquire", "use", "release"]);
    }

    #[test]
    fn bracket_releases_on_use_error() {
        let released = Arc::new(AtomicBool::new(false));
        let r = released.clone();

        let io = IO::bracket(
            IO::succeed(42),
            |_| IO::<i32>::fail(anyhow::anyhow!("use failed")),
            move |_| {
                r.store(true, Ordering::SeqCst);
            },
        );

        assert!(io.run().is_err());
        assert!(released.load(Ordering::SeqCst), "release should run on use error");
    }

    #[test]
    fn bracket_does_not_release_on_acquire_error() {
        let released = Arc::new(AtomicBool::new(false));
        let r = released.clone();

        let io = IO::bracket(
            IO::<i32>::fail(anyhow::anyhow!("acquire failed")),
            |_| IO::succeed(0),
            move |_| {
                r.store(true, Ordering::SeqCst);
            },
        );

        assert!(io.run().is_err());
        assert!(
            !released.load(Ordering::SeqCst),
            "release should NOT run on acquire error"
        );
    }

    #[test]
    fn ensuring_runs_on_success() {
        let ran = Arc::new(AtomicBool::new(false));
        let r = ran.clone();
        let io = IO::succeed(42).ensuring(move || {
            r.store(true, Ordering::SeqCst);
        });
        assert_eq!(io.run().unwrap(), 42);
        assert!(ran.load(Ordering::SeqCst));
    }

    #[test]
    fn ensuring_runs_on_error() {
        let ran = Arc::new(AtomicBool::new(false));
        let r = ran.clone();
        let io: IO<i32> = IO::fail(anyhow::anyhow!("err")).ensuring(move || {
            r.store(true, Ordering::SeqCst);
        });
        assert!(io.run().is_err());
        assert!(ran.load(Ordering::SeqCst));
    }

    #[test]
    fn ensuring_preserves_result() {
        let io = IO::succeed(42).ensuring(|| {});
        assert_eq!(io.run().unwrap(), 42);

        let io: IO<i32> = IO::fail(anyhow::anyhow!("err")).ensuring(|| {});
        assert_eq!(io.run().unwrap_err().to_string(), "err");
    }

    // ===== Step 5: Async interop =====

    #[tokio::test(flavor = "multi_thread")]
    async fn from_future_success() {
        let io = IO::from_future(async { Ok(42) });
        assert_eq!(io.run().unwrap(), 42);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn from_future_error() {
        let io: IO<i32> = IO::from_future(async { Err(anyhow::anyhow!("async fail")) });
        assert_eq!(io.run().unwrap_err().to_string(), "async fail");
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn to_future_success() {
        let io = IO::succeed(42);
        let result = io.to_future().await;
        assert_eq!(result.unwrap(), 42);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn to_future_error() {
        let io: IO<i32> = IO::fail(anyhow::anyhow!("err"));
        let result = io.to_future().await;
        assert_eq!(result.unwrap_err().to_string(), "err");
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn future_roundtrip() {
        let io = IO::succeed(42);
        let future = io.to_future();
        let io2 = IO::from_future(future);
        assert_eq!(io2.run().unwrap(), 42);
    }

    // ===== Step 6: Pure trait + fdo! verification =====

    #[test]
    fn pure_creates_succeed() {
        let io: IO<i32> = Pure::pure(42);
        assert_eq!(io.run().unwrap(), 42);
    }

    #[test]
    fn fdo_single_bind() {
        use functype_core::fdo;

        let result = fdo! {
            x <- IO::succeed(42);
            yield x
        };
        assert_eq!(result.run().unwrap(), 42);
    }

    #[test]
    fn fdo_multi_bind() {
        use functype_core::fdo;

        let result = fdo! {
            x <- IO::succeed(10);
            y <- IO::succeed(20);
            yield x + y
        };
        assert_eq!(result.run().unwrap(), 30);
    }

    #[test]
    fn fdo_short_circuits_on_fail() {
        use functype_core::fdo;

        let ran = Arc::new(AtomicBool::new(false));
        let r = ran.clone();
        let result: IO<i32> = {
            let r2 = r;
            fdo! {
                _x <- IO::<i32>::fail(anyhow::anyhow!("fail"));
                y <- IO::effect(move || { r2.store(true, Ordering::SeqCst); 99 });
                yield y
            }
        };
        assert!(result.run().is_err());
        assert!(!ran.load(Ordering::SeqCst));
    }

    #[test]
    fn fdo_let_binding() {
        use functype_core::fdo;

        let result = fdo! {
            x <- IO::succeed(10);
            let doubled = x * 2;
            y <- IO::succeed(3);
            yield doubled + y
        };
        assert_eq!(result.run().unwrap(), 23);
    }

    #[test]
    fn fdo_nested() {
        use functype_core::fdo;

        let result = fdo! {
            x <- IO::succeed(10);
            y <- fdo! {
                a <- IO::succeed(20);
                yield a + 1
            };
            yield x + y
        };
        assert_eq!(result.run().unwrap(), 31);
    }

    #[test]
    fn fdo_realistic_pipeline() {
        use functype_core::fdo;

        fn parse_int(s: &str) -> IO<i32> {
            match s.parse::<i32>() {
                Ok(n) => IO::succeed(n),
                Err(e) => IO::fail(anyhow::anyhow!("parse error: {}", e)),
            }
        }

        fn safe_div(a: i32, b: i32) -> IO<i32> {
            if b == 0 {
                IO::fail(anyhow::anyhow!("division by zero"))
            } else {
                IO::succeed(a / b)
            }
        }

        let result = fdo! {
            x <- parse_int("100");
            y <- parse_int("5");
            z <- safe_div(x, y);
            yield z + 1
        };
        assert_eq!(result.run().unwrap(), 21);

        let result = fdo! {
            x <- parse_int("100");
            y <- parse_int("0");
            z <- safe_div(x, y);
            yield z + 1
        };
        assert_eq!(result.run().unwrap_err().to_string(), "division by zero");
    }

    // ===== Step 8: Debug + Task alias =====

    #[test]
    fn debug_impl() {
        let io = IO::succeed(42);
        let debug_str = format!("{:?}", io);
        assert!(debug_str.contains("IO"));
    }

    #[test]
    fn task_alias() {
        let task: Task<i32> = IO::succeed(42);
        assert_eq!(task.run().unwrap(), 42);
    }
}
