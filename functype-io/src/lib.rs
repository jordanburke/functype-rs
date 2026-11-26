//! functype-io: effect helpers for code translated from TS functype's `IO`.
//!
//! TS `IO<R, E, A>` maps to a plain `async fn -> Result<A, E>`. Rust futures are already lazy,
//! so this crate has no `IO` type. It ships only what Rust lacks:
//!
//! - [`Exit`] and [`run_exit`]: report success, failure, a panic, or cancellation as a value.
//! - Retry policies with TS defaults: [`retry`], [`retry_with_delay`], [`retry_while`],
//!   [`retry_with_backoff`], [`retry_with_backoff_while`], [`first_success_of`].
//! - Bounded repeats: [`repeat_until`], [`repeat_while`].
//! - [`BoxIO`]: a boxed future, for storing effects or returning them from trait objects.
//!
//! Every helper takes a factory (a closure that builds a fresh future), always as the last
//! argument, because a Rust future runs only once.
//!
//! The retry and repeat helpers act on `Err` only. A panic is not retried; it unwinds through
//! them as it would through `.await`. TS recovers defects too, so a TS step that throws and is
//! expected to be recovered or retried must return `Err` in Rust. Only [`run_exit`] catches a
//! panic, and reports it as [`Exit::Die`].
//!
//! Delays use `tokio::time::sleep`, so they need a Tokio runtime with time enabled.
//!
//! See `docs/LIB_SPEC_TS-to-Rust-mapping.md` in the repository for the full TS→Rust mapping.
//!
//! # Examples
//!
//! ```
//! use functype_io::{retry_with_backoff, Backoff};
//! use std::time::Duration;
//!
//! #[derive(Debug, PartialEq)]
//! enum AppError { Network }
//!
//! // TS: const getUser = (id: number): IO<never, AppError, string> => ...
//! async fn get_user(id: u32) -> Result<String, AppError> {
//!     if id == 1 { Ok("ann".into()) } else { Err(AppError::Network) }
//! }
//!
//! # tokio::runtime::Runtime::new().unwrap().block_on(async {
//! // TS: getUser(1).retryWithBackoff({ n: 3, baseMs: 250 })
//! let policy = Backoff::new(3, Duration::from_millis(250));
//! let user = retry_with_backoff(policy, || get_user(1)).await;
//! assert_eq!(user, Ok("ann".to_string()));
//! # });
//! ```

use std::future::Future;
use std::pin::Pin;

mod exit;
mod repeat;
mod retry;
mod run_exit;

pub use exit::Exit;
pub use repeat::{repeat_until, repeat_while, RepeatError, RepeatExhausted};
pub use retry::{
    first_success_of, retry, retry_while, retry_with_backoff, retry_with_backoff_while, retry_with_delay, Backoff,
};
pub use run_exit::run_exit;

/// A boxed, `Send` future returning `Result<A, E>`.
///
/// Use it where one concrete type is needed: a struct field, a `Vec` of effects, or a trait
/// method returning an effect. Elsewhere, write `async fn -> Result<A, E>`.
///
/// # Examples
///
/// ```
/// use functype_io::BoxIO;
///
/// fn load(id: u32) -> BoxIO<'static, String, String> {
///     Box::pin(async move { Ok(format!("item {id}")) })
/// }
///
/// let effects: Vec<BoxIO<'static, String, String>> = vec![load(1), load(2)];
/// assert_eq!(effects.len(), 2);
/// ```
pub type BoxIO<'a, A, E> = Pin<Box<dyn Future<Output = Result<A, E>> + Send + 'a>>;

/// The helpers, for `use functype_io::prelude::*`.
pub mod prelude {
    pub use crate::{
        first_success_of, repeat_until, repeat_while, retry, retry_while, retry_with_backoff, retry_with_backoff_while,
        retry_with_delay, run_exit, Backoff, BoxIO, Exit, RepeatError, RepeatExhausted,
    };
}
