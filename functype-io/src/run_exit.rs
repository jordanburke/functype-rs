use std::any::Any;
use std::future::{poll_fn, Future};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::{pin, Pin};
use std::task::{Context, Poll};

use functype_core::try_type::TryError;
use pin_project_lite::pin_project;

use crate::exit::Exit;

/// Runs a future to an [`Exit`], reporting panics and cancellation as values.
/// TS: `io.runExit({ signal })`.
///
/// - When `cancelled` is already done, `fut` is never polled and the result is
///   `Exit::Interrupted`, as in TS, where a pre-aborted signal stops the first step.
/// - When `cancelled` finishes while `fut` is pending, `fut` is dropped and the result is
///   `Exit::Interrupted`.
/// - `Err(e)` gives `Exit::Failure(e)`, or `Exit::Interrupted` when `cancelled` is done by then.
/// - `Ok(a)` gives `Exit::Success(a)`. A panic inside `fut` gives `Exit::Die`, even after
///   cancellation.
///
/// After the first poll, `fut` is polled before `cancelled` on every wake-up, so a result that is
/// ready on the same wake-up as the cancel is kept. Rust sees cancellation only between polls:
/// code between two `.await`s runs on to the next one. TS checks before every step, so a TS
/// `io.map(f)` aborted mid-run reports `Interrupted` where the Rust `async` block may finish with
/// `Success`.
///
/// `cancelled` is any future that finishes when the work should stop: for example
/// `token.cancelled()` from `tokio_util::sync::CancellationToken`, a `oneshot` receiver, or
/// `tokio::time::sleep(d)`. TS `runExit()` with no signal maps to `std::future::pending()`.
///
/// Panic capture uses `catch_unwind`, so it cannot catch anything under `panic = "abort"`.
///
/// # Examples
///
/// ```
/// use functype_io::{run_exit, Exit};
/// use std::future::{pending, ready};
///
/// # tokio::runtime::Runtime::new().unwrap().block_on(async {
/// let exit = run_exit(async { Ok::<_, String>(42) }, pending()).await;
/// assert_eq!(exit.ok(), Some(42));
///
/// let exit = run_exit(async { Err::<i32, _>("boom".to_string()) }, pending()).await;
/// assert!(exit.is_failure());
///
/// // Cancelled before the effect can finish.
/// let exit = run_exit(pending::<Result<i32, String>>(), ready(())).await;
/// assert!(exit.is_interrupted());
/// # });
/// ```
pub async fn run_exit<A, E, Fut, C>(fut: Fut, cancelled: C) -> Exit<E, A>
where
    Fut: Future<Output = Result<A, E>>,
    C: Future<Output = ()>,
{
    let mut fut = pin!(CatchUnwind { inner: fut });
    let mut cancelled = pin!(cancelled);
    let mut started = false;
    poll_fn(|cx| {
        if !started {
            started = true;
            if cancelled.as_mut().poll(cx).is_ready() {
                return Poll::Ready(Exit::Interrupted);
            }
        }
        poll_once(fut.as_mut(), cancelled.as_mut(), cx)
    })
    .await
}

fn poll_once<A, E, Fut, C>(
    fut: Pin<&mut CatchUnwind<Fut>>,
    cancelled: Pin<&mut C>,
    cx: &mut Context<'_>,
) -> Poll<Exit<E, A>>
where
    Fut: Future<Output = Result<A, E>>,
    C: Future<Output = ()>,
{
    let mut cancelled = cancelled;
    match fut.poll(cx) {
        Poll::Ready(Ok(Ok(a))) => Poll::Ready(Exit::Success(a)),
        Poll::Ready(Ok(Err(e))) => match cancelled.as_mut().poll(cx) {
            Poll::Ready(()) => Poll::Ready(Exit::Interrupted),
            Poll::Pending => Poll::Ready(Exit::Failure(e)),
        },
        Poll::Ready(Err(payload)) => Poll::Ready(Exit::Die(TryError::from_panic(payload))),
        Poll::Pending => match cancelled.as_mut().poll(cx) {
            Poll::Ready(()) => Poll::Ready(Exit::Interrupted),
            Poll::Pending => Poll::Pending,
        },
    }
}

pin_project! {
    /// Polls `inner`, turning a panic during a poll into `Err(payload)`.
    /// After a panic it must not be polled again; `run_exit` returns at once.
    struct CatchUnwind<F> {
        #[pin]
        inner: F,
    }
}

impl<F: Future> Future for CatchUnwind<F> {
    type Output = Result<F::Output, Box<dyn Any + Send>>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let inner = self.project().inner;
        match catch_unwind(AssertUnwindSafe(|| inner.poll(cx))) {
            Ok(Poll::Pending) => Poll::Pending,
            Ok(Poll::Ready(output)) => Poll::Ready(Ok(output)),
            Err(payload) => Poll::Ready(Err(payload)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::future::{pending, ready};
    use std::time::Duration;
    use tokio::sync::oneshot;

    #[tokio::test]
    async fn success() {
        let exit = run_exit(async { Ok::<_, String>(1) }, pending()).await;
        assert_eq!(exit.ok(), Some(1));
    }

    #[tokio::test]
    async fn failure() {
        let exit = run_exit(async { Err::<i32, _>("e".to_string()) }, pending()).await;
        assert_eq!(exit.err(), Some("e".to_string()));
    }

    #[tokio::test]
    async fn panic_becomes_die() {
        let exit = run_exit(
            async {
                if true {
                    panic!("kaboom");
                }
                Ok::<i32, String>(1)
            },
            pending(),
        )
        .await;
        match exit {
            Exit::Die(d) => assert_eq!(d.message(), "kaboom"),
            other => panic!("expected Die, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn panic_after_an_await_becomes_die() {
        let exit = run_exit(
            async {
                tokio::task::yield_now().await;
                if true {
                    panic!("later");
                }
                Ok::<i32, String>(1)
            },
            pending(),
        )
        .await;
        assert!(exit.is_die());
    }

    #[tokio::test(start_paused = true)]
    async fn cancel_while_pending_interrupts_and_drops_the_effect() {
        let (tx, rx) = oneshot::channel::<()>();
        let effect = async move {
            tokio::time::sleep(Duration::from_secs(60)).await;
            let _ = tx.send(());
            Ok::<i32, String>(1)
        };
        let exit = run_exit(effect, tokio::time::sleep(Duration::from_secs(1))).await;
        assert!(exit.is_interrupted());
        // The effect was dropped before it could send.
        assert!(rx.await.is_err());
    }

    /// A cancel future that finishes once the effect fires `tx`.
    async fn cancel_on(rx: oneshot::Receiver<()>) {
        let _ = rx.await;
    }

    #[tokio::test]
    async fn pre_cancelled_never_polls_the_effect() {
        let ran = Cell::new(false);
        let exit = run_exit(
            async {
                ran.set(true);
                Ok::<_, String>(7)
            },
            ready(()),
        )
        .await;
        assert!(exit.is_interrupted());
        assert!(!ran.get());
    }

    #[tokio::test]
    async fn pre_cancelled_effect_that_would_panic_is_interrupted() {
        let exit = run_exit(
            async {
                if true {
                    panic!("never runs");
                }
                Ok::<i32, String>(1)
            },
            ready(()),
        )
        .await;
        assert!(exit.is_interrupted());
    }

    #[tokio::test]
    async fn success_on_the_same_poll_as_the_cancel_is_kept() {
        let (tx, rx) = oneshot::channel();
        let exit = run_exit(
            async move {
                let _ = tx.send(());
                Ok::<_, String>(7)
            },
            cancel_on(rx),
        )
        .await;
        assert_eq!(exit.ok(), Some(7));
    }

    #[tokio::test]
    async fn failure_after_cancel_is_interrupted() {
        let (tx, rx) = oneshot::channel();
        let exit = run_exit(
            async move {
                let _ = tx.send(());
                Err::<i32, _>("late".to_string())
            },
            cancel_on(rx),
        )
        .await;
        assert!(exit.is_interrupted());
    }

    #[tokio::test]
    async fn defect_after_cancel_stays_die() {
        let (tx, rx) = oneshot::channel();
        let exit = run_exit(
            async move {
                let _ = tx.send(());
                if true {
                    panic!("still a defect");
                }
                Ok::<i32, String>(1)
            },
            cancel_on(rx),
        )
        .await;
        assert!(exit.is_die());
    }

    #[test]
    fn run_exit_future_is_send_when_its_inputs_are() {
        fn assert_send<T: Send>(_: &T) {}
        let f = run_exit(async { Ok::<_, String>(1) }, pending::<()>());
        assert_send(&f);
    }
}
