# functype-io

Effect helpers for async Rust, shaped for code translated from TS [functype](https://functype.org/)'s `IO`.

Part of the [functype](https://github.com/jordanburke/functype-rs) library.

TS `IO<R, E, A>` maps to a plain `async fn -> Result<A, E>`. Rust futures are already lazy, so this crate has no `IO` type. It ships only what Rust lacks:

- **`Exit<E, A>` and `run_exit(fut, cancelled)`**: report success, failure, a panic (`Die`), or cancellation (`Interrupted`) as a value.
- **Retry policies with TS defaults**: `retry`, `retry_with_delay`, `retry_while`, `retry_with_backoff` (`Backoff::new` sets a 30 s cap, factor 2 and jitter on), `retry_with_backoff_while`, `first_success_of`.
- **Bounded repeats**: `repeat_until`, `repeat_while`, failing with `RepeatError::Exhausted` at the bound.
- **`BoxIO<'a, A, E>`**: a boxed `Send` future, for struct fields, lists of effects, and trait methods.

Every helper takes a factory (a closure that builds a fresh future), always as the last argument, because a Rust future runs once.

## Usage

```toml
[dependencies]
functype-io = { git = "https://github.com/jordanburke/functype-rs" }
```

```rust
use functype_io::{retry_with_backoff, run_exit, Backoff, Exit};
use std::time::Duration;

// TS: getUser(id).retryWithBackoff({ n: 3, baseMs: 250 })
let user = retry_with_backoff(Backoff::new(3, Duration::from_millis(250)), || get_user(id)).await;

// TS: getUser(id).runExit({ signal })
match run_exit(get_user(id), token.cancelled()).await {
    Exit::Success(user) => println!("{user}"),
    Exit::Failure(e) => eprintln!("failed: {e}"),
    Exit::Die(defect) => eprintln!("panicked: {}", defect.message()),
    Exit::Interrupted => eprintln!("cancelled"),
}
```

## Panics are not errors

The retry and repeat helpers act on `Err` only, and a panic unwinds through them as it would through `.await`. TS recovers defects too, so a TS step that throws and is expected to be retried must return `Err` in Rust. Only `run_exit` catches a panic, and it cannot under `panic = "abort"`.

Delays use `tokio::time::sleep`, so they need a Tokio runtime with time enabled.

See [`docs/LIB_SPEC_TS-to-Rust-mapping.md`](../docs/LIB_SPEC_TS-to-Rust-mapping.md) for the full TS→Rust mapping.
