# functype

Scala-inspired functional programming library for Rust.

Brings the ergonomics of Scala's type system — `Either`, `Validated`, do-notation — to Rust, without fighting the borrow checker. It is also the Rust side of [functype](https://functype.org/) for TypeScript: [`docs/LIB_SPEC_TS-to-Rust-mapping.md`](docs/LIB_SPEC_TS-to-Rust-mapping.md) maps TS functype code onto Rust.

```rust
use functype::prelude::*;
use functype_core::fdo;

let result: Either<&str, i32> = fdo! {
    x <- Either::<&str, i32>::right(10);
    y <- Either::<&str, i32>::right(20);
    yield x + y
};
assert_eq!(result, Either::Right(30));
```

## Crates

| Crate | Description |
|-------|-------------|
| [`functype`](functype/) | Umbrella crate — re-exports everything |
| [`functype-core`](functype-core/) | Core types: Either, Validated, Try, NonEmptyVec, persistent collections, fdo! macro |
| [`functype-io`](functype-io/) | Effect helpers for async Rust: `Exit`, `run_exit`, retry/repeat policies with TS functype defaults |

## Core Types

### Either\<L, R\>

Right-biased disjoint union. Short-circuits on `Left`.

```rust
use functype::prelude::*;
use functype_core::fdo;

let result: Either<&str, i32> = fdo! {
    x <- Either::<&str, i32>::right(10);
    y <- Either::<&str, i32>::right(20);
    yield x + y
};
assert_eq!(result, Either::Right(30));
```

Full API: `map`, `flat_map`, `bimap`, `fold`, `swap`, `filter_or_else`, `ap`, `zip`, conversions to/from `Result` and `Option`.

### Validated\<E, A\>

Applicative validation that **accumulates all errors** instead of short-circuiting. Errors are collected in `NonEmptyVec<E>` — guaranteed non-empty at the type level.

```rust
use functype::prelude::*;

fn validate_name(s: &str) -> Validated<String, String> {
    if s.is_empty() { Validated::invalid("name required".into()) }
    else { Validated::valid(s.into()) }
}

fn validate_age(n: i32) -> Validated<String, i32> {
    if n < 0 { Validated::invalid("age must be positive".into()) }
    else { Validated::valid(n) }
}

let result = validate_name("").zip(&validate_age(-1));
// Both errors collected, not just the first
assert!(result.is_invalid());
```

### Effects (functype-io)

TS functype's `IO<R, E, A>` maps to a plain `async fn -> Result<A, E>`. Rust futures are already lazy, so there is no `IO` type. `functype-io` ships only what Rust lacks. Every helper takes a factory closure, last, because a future runs once.

```rust
use functype::functype_io::{retry_with_backoff, Backoff};
use std::time::Duration;

// TS: getUser(id).retryWithBackoff({ n: 3, baseMs: 250 })
let user = retry_with_backoff(Backoff::new(3, Duration::from_millis(250)), || get_user(id)).await;
```

| TS | Rust |
|----|------|
| `io.retry(n)` | `retry(n, factory)` |
| `io.retryWithDelay(n, ms)` | `retry_with_delay(n, delay, factory)` |
| `io.retryWhile({ n, while, delayMs })` | `retry_while(n, delay, retry_if, factory)` |
| `io.retryWithBackoff({ n, baseMs, ... })` | `retry_with_backoff(Backoff::new(n, base), factory)`, or `retry_with_backoff_while` |
| `io.repeatUntil(done, { max, delayMs })` | `repeat_until(max, delay, done, factory)` → `Err(RepeatError::Exhausted)` at the bound |
| `io.repeatWhile(cont, { max, delayMs })` | `repeat_while(max, delay, keep_going, factory)` |
| `IO.firstSuccessOf(effects)` | `first_success_of(nev![...])` |
| `io.runExit({ signal })` | `run_exit(fut, token.cancelled()).await` → `Exit<E, A>` |
| a stored or `dyn` effect | `BoxIO<'a, A, E>` |

The retry and repeat helpers act on `Err` only; a panic unwinds through them. Only `run_exit` catches a panic, as `Exit::Die`.

### fdo! Macro

Scala/Haskell-style do-notation. Works with any type that has `and_then` and `map`: `Option`, `Result`, `Either`, `Validated`.

```rust
use functype_core::fdo;

// Option
let result: Option<i32> = fdo! {
    x <- Some(1);
    y <- Some(2);
    yield x + y          // Some(3)
};

// Result
let result: Result<i32, &str> = fdo! {
    x <- Ok(10);
    y <- Ok(20);
    yield x + y          // Ok(30)
};

// Let bindings and guards
let result: Option<i32> = fdo! {
    x <- Some(42);
    let doubled = x * 2;
    when doubled > 0;     // short-circuit to None if false
    yield doubled
};
```

### Try

Captures panics as values, inspired by Scala's `Try`.

```rust
use functype::prelude::*;

let result = try_catch(|| {
    "42".parse::<i32>().unwrap()
});
assert!(result.is_success());

let result = try_catch(|| {
    panic!("boom");
});
assert!(result.is_failure());
```

### NonEmptyVec\<T\>

A `Vec` guaranteed to have at least one element at the type level.

```rust
use functype::prelude::*;
use functype_core::nev;

let v = nev![1, 2, 3];
assert_eq!(*v.head(), 1);    // no Option — always exists
assert_eq!(v.len(), 3);
```

### Persistent Collections

Immutable, structurally-shared collections backed by [rpds](https://crates.io/crates/rpds). Thread-safe via `Arc`.

```rust
use functype::prelude::*;
use functype_core::{list, map};

let l = list![1, 2, 3];
let l2 = l.prepend(0);
assert_eq!(l.len(), 3);   // original unchanged
assert_eq!(l2.len(), 4);

let m = map!{ "a" => 1, "b" => 2 };
let m2 = m.insert("c", 3);
assert_eq!(m.len(), 2);   // original unchanged
assert_eq!(m2.len(), 3);
```

### Extension Traits

Adds Scala-style combinators to standard library types.

**OptionExt**: `get_or_else`, `fold`, `to_either`, `to_validated`, `tap_some`, `tap_none`, `when`, `contains_where`, `zip_with`

**ResultExt**: `get_or_else`, `fold`, `to_either`, `to_validated`, `tap_ok`, `tap_err`, `bimap`, `recover`, `recover_with`, `swap`

**TupleExt**: `map_n` for 2- through 5-tuples

### Pure Trait

Lifts a value into any monadic context. Implemented for `Option`, `Result`, `Either`, and `Validated`.

```rust
use functype::prelude::*;

let opt: Option<i32> = Pure::pure(42);    // Some(42)
let res: Result<i32, String> = Pure::pure(42); // Ok(42)
```

## Usage

Add to your `Cargo.toml`:

```toml
[dependencies]
functype = { git = "https://github.com/jordanburke/functype-rs" }
```

Or for specific crates:

```toml
[dependencies]
functype-core = { git = "https://github.com/jordanburke/functype-rs" }
functype-io = { git = "https://github.com/jordanburke/functype-rs" }
```

## Requirements

- Rust 1.85+
- Edition 2021

## License

MIT OR Apache-2.0
