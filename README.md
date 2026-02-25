# functype

Scala-inspired functional programming library for Rust.

Brings the ergonomics of Scala's type system — `Either`, `Validated`, `IO`, do-notation — to Rust, without fighting the borrow checker.

```rust
use functype::prelude::*;
use functype::IO;
use functype_core::fdo;

let result = fdo! {
    x <- IO::succeed(10);
    y <- IO::succeed(20);
    yield x + y
};
assert_eq!(result.run().unwrap(), 30);
```

## Crates

| Crate | Description |
|-------|-------------|
| [`functype`](functype/) | Umbrella crate — re-exports everything |
| [`functype-core`](functype-core/) | Core types: Either, Validated, Try, NonEmptyVec, persistent collections, fdo! macro |
| [`functype-io`](functype-io/) | Lazy IO effect type with resource safety and async interop |

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

### IO\<A\>

Lazy, composable effect type. Nothing executes until `.run()`.

```rust
use functype::IO;

let io = IO::effect(|| {
    println!("side effect!");
    42
}).map(|x| x * 2);

// Nothing printed yet
let result = io.run().unwrap(); // prints "side effect!", returns 84
```

**Why `IO<A>` instead of three type parameters:**
- **No R (environment)**: Rust has compile-time DI via function arguments + trait bounds.
- **No E (typed error)**: `Result` already handles typed errors. For typed errors, use `IO<Result<A, E>>` — opt-in, not mandatory.
- **One type param**: Clean signatures. `io.map(|x| x + 1)` without error type propagation everywhere.

#### Constructors

```rust
IO::succeed(42)                              // pure value
IO::fail(anyhow::anyhow!("boom"))            // pure error
IO::effect(|| compute())                     // infallible side effect
IO::effect_result(|| Ok(compute()?))         // fallible side effect
IO::from_result(Ok(42))                      // lift Result
IO::from_option(Some(42), || error)          // lift Option
IO::from_either(Either::Right(42))           // lift Either
```

#### Combinators

```rust
io.map(|x| x + 1)                           // transform success
io.flat_map(|x| IO::succeed(x + 1))         // chain effects
io.zip(other)                                // combine into tuple
io.zip_with(other, |a, b| a + b)            // combine with function
io.then(other)                               // sequence, discard first
io.tap(|x| println!("{x}"))                  // side effect, return original
```

#### Error Handling

```rust
io.map_error(|e| anyhow::anyhow!("wrapped: {e}"))  // transform error
io.catch(|e| IO::succeed(fallback))                  // recover
io.or_else(IO::succeed(default))                     // fallback on error
io.either()                                          // IO<Either<Error, A>> (infallible)
IO::retry(|| make_request(), 3)                      // retry up to 3 times
```

#### Resource Safety

```rust
IO::bracket(
    IO::effect(|| open_file()),       // acquire
    |file| IO::effect(|| read(file)), // use
    |file| close(file),               // release (always runs)
);

io.ensuring(|| cleanup())  // finalizer runs on both success and error
```

#### Async Interop

```rust
IO::from_future(async { Ok(fetch().await?) })  // future -> IO
io.to_future().await                            // IO -> future
```

### fdo! Macro

Scala/Haskell-style do-notation. Works with any type that has `and_then` and `map`: `Option`, `Result`, `Either`, `Validated`, `IO`.

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

Lifts a value into any monadic context. Implemented for `Option`, `Result`, `Either`, `Validated`, and `IO`.

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

- Rust 1.75+
- Edition 2021

## License

MIT OR Apache-2.0
