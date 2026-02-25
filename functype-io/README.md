# functype-io

Lazy, composable IO effect type for Rust.

Part of the [functype](https://crates.io/crates/functype) library.

## IO\<A\>

A deferred computation that produces a value of type `A` or fails with an error. Nothing executes until `.run()` is called.

```rust
use functype_io::IO;

let io = IO::effect(|| {
    println!("side effect!");
    42
}).map(|x| x * 2);

// Nothing printed yet
let result = io.run().unwrap(); // prints "side effect!", returns 84
```

## Features

- **Constructors** — `succeed`, `fail`, `effect`, `effect_result`, `from_result`, `from_option`, `from_either`
- **Combinators** — `map`, `flat_map`, `zip`, `zip_with`, `then`, `tap`
- **Error handling** — `map_error`, `catch`, `or_else`, `either()`, `retry`
- **Resource safety** — `bracket` (acquire/use/release), `ensuring` (finalizer)
- **Async interop** — `from_future`, `to_future`
- **Do-notation** — Works with `fdo!` macro via `and_then`/`map`

## Usage

```toml
[dependencies]
functype-io = "0.1"
```

```rust
use functype_io::IO;
use functype_core::fdo;

let result = fdo! {
    x <- IO::succeed(10);
    y <- IO::succeed(20);
    yield x + y
};
assert_eq!(result.run().unwrap(), 30);
```

## License

MIT OR Apache-2.0
