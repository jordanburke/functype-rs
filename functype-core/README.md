# functype-core

Core functional programming types for Rust.

Part of the [functype](https://crates.io/crates/functype) library.

## Types

- **Either\<L, R\>** — Right-biased disjoint union with `map`, `flat_map`, `fold`, `zip`, `ap`, and conversions to/from `Result`/`Option`
- **Validated\<E, A\>** — Applicative validation that accumulates all errors in `NonEmptyVec<E>`
- **Try** — Captures panics as values (`try_catch`, `try_catch_unchecked`)
- **NonEmptyVec\<T\>** — Vec guaranteed to have at least one element
- **List\<T\>** — Persistent, immutable singly-linked list (structural sharing via Arc)
- **Map\<K, V\>** — Persistent, immutable hash map (structural sharing via Arc)
- **fdo!** — Do-notation macro for monadic composition (works with Option, Result, Either, Validated, IO)
- **Pure** — Trait for lifting values into monadic contexts

## Extension Traits

- **OptionExt** — `get_or_else`, `fold`, `to_either`, `to_validated`, `tap_some`, `tap_none`, `when`, `contains_where`, `zip_with`
- **ResultExt** — `get_or_else`, `fold`, `to_either`, `to_validated`, `tap_ok`, `tap_err`, `bimap`, `recover`, `swap`
- **TupleExt** — `map_n` for 2- through 5-tuples

## Usage

```toml
[dependencies]
functype-core = "0.1"
```

```rust
use functype_core::prelude::*;
use functype_core::fdo;

let result: Option<i32> = fdo! {
    x <- Some(10);
    y <- Some(20);
    yield x + y
};
assert_eq!(result, Some(30));
```

## License

MIT OR Apache-2.0
