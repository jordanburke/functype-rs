//! functype: Scala/ZIO-inspired functional programming library for Rust.
//!
//! This is the umbrella crate that re-exports all functype functionality.
//!
//! # Quick Start
//! ```
//! use functype::prelude::*;
//!
//! let either: Either<&str, i32> = Either::right(42);
//! let doubled = either.map(|x| x * 2);
//! assert_eq!(doubled.right_value(), Some(&84));
//! ```

pub use functype_core::prelude;
pub use functype_core::*;
