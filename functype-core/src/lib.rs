//! functype-core: Core functional programming types for Rust.
//!
//! This crate provides Scala/ZIO-inspired functional programming primitives
//! including Either, Validated, Try, NonEmptyVec, and persistent collections.

pub mod collections;
pub mod either;
pub mod non_empty_vec;
pub mod option_ext;
pub mod prelude;
pub mod result_ext;
pub mod try_type;
pub mod tuple_ext;
pub mod validated;
