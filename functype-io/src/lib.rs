//! functype-io: Lazy, composable IO effect type for functype.
//!
//! Provides `IO<A>`, a lazy, composable effect type.
//! Nothing executes until `.run()` is called.
//!
//! # Examples
//!
//! ```
//! use functype_io::IO;
//!
//! let io = IO::succeed(42).map(|x| x * 2);
//! assert_eq!(io.run().unwrap(), 84);
//! ```

pub mod io;

pub use io::{Task, IO};

pub mod prelude {
    pub use crate::io::{Task, IO};
}
