/// Scala/Haskell-style do-notation macro for monadic composition.
///
/// Desugars imperative-looking syntax into `and_then`/`map` chains.
/// Works with any type that implements `and_then` (Option, Result, Either, Validated).
///
/// # Syntax
///
/// | Form | Meaning |
/// |------|---------|
/// | `x <- expr;` | Bind: unwrap `expr`, binding the inner value to `x` |
/// | `_ <- expr;` | Discard bind: execute `expr` for its effect, discard value |
/// | `let x = expr;` | Pure let: bind a pure (non-monadic) expression |
/// | `when cond;` | Guard: short-circuit to `None` if `cond` is false (Option only) |
/// | `yield expr` | Terminal: lift `expr` into the monad via `Pure::pure()` |
/// | `expr` | Terminal: return `expr` as-is (must already be the right type) |
///
/// # Examples
///
/// ```
/// use functype_core::fdo;
/// use functype_core::pure::Pure;
///
/// // Option chaining
/// let result: Option<i32> = fdo! {
///     x <- Some(1);
///     y <- Some(2);
///     yield x + y
/// };
/// assert_eq!(result, Some(3));
///
/// // Short-circuit on None
/// let result: Option<i32> = fdo! {
///     x <- Some(1);
///     y <- None::<i32>;
///     yield x + y
/// };
/// assert_eq!(result, None);
///
/// // Result chaining
/// let result: Result<i32, &str> = fdo! {
///     x <- Ok(10);
///     y <- Ok(20);
///     yield x + y
/// };
/// assert_eq!(result, Ok(30));
/// ```
#[macro_export]
macro_rules! fdo {
    // Optimization: last bind + yield → map instead of and_then
    ($binding:ident <- $x:expr ; yield $final:expr) => {
        $x.map(|$binding| $final)
    };

    // Bind: x <- expr; rest → expr.and_then(|x| fdo!{rest})
    ($binding:ident <- $x:expr ; $($rest:tt)+) => {
        $x.and_then(|$binding| fdo!{ $($rest)+ })
    };

    // Discard bind: _ <- expr; rest
    (_ <- $x:expr ; $($rest:tt)+) => {
        $x.and_then(|_| fdo!{ $($rest)+ })
    };

    // Let binding: let pat = expr; rest
    (let $p:pat = $e:expr ; $($rest:tt)+) => {
        { let $p = $e; fdo!{ $($rest)+ } }
    };

    // Guard: when cond; rest → if cond { rest } else { None }
    (when $cond:expr ; $($rest:tt)+) => {
        if $cond { fdo!{ $($rest)+ } } else { None }
    };

    // Terminal: yield lifts via Pure::pure()
    (yield $e:expr) => {
        $crate::pure::Pure::pure($e)
    };

    // Terminal: bare expression passthrough (MUST be last — $e:expr is greedy)
    ($e:expr) => {
        $e
    };
}

#[cfg(test)]
mod tests {
    use crate::either::Either;
    use crate::pure::Pure;
    use crate::validated::Validated;

    // ===== Option tests =====

    #[test]
    fn option_single_bind() {
        let result: Option<i32> = fdo! {
            x <- Some(42);
            yield x
        };
        assert_eq!(result, Some(42));
    }

    #[test]
    fn option_multi_bind() {
        let result: Option<i32> = fdo! {
            x <- Some(1);
            y <- Some(2);
            z <- Some(3);
            yield x + y + z
        };
        assert_eq!(result, Some(6));
    }

    #[test]
    fn option_none_short_circuit() {
        let result: Option<i32> = fdo! {
            x <- Some(1);
            _y <- None::<i32>;
            yield x
        };
        assert_eq!(result, None);
    }

    #[test]
    fn option_let_binding() {
        let result: Option<i32> = fdo! {
            x <- Some(10);
            let y = x * 2;
            z <- Some(3);
            yield y + z
        };
        assert_eq!(result, Some(23));
    }

    #[test]
    fn option_when_guard_pass() {
        let result: Option<i32> = fdo! {
            x <- Some(42);
            when x > 0;
            yield x * 10
        };
        assert_eq!(result, Some(420));
    }

    #[test]
    fn option_when_guard_fail() {
        let result: Option<i32> = fdo! {
            x <- Some(-1);
            when x > 0;
            yield x * 10
        };
        assert_eq!(result, None);
    }

    #[test]
    fn option_discard_bind() {
        let result: Option<i32> = fdo! {
            x <- Some(42);
            _ <- Some("ignored");
            yield x
        };
        assert_eq!(result, Some(42));
    }

    #[test]
    fn option_bare_expression() {
        let result: Option<i32> = fdo! {
            x <- Some(42);
            Some(x + 1)
        };
        assert_eq!(result, Some(43));
    }

    // ===== Result tests =====

    #[test]
    fn result_single_bind() {
        let result: Result<i32, &str> = fdo! {
            x <- Ok::<i32, &str>(42);
            yield x
        };
        assert_eq!(result, Ok(42));
    }

    #[test]
    fn result_multi_bind() {
        let result: Result<i32, &str> = fdo! {
            x <- Ok::<i32, &str>(10);
            y <- Ok::<i32, &str>(20);
            yield x + y
        };
        assert_eq!(result, Ok(30));
    }

    #[test]
    fn result_err_short_circuit() {
        let result: Result<i32, &str> = fdo! {
            x <- Ok::<i32, &str>(10);
            _y <- Err::<i32, &str>("fail");
            yield x
        };
        assert_eq!(result, Err("fail"));
    }

    #[test]
    fn result_let_binding() {
        let result: Result<i32, &str> = fdo! {
            x <- Ok::<i32, &str>(5);
            let doubled = x * 2;
            y <- Ok::<i32, &str>(3);
            yield doubled + y
        };
        assert_eq!(result, Ok(13));
    }

    // ===== Either tests =====

    #[test]
    fn either_single_bind() {
        let result: Either<&str, i32> = fdo! {
            x <- Either::right(42);
            yield x
        };
        assert_eq!(result, Either::Right(42));
    }

    #[test]
    fn either_multi_bind() {
        let result: Either<&str, i32> = fdo! {
            x <- Either::<&str, i32>::right(10);
            y <- Either::<&str, i32>::right(20);
            yield x + y
        };
        assert_eq!(result, Either::Right(30));
    }

    #[test]
    fn either_left_short_circuit() {
        let result: Either<&str, i32> = fdo! {
            x <- Either::<&str, i32>::right(10);
            _y <- Either::<&str, i32>::left("fail");
            yield x
        };
        assert_eq!(result, Either::Left("fail"));
    }

    // ===== Validated tests =====

    #[test]
    fn validated_single_bind() {
        let result: Validated<String, i32> = fdo! {
            x <- Validated::<String, i32>::valid(42);
            yield x
        };
        assert_eq!(result, Validated::Valid(42));
    }

    #[test]
    fn validated_invalid_short_circuit() {
        let result: Validated<String, i32> = fdo! {
            x <- Validated::<String, i32>::valid(10);
            _y <- Validated::<String, i32>::invalid("err".to_string());
            yield x
        };
        assert!(result.is_invalid());
    }

    // ===== Map optimization test =====

    #[test]
    fn map_optimization_option() {
        let result: Option<String> = fdo! {
            x <- Some(42);
            yield x.to_string()
        };
        assert_eq!(result, Some("42".to_string()));
    }

    #[test]
    fn map_optimization_result() {
        let result: Result<String, &str> = fdo! {
            x <- Ok::<i32, &str>(42);
            yield x.to_string()
        };
        assert_eq!(result, Ok("42".to_string()));
    }

    // ===== Nested fdo! =====

    #[test]
    fn nested_fdo() {
        let result: Option<i32> = fdo! {
            x <- Some(10);
            y <- fdo! {
                a <- Some(20);
                yield a + 1
            };
            yield x + y
        };
        assert_eq!(result, Some(31));
    }

    // ===== Complex composition =====

    #[test]
    fn complex_option_pipeline() {
        fn parse(s: &str) -> Option<i32> {
            s.parse().ok()
        }

        let result: Option<i32> = fdo! {
            x <- parse("10");
            y <- parse("20");
            let sum = x + y;
            when sum > 0;
            yield sum * 2
        };
        assert_eq!(result, Some(60));
    }

    #[test]
    fn complex_result_pipeline() {
        fn safe_div(a: i32, b: i32) -> Result<i32, String> {
            if b == 0 {
                Err("division by zero".to_string())
            } else {
                Ok(a / b)
            }
        }

        let result: Result<i32, String> = fdo! {
            x <- safe_div(100, 5);
            y <- safe_div(x, 2);
            yield y + 1
        };
        assert_eq!(result, Ok(11));
    }

    #[test]
    fn complex_result_pipeline_error() {
        fn safe_div(a: i32, b: i32) -> Result<i32, String> {
            if b == 0 {
                Err("division by zero".to_string())
            } else {
                Ok(a / b)
            }
        }

        let result: Result<i32, String> = fdo! {
            x <- safe_div(100, 0);
            y <- safe_div(x, 2);
            yield y + 1
        };
        assert_eq!(result, Err("division by zero".to_string()));
    }
}
