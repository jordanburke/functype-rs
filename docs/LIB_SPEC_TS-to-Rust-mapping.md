# TS functype → Rust mapping

Status: revised 2026-11-27. IO decided: `async fn`, with the helpers in `functype-io`. Errors and the remaining modules mapped.
Compared: TS `functype` 2.2.2 (release commit `14c12d44`; line references are to that commit) against `functype-rs` 0.1.1 (`main`).

## Goal

Code written with TS functype should translate to Rust by a fixed mapping, type by type and
method by method. A reader who knows one port should be able to read the other.

"Same shape" means the same meaning and the same mapping. It does not mean the same method
names grafted onto types Rust already has.

## Principles

1. **TS is the source of truth for meaning.** Rust follows it through this mapping. TS does not
   change shape to suit Rust.
2. **Map to std where Rust has the type.** TS functype exists partly because TypeScript has no
   `Option` or `Result`. Rust does. A translated program should read as normal Rust.
3. **functype-rs supplies only what Rust lacks.** Error accumulation (`Validated`,
   `NonEmptyVec`), exit reporting (`Exit`, `run_exit`), named retry/repeat policies with TS defaults, and an
   expression-level do-notation (`fdo!`). Where an established crate covers a gap (`backon`,
   `tokio-util`, `indexmap`), the mapping points to it instead.
4. **A translation must compile correctly or fail to compile.** This is TS functype's own rule
   (`docs/ROADMAP.md`, Principles, line 169). Any mapping that can compile and silently do the
   wrong thing is listed under Traps.
5. **No alias layer.** Don't add `get_or_else` and friends onto std `Option`/`Result` just to
   match TS names. It gives every operation two names. Put the name map in this doc instead.

MSRV note: the workspace declares `rust-version = "1.85"`, the MSRV of `tokio` and `rpds`. It
uses `resolver = "3"`, so Cargo picks dependency versions that fit, and CI runs the tests on
1.85. Every std method this doc maps to is
stable by then (`inspect`/`inspect_err` 1.76, `LazyLock` 1.80), and indexmap 2.14 also needs
1.85. Check the MSRV of `backon`, `tokio-util` and `futures-util` before adding them.

## Type map

| TS functype 2.2.2 | Rust | Notes |
|---|---|---|
| `Option<T>` | `std::option::Option<T>` | std |
| `Option(nullable)` | the value is already `Option<T>` in Rust | std |
| `Either<L, R>` | `Result<R, L>` | **Parameters swap.** See Traps |
| `Either.fromNullable(v, l)` | `opt.ok_or(l)` | std |
| `Try<T>` | `Result<T, E>` | Pick a concrete `E`; TS is always `Error`, so `anyhow::Error` is the closest default. `functype_core::Try` (`Result<T, TryError>`, catches panics) maps here only where the TS code relied on catching a crash. See Traps |
| `Try(() => f())` / `tryCatch` | a fn returning `Result` | std |
| `Do(function* …)` over Option/Either/Try | **`fdo!`** (`functype-core/src/fdo.rs:48`), or `?` inside a helper fn / immediately-called closure | **Not bare `?` in the enclosing fn.** See Traps |
| `Do` over `List` (cartesian product) | iterator `flat_map` | std |
| `DoAsync` | `async` block + `?` | same caveat as `Do` |
| `List<T>` | `Vec<T>` | TS `List` copies its array on every change (`list/List.ts:270-304`). See List methods |
| `LazyList<T>` | `impl Iterator<Item = T>` | std |
| `Map<K, V>` / `Set<T>` | `indexmap::IndexMap` / `IndexSet` | TS `Map` wraps the ES Map (`map/Map.ts:17`), which iterates in insertion order. `HashMap` (arbitrary) and `BTreeMap` (sorted) change iteration order. Use them only where order is not observed. Remove with **`shift_remove`**: `IndexMap::remove` is deprecated because it reorders the map (indexmap 2.x) |
| `Stack<T>` | `Vec<T>` (`push`/`pop`/`last`) | TS `Stack` is immutable; apply the `List` clone rule |
| `Lazy<T>` | `LazyLock<Result<T, E>>` / `OnceLock` | TS `Lazy` memoizes a thrown error (`lazy/Lazy.ts:219-246`); a panicking `LazyLock` poisons and re-panics instead. Make the error a value |
| `Ref<A>` | `Cell`/`RefCell` (one thread), `Arc<Mutex<A>>` or atomics (shared) | std |
| `Tuple` | native tuples | std |
| Branded types (`PositiveInteger`, `EmailAddress`, …) | newtype + `TryFrom` | std pattern; functype-rs could ship the common ones |
| `TypedError<Code>` | error `enum` (e.g. with `thiserror`), one variant per code | TS discriminates on `code` (`error/typed/TypedError.ts:95-96`). Its `_tag` is always `"Throwable"` (`core/throwable/Throwable.ts:20`), so `catchTag` does not apply to it |
| `Validation` helpers → `FormValidation<T>` = `Either<List<TypedError>, T>` | `Result<T, NonEmptyVec<E>>` via `functype_core::Validated<E, A>` | See Validated |
| `IO<R, E, A>` | `async fn -> Result<A, E>` | See IO |
| `Exit<E, A>` | **functype-rs `Exit`** + `run_exit` | `fold`/`match` → Rust `match`; `mapError` → `map_err`; `flatMap` → `and_then`; `toOption` → `ok()`; `getOrElse` → `unwrap_or_else` |
| `Context` / `Tag` / `Layer` | plain arguments, see Services | |
| `Match` / `Cond`, `Http`, `Decoder`, serialization | `match` / `if`, `reqwest`, `serde` | See Other modules |
| `Obj` | **not mapped yet** | |

## Method map (Option, Either, Try)

| TS | Rust std | Notes |
|---|---|---|
| `map` | `map` | **Not for `Try` with a throwing `f`.** See Traps |
| `flatMap` | `and_then` | |
| `mapTry(f, onError)` | `and_then(\|v\| f(v).map_err(onError))`, with `f` returning `Result` | |
| `getOrElse(() => x)` | `unwrap_or_else(\|\| x)` | Lazy. See Traps |
| `orElse(() => o)` | `or_else(\|\| o)` on `Option`; `or_else(\|_\| r)` on `Result` | The `Option` form doesn't compile on `Result`; the compiler catches a mix-up |
| `fold(onNone, onSome)` | `map_or_else(onNone, onSome)` | Same order, empty case first |
| `match({ Some, None })` | `match` | |
| `filter` | `filter` | |
| `orThrow()` | `?` in a fallible fn; `expect("…")` only where TS meant a crash | `?` on `Option` doesn't convert into a `Result` fn; it fails to compile, so add `ok_or` |
| `orNull()` / `orUndefined()` | not needed; keep the `Option` | |
| `toEither(e)` | `ok_or(e)` / `ok_or_else(\|\| e)` | |
| `Either.toOption()` | `ok()` | |
| `mapLeft` | `map_err` | |
| `tap` (Either only) | `inspect` (std 1.76) | TS `Option` and `Try` have no `tap` |
| `tapLeft` | `inspect_err` (std 1.76) | |
| `swap` | no std method; `functype_core::ResultExt::swap` | |
| `bimap(fl, fr)` | `.map_err(fl).map(fr)` | functype-rs has no `Result` `bimap`; `functype_core::Either::bimap` keeps the TS order `(on_left, on_right)` |
| `filterOrElse(p, e)` | `and_then(\|v\| if p(&v) { Ok(v) } else { Err(e(v)) })` | |
| `recover(f)` (Try) | `or_else(\|e\| Ok(f(e)))`, or `or_else(f)` when `f` can fail | TS `recover` returns `Try<T \| U>` (`try/Try.ts:118`) and runs `f` inside `Try` (337-339), so a throwing `f` becomes `Failure`. Not `unwrap_or_else` |
| `recoverWith(f)` (Try) | `or_else(f)` | |
| `traverse` / `sequence` | `iter.map(f).collect::<Result<Vec<_>, _>>()` | |
| `flatMapAsync` / `mapAsync` / `foldAsync` | inside an `async` block: `match` or `?` on the awaited value | |

## List methods

TS `List` methods return a new list. Rust `Vec` methods mutate in place. The rule: when the old
TS list is never used again, mutate the `Vec`. When it is still used, `clone()` first.

| TS `List` | Rust |
|---|---|
| `add(x)` | `v.push(x)` (old list dead) / `{ let mut w = v.clone(); w.push(x); w }` |
| `prepend(x)` | `v.insert(0, x)` |
| `concat(o)` | `v.extend(o)` |
| `removeAt(i)` | `if i < v.len() { v.remove(i); }` (TS returns the list unchanged when `i` is out of range, `list/List.ts:267-270`; bare `v.remove(i)` panics) |
| `map` / `filter` / `flatMap` | `into_iter().map(…).collect()` (or `iter()` to keep the original) |
| `foldLeft(z)(op)` | `iter().fold(z, op)` |
| `reduce` | `iter().copied().reduce(op)` / `into_iter().reduce(op)` |
| `head` / `headOption` | `first()` |
| `last` / `lastOption` | `last()` |
| `tail` | `&v[1..]` (after checking non-empty) |
| `take(n)` / `drop(n)` | `iter().take(n)` / `iter().skip(n)` |
| `find` / `exists` / `every` | `iter().find` / `any` / `all` |
| `reverse` | `v.reverse()` / `iter().rev()` |
| `sortBy(f)` | `v.sort_by_key(f)` |
| `distinct` | `IndexSet` collect, to keep first-seen order. TS compares objects by reference (`list/List.ts:315-324`), Rust by value (`Eq`/`Hash`); the same holds for `groupBy` and `Map` keys |
| `groupBy(f)` | fold into an `IndexMap<K, Vec<T>>` |
| `zip` / `zipWithIndex` | `iter().zip` / `iter().enumerate()` |
| `partition(p)` | `into_iter().partition(p)` |

## Traps

Each of these compiles and changes meaning, except the last, which is a rule to keep.

- **`Either<L, R>` → `Result<R, L>` swaps the type parameters.** When `L` and `R` differ, a
  mis-order fails to compile. When they are the same type (`Either<string, string>`), it compiles
  and swaps success with failure. Reorder on every occurrence, and test both paths for same-type
  Eithers.
- **`Do` → bare `?` returns from the whole function.** TS `Do(...)` is an expression that
  evaluates to `None`/`Left`, and the code after it keeps running. Rust `?` returns from the
  enclosing fn. When the return types happen to match, it compiles and skips the rest of the fn.
  Use `fdo!`, or put the `?` chain in its own helper fn or an immediately-called closure.
- **`bimap` argument order.** TS `bimap(fl, fr)` is left first (`either/Either.ts:107`).
  Translate it to `.map_err(fl).map(fr)`, which names each side. (functype-rs used to have a
  `ResultExt::bimap(on_ok, on_err)` that compiled with same-typed sides and swapped them; it is
  removed.)
- **TS IO recovery also catches defects; Rust `match Err` doesn't.** In TS the error channel
  holds `Die` as well as `Failure` (`io/IO.ts:1137-1141`), and `Recover`, `RecoverWith` and
  `MapError` branch on it (`io/IO.ts:1617-1636`). So a throw inside `IO.sync` is recovered or
  retried by `recover`, `recoverWith`, `catchAll`, `mapError`, `retry*` and `firstSuccessOf`.
  (`timeoutTo` no longer does, as of 2.2.2.) In Rust a panic passes straight through `match fut.await { Err(e) => … }`.
  **Rule: anything the TS code expects to recover from must return `Err` in Rust.** A throwing
  TS step becomes a `Result`-returning Rust step. The functype-rs helpers do not catch panics;
  only `run_exit` reports one, as `Die`.
- **`Try.map` and `Try.recover` catch errors; `Result::map` and `or_else` don't.** TS `Try.map` runs `f` inside `Try`
  (`try/Try.ts:197`), so a throw becomes `Failure`; `Try.recover` does the same (`try/Try.ts:337-339`).
  A Rust `f` that can fail must return `Result` and go through `and_then` (for `map`) or
  `or_else` (for `recover`); a panic in `map` is not caught.
- **`Try` is not panic capture.** Translating every TS `Try` to `functype_core::Try` wraps
  ordinary errors in `catch_unwind`. Most TS `Try` sites become plain `Result`.
- **`getOrElse` laziness.** TS `getOrElse` takes a thunk. Map it to `unwrap_or_else`, not
  `unwrap_or`, or the default is computed eagerly.
- **`Map`/`Set` iteration order.** See the type map: use `IndexMap`/`IndexSet`, and remove with
  `shift_remove`, never `remove` or `swap_remove`, when order is
  observed.
- **`fold` argument order** agrees today (TS `fold(onNone, onSome)` / `fold(onLeft, onRight)`
  and `map_or_else(default, f)`). Keep any functype-rs `fold` in that order.

## IO

Decision: **TS `IO` maps to `async fn -> Result<A, E>`.** functype-rs does not ship an `IO`
effect type. Rust futures are already lazy, which is the main thing TS `IO` adds over `Promise`,
and `async fn` is what a Rust reader or an LLM writes by default.

### What TS `IO<R, E, A>` has

- Typed error `E` that widens as you chain: `flatMap` gives `E | E2` (`io/IO.ts:367`),
  `timeout` adds `TimeoutError` (730), `catchTag` gives `Exclude<E, {_tag: K}> | E2` (442-445).
  `recover`/`timeoutTo` widen the value to `A | B` (415, 741).
- `run()` returns `Promise<Either<E, A>>` and **throws** on `Die` and `Interrupted`
  (`io/IO.ts:1181-1185`); `runExit()` returns `Promise<Exit<E, A>>`; `runSync`, `runOrThrow`,
  `runSyncOrThrow` exist.
- Constructors: `sync`, `succeed`, `fail`, `die`, `async`, `tryPromise`, `tryCatch`, `all`,
  `forEach`, `race`, `firstSuccessOf`, `sleep`.
- Do-notation: `IO.gen` (generator, `io/IO.ts:2728`) and the `IO.Do` builder (`io/IO.ts:2752`).
- Policies: `retry`, `retryWithDelay`, `retryWhile`, `retryWithBackoff`, `repeatUntil`,
  `repeatWhile`, `timeout`, `timeoutTo`, `delay`, `interruptOn(signal)`.
- Resources: `bracket`, `bracketExit`, `acquireRelease`.
- Services: `provideService`, `provideContext`, `provideLayer`.
- An `IO` value can run more than once: `retry` is `this.recoverWith(() => this.retry(n - 1))`
  (`io/IO.ts:924-927`).

### The mapping

| TS `IO` | Rust |
|---|---|
| a function returning `IO<R, E, A>` | `async fn …(deps: &Deps, …) -> Result<A, E>` |
| `IO.gen` / `IO.Do` body | the `async fn` body |
| `io.map(f)` | `f(io.await?)` |
| `io.flatMap(g)` | `let a = io.await?; g(a).await` |
| `mapError(h)` | `.await.map_err(h)` |
| `recover(v)` / `recoverWith(f)` / `catchAll(f)` | `match fut.await { Ok(a) => a, Err(e) => … }` |
| `catchTag(tag, f)` | `match` on the error-enum variant; manual rewrite, see Errors |
| `tap(f)` / `tapError(f)` | `.await.inspect(f)` / `.inspect_err(f)` (std 1.76) |
| `IO.succeed(a)` / `IO.fail(e)` | `Ok(a)` / `Err(e.into())` (`.into()` widens into the module error enum) |
| `IO.sync(f)` / `IO.tryCatch(f, onErr)` | a sync call / `f().map_err(onErr)` |
| `IO.async(f)` / `IO.tryPromise` | `.await` the future |
| `IO.all` (default: all at once, `io/IO.ts:2439`) | `tokio::try_join!` / `futures::future::try_join_all` |
| `IO.forEach` (default: one at a time, `io/IO.ts:2672`) | `for x in items { out.push(f(x).await?) }` |
| `all` / `forEach` with `{ concurrency: n }` | `stream::iter(items).map(f).buffered(n).try_collect().await`. Same result type, but which error comes back can differ: `try_collect` returns the lowest-index error once earlier items finish, while TS fails on the first failure in time and aborts the rest (`io/IO.ts:2031-2045`) |
| `IO.race(effects)` (first to settle, success or failure; takes an array, `io/IO.ts:2650`) | `tokio::select!` for a fixed set; `futures::future::select_all` for a dynamic list |
| `IO.firstSuccessOf` (runs in sequence; first success, else last failure, `io/IO.ts:2470-2475`) | functype-rs `first_success_of(nev![…])`. It takes a `NonEmptyVec`, so an empty list fails to compile; TS dies at run time. All factories share one type: map one closure over the inputs, or box different effects as `Box<dyn FnOnce() -> BoxIO<'static, A, E> + Send>` (mixing unboxed closures fails with E0308) |
| `IO.sleep(ms)` / `delay(ms)` | `tokio::time::sleep` |
| `timeout(ms)` | `tokio::time::timeout(d, fut).await` → `Result<Result<A, E>, Elapsed>`; map `Elapsed` into the error enum |
| `timeoutTo(ms, b)` | `timeout(d, fut).await.unwrap_or(Ok(b))`. As of 2.2.2, TS returns `b` only when its own deadline passes (`io/IO.ts:1976-2004`); the effect's failures, defects and interruption pass through, and a cancelled run is `Interrupted`, not `b`. Before 2.2.2 it also replaced every failure; code that relied on that adds `.recover(b)` in TS, `.or_else(\|_\| Ok(b))` in Rust |
| `retry(n)` (no delay, `io/IO.ts:924-927`) | functype-rs `retry(n, \|\| get_user(id))` |
| `retryWithDelay(n, ms)` | functype-rs `retry_with_delay(n, d, factory)`, or `backon` `ConstantBuilder::default().with_delay(d).with_max_times(n)` |
| `retryWithBackoff(opts)` | functype-rs `retry_with_backoff(Backoff::new(n, base), factory)`; `maxMs`/`factor`/`jitter` → `.with_max(d)`/`.with_factor(f)`/`.with_jitter(b)`; with `while` → `retry_with_backoff_while(policy, retry_if, factory)`. `Backoff::new` sets the TS defaults (jitter on at 50–100% of the delay, 30 s cap, `io/IO.ts:947-949`). `backon` `ExponentialBuilder` works only with every setting explicit (`with_max_times`, `with_min_delay`, `with_max_delay`, `with_jitter`): its defaults (no jitter, factor 2, 1 s min, 60 s max, 3 tries) differ from TS, and its jitter formula differs too |
| `retryWhile({ n, while, delayMs })` (predicate gets `(error, attempt)`, attempt 1-indexed) | functype-rs `retry_while(n, delay, retry_if, factory)`, with `delay: Option<Duration>` and `retry_if: FnMut(&E, usize) -> bool` |
| `repeatUntil(done, { max })` / `repeatWhile` | functype-rs `repeat_until(max, delay, done, factory)` / `repeat_while(max, delay, keep_going, factory)`, returning `Result<A, RepeatError<E, A>>`: `RepeatError::Failure(e)` for the first `Err`, `RepeatError::Exhausted(RepeatExhausted { max, last_value })` after `max` runs. TS `E \| RepeatExhausted<A>` becomes that enum; widen it into a module error enum with `From` (`io/IO.ts:965-977`). **Not a bare `loop`**: it compiles and can spin forever |
| `interruptOn(signal)` | `tokio_util::sync::CancellationToken` + `select!`, mapping cancellation to an `Interrupted` variant of the error enum (TS puts `InterruptedError` in `E`, `io/IO.ts:776`) |
| `bracket` / `acquireRelease` | a `Drop` guard for sync release; see Limits |
| `run()` | `.await` |
| `runExit({ signal })` | functype-rs `run_exit(fut, token.cancelled()).await` → `Exit<E, A>`. The second argument is any cancellation future; `runExit()` with no signal → `std::future::pending()` |
| fire-and-forget `io.run()` (no `await`) | `tokio::spawn(fut)` |
| `runSync()` | a plain sync fn returning `Result` |
| `provide*` | see Services |
| stored or dynamically dispatched `IO` | `BoxIO<'a, A, E>` (below) |

### What functype-rs ships for IO

Only the gaps:
- **`Exit<E, A>`** with `Success`/`Failure`/`Die`/`Interrupted`, and
  **`run_exit(fut, cancelled)`**, which runs a future, catches a panic as `Die`, and reports
  `Interrupted` when `cancelled` finishes first, as TS `runExit({ signal })` does
  (`io/IO.ts:1041-1048`). `cancelled` is any future, such as `token.cancelled()` from
  `tokio_util::sync::CancellationToken`, so functype-rs doesn't depend on `tokio-util`. A dropped
  future reports nothing, so the argument is required. As in TS, an already-done cancel stops
  the effect before it starts. After that, Rust sees the cancel only between polls: a failure
  on the wake-up that sees it is `Interrupted`, a success on that wake-up is kept, and a defect
  stays `Die`. TS checks before every step, so a TS `io.map(f)` aborted mid-run reports
  `Interrupted` where the Rust `async` block may run on to `Success`.
- **Named policy helpers with TS defaults**, each taking its factory as the last argument:
  `retry`, `retry_with_delay`, `retry_while`, `retry_with_backoff`, `retry_with_backoff_while`
  (with the `Backoff` policy), `repeat_until`, `repeat_while`, `first_success_of`.
  These are the places where TS has a named policy and Rust has only a primitive, so a bare
  primitive would compile with different counts, delays or bounds.
- **`BoxIO<'a, A, E>`** = `Pin<Box<dyn Future<Output = Result<A, E>> + Send + 'a>>`, for storing
  futures and for trait objects.

Rejected:
- **An `IO` effect struct** (the former `functype-io` boxed thunk, now removed, or a boxed-future wrapper):
  an allocation per combinator, `Send + 'static` on everything, a second idiom next to
  `async fn`, and no widely used Rust crate takes this shape.
- **`impl IO<A, E>` in signatures.** It adds no type safety over `impl Future<…>`, and:
  - a borrowed argument fails with E0700 on edition 2021 unless `+ '_` is added; `async fn`
    handles it;
  - code before an inner `async` block runs at call time, which breaks TS laziness and compiles
    silently; `async fn` can't make this mistake;
  - `IO<A, E>` vs TS `IO<R, E, A>` is a second parameter-order trap when `A` and `E` are the
    same type;
  - trait methods returning it aren't `Send` unless `+ Send` is written out.
- **`futures::TryFutureExt` chains** as the translation target. With `futures::FutureExt` in
  scope, a literal `io.map(f)` maps the whole `Result` and drops the error into `f`; TS `map`
  touches only the success value. `TryFutureExt::and_then` also needs one error type on both
  sides with no `From`. `async` + `?` avoids both.

### Rules

- **Effects run once, and re-running takes a factory.** A future runs once. TS `retry`,
  `retryWithBackoff`, `repeatUntil` and `repeatWhile` translate to calls that take
  `Fn() -> impl Future`. A second `.await` of a consumed future fails to compile, so
  Principle 4 holds.
- **A future that is never awaited never runs.** TS `io.run()` without `await` still runs; a Rust
  future without `.await` does nothing, and the compiler only warns (`unused_must_use`). Treat
  that warning as an error (`#![deny(unused_must_use)]`). The lint misses `let _ = fut;` and a
  future bound to a name and never awaited, so review for those. Fire-and-forget TS code maps to
  `tokio::spawn`.
- **Errors: one error enum per module, widened by `From`, never narrowed.** Rust has no unions, so
  `E | E2` becomes a module enum with `From` impls, and `?` widens. An enum can't lose a variant,
  so `catchTag` can't narrow the type. **`catchTag` is a manual rewrite**: a `match` on the
  variant that handles one case and re-raises the rest into the same enum.
- **`.await` reports defects as panics.** TS `run()` throws on `Die`/`Interrupted` (and TS
  recovery catches `Die` first; see Traps). In Rust a
  panic propagates through `.await` on its own within one task; across `tokio::spawn` it arrives
  as a `JoinError`. A dropped future simply stops. Use
  `run_exit` where the TS code inspected `Exit`.

### Limits

- `Die` from a panic needs unwind capture across `.await`. `run_exit` does it with
  `catch_unwind` around each poll, so it needs no `futures-util`. It cannot work under
  `panic = "abort"`.
- `bracket` with an async release is best effort. When a future is dropped mid-await, Rust has
  no async `Drop`, so the release can't be guaranteed to run. A sync release in a `Drop` guard
  is guaranteed.
- `backon`, `tokio-util` and `futures-util` are not functype-rs dependencies. Translated code
  adds the ones it uses. functype-io depends on `tokio` with only the `time` feature, for the
  retry and repeat delays.

## Services (`R`)

Decision: **drop `R`.** A missing service still fails to compile, as a missing argument, so
Principle 4 holds. Keeping `R` would need a type-level set to stand in for `R | R2`, and
signatures get heavy.

The mapping:
- `Tag<S>` → a trait or struct type `S`.
- Services travel in **one deps struct** per module, passed by reference (`&Deps`). Pick this one
  shape rather than mixing arguments and trait bounds.
- `Layer<RIn, E, ROut>` → `async fn build(deps: &RIn) -> Result<ROut, E>`, because
  `provideLayer` awaits the build and carries its error (`io/IO.ts:618,1010-1020`).
- `provideService` / `provideContext` / `provideLayer` → build the deps struct, then call the fn
  with it.

## Validated vs Validation

- Rust has a real `Validated<E, A>` with `NonEmptyVec<E>` errors (`functype-core/src/validated.rs:105`)
  and applicative `zip`.
- TS has no `Validated` type. `FormValidation<T>` is `Either<List<TypedError<"VALIDATION_FAILED">>, T>`
  (`error/typed/Validation.ts:47`), where the list can be empty by type.

Decision: **keep Rust's shape.** Map `FormValidation<T>` → `Result<T, NonEmptyVec<E>>`, built
with `Validated`. Whether TS should gain `Validated` is a TS decision, outside this doc.

## Errors

TS error channels are unions of tagged objects (`NotFound | Timeout`), and they widen as
effects chain. Rust has no union types. The convention:

- **One error enum per module**, one variant per TS `_tag`. Derive `Debug` and
  `thiserror::Error`.
- **Widen with `From`, never narrow.** Where TS gets `E | E2`, the caller's enum wraps each
  source with `#[from]`, and `?` converts. An enum can't lose a variant, so a handled case stays
  in the type.
- **`catchTag` is a manual rewrite**: a `match` that handles one variant and passes the rest
  through. The result type is still the whole enum.
- **Throws that TS recovers become `Err`**, never panics (see Traps).

Worked example. TS:

```ts
type NotFound = { _tag: "NotFound"; id: string }
type Timeout = { _tag: "Timeout"; ms: number }

const getUser = (id: string): IO<never, NotFound | Timeout, User> => …

// catchTag narrows the error to Timeout
const getUserOrGuest = (id: string) => getUser(id).catchTag("NotFound", () => IO.succeed(User.guest()))
```

Rust:

```rust
#[derive(Debug, PartialEq, thiserror::Error)]
enum UserError {
    #[error("user {0} not found")]
    NotFound(String),
    #[error("timed out after {0:?}")]
    Timeout(Duration),
}

async fn get_user(id: &str) -> Result<User, UserError> { … }

// catchTag("NotFound", …): handle one variant, pass the rest through.
// The type stays Result<User, UserError>; NotFound is no longer produced, but the type can't say so.
async fn get_user_or_guest(id: &str) -> Result<User, UserError> {
    match get_user(id).await {
        Err(UserError::NotFound(_)) => Ok(User::guest()),
        other => other,
    }
}

// Widening: TS `UserError | ConfigError` becomes one enum with From for each source.
#[derive(Debug, thiserror::Error)]
enum AppError {
    #[error(transparent)]
    User(#[from] UserError),
    #[error("bad config: {0}")]
    Config(String),
}

async fn greet(id: &str) -> Result<String, AppError> {
    let user = get_user_or_guest(id).await?; // UserError -> AppError via From
    Ok(format!("hi {}", user.name))
}
```

When a caller really needs the narrowed type, write a second enum without the handled variant
and map into it explicitly. That is a design choice, not a mechanical translation.

| TS | Rust |
|---|---|
| `IO.fail(e)` with a tagged `e` | `Err(ModuleError::Variant(..))` |
| `catchTag(tag, f)` | `match` on that variant; the rest pass through |
| `catchAll(f)` / `recoverWith(f)` | `match` / `or_else` on the whole `Result` |
| `mapError(f)` | `map_err(f)` |
| `E \| E2` from `flatMap` | a caller enum with `#[from]` variants, and `?` |
| `TypedError<Code>` | an enum variant per code, holding the TS `context` fields |
| `RepeatExhausted` / `TimeoutError` / `InterruptedError` in `E` | a variant of the module enum; `From<RepeatError<E, A>>` or `From<tokio::time::error::Elapsed>` where useful |

## Other modules

### `Cond` and `Match`

TS passes conditions and non-function values as plain arguments, so they are evaluated before
the call, eagerly. Rust `if` / `match` evaluates only the branch taken. A side effect in an
unchosen condition or value runs in TS and not in Rust. Function values (thunks) are lazy in
both.

| TS | Rust | Notes |
|---|---|---|
| `Cond.of<T>().when(c, v).elseWhen(c2, v2).else(v3)` | `if c { v } else if c2 { v2 } else { v3 }` | TS evaluates `c2`, `v` and `v2` even when `c` is true (`conditional/Cond.ts:62,70`) |
| `Cond.lazy<T>()` | `if` / `else if` / `else` | Both lazy |
| `Cond.match(value)({ a: …, b: … })` | `match` over an enum | `conditional/Cond.ts:147` |
| `Cond…orThrow()` | `else { panic!("…") }`, or return `Err` if TS caught it | TS throws `Error("Conditional expression has no matching condition")` |
| `Match(v).case(p, r)…default(d)` | `match v { x if p(&x) => r, _ => d }` | First match wins in both. TS evaluates every non-function `r` eagerly (`conditional/Match.ts:180,218,232`) |
| `Match(v).caseValue(x, r)` / `caseValues([x, y], r)` | `x => r` / `x \| y => r` match arms | |
| `Match(v).when(guard, r)` | a guard arm: `x if guard(&x) => r` | |
| `Match(v)…exhaustive()` | a `match` with no `_` arm, over an enum | TS checks at run time and throws (`conditional/Match.ts:275-282`); Rust checks at compile time |
| `Match(v)…orThrow(msg)` | `_ => panic!("{msg}")`, or `Err` if TS caught it | `unreachable!(msg)` with a non-literal `msg` fails to compile |
| `Match(v)…toOption()` | a `match` that returns `Option` | |
| `Match.exhaustive<Status, R>({ pending: …, … })(s)` | `enum Status` + `match s { Status::Pending => …, … }` | A TS string-literal union becomes an enum |
| `Match.partial({…}).withDefault(f)(v)` | `match v { 200 => …, 404 => …, code => f(code) }` | |
| `Match.withGuards([[p, r], …]).withDefault(d)(v)` | guard arms in order, then `_ => d` | |

### `Http`

TS `Http.get/post/…(url, opts)` returns `IO<never, HttpError, HttpResponse<T>>`
(`fetch/Http.ts:228-231`). The usual Rust target is `reqwest`, written out so each TS error case
keeps its own variant:

```rust
#[derive(Debug, thiserror::Error)]
enum HttpError {
    #[error("network error: {0}")]
    Network(#[source] reqwest::Error),
    #[error("HTTP {status}")]
    Status { status: reqwest::StatusCode, body: String },
    #[error("decode error: {0}")]
    Decode(#[source] reqwest::Error),
}

// TS: Http.get(url, { decode }) with HttpClientConfig.baseUrl
async fn get_json<T: serde::de::DeserializeOwned>(
    client: &reqwest::Client,
    base_url: &str,
    url: &str,
) -> Result<T, HttpError> {
    let resp = client.get(resolve_url(base_url, url)).send().await.map_err(HttpError::Network)?;
    let status = resp.status();
    if !status.is_success() {
        // TS fails on any status outside 200-299 (`!response.ok`) and keeps the body.
        let body = resp.text().await.unwrap_or_default();
        return Err(HttpError::Status { status, body });
    }
    // `json()` reads the body, then parses. TS reports a failed read as a NetworkError and only a
    // parse failure as a DecodeError (`fetch/Http.ts:292-296`).
    resp.json::<T>().await.map_err(|e| if e.is_decode() { HttpError::Decode(e) } else { HttpError::Network(e) })
}

// TS resolveUrl concatenates (`fetch/Http.ts:20-26`).
fn resolve_url(base: &str, url: &str) -> String {
    if base.is_empty() || url.starts_with("http://") || url.starts_with("https://") {
        return url.to_string();
    }
    let base = base.strip_suffix('/').unwrap_or(base);
    if url.starts_with('/') { format!("{base}{url}") } else { format!("{base}/{url}") }
}
```

| TS | Rust | Notes |
|---|---|---|
| `Http.get(url, { decode })` | `get_json` above | **Not `error_for_status()`**: it errors only on 4xx/5xx, so a 304 (or a 3xx with redirects off) decodes instead of failing as TS does (`fetch/Http.ts:278`). It also consumes the response, so the body is lost. And a single `#[from] reqwest::Error` would merge network, status and decode failures into one variant |
| `HttpClientConfig.baseUrl` | `resolve_url` above | **Not `Url::join`**: joining `/users` onto `https://api.x/v1` gives `https://api.x/users`, where TS gives `/v1/users` |
| `HttpClientConfig.defaultHeaders` | `reqwest::Client::builder().default_headers(…)` | |
| `NetworkError \| HttpStatusError \| DecodeError` | the `HttpError` enum above | |
| parse by content type | check `resp.headers()` before `.json()` | TS parses JSON only when the content type includes `application/json`, and returns text for `text/*` (`fetch/Http.ts:170-175`); `.json()` ignores the content type |
| `HttpResponse { data, status, headers }` | read `resp.status()` / `resp.headers()` before consuming the body | |
| `retryWithBackoff`, `timeout` on the IO | functype-io `retry_with_backoff` around a factory; `tokio::time::timeout` | See IO |
| `signal` | drop the future, or `select!` on a cancellation token | |

### `Decoder`

TS `Decoder<A>` is `(raw: unknown) => Either<DecoderError, A>` (`decoder/Decoder.ts:17`). The Rust
target is `serde::Deserialize` plus `serde_json::from_value` / `from_str`.

| TS | Rust (`serde`) | Notes |
|---|---|---|
| `Decoder.object({ a, b })` | `#[derive(Deserialize)] struct { a, b }` | **TS collects every failing field into one `Composite` error; serde stops at the first.** Code that reports all field errors needs `Validated` over per-field results, not plain serde |
| `Decoder.list(inner)` / `array` | `Vec<T>` | Same first-error difference |
| `Decoder.map(inner)` | `IndexMap<String, T>` (indexmap's `serde` feature) | Keeps key order, as the type map requires; `HashMap` would not. Same first-error difference |
| `Decoder.string` / `number` / `boolean` | `String` / `f64` (or an integer type) / `bool` | TS `number` is `f64`. An integer type rejects `1.0`, which TS accepts |
| `Decoder.option(inner)` / `nullable(inner)` | `Option<T>` | Both sides read `null` and a missing key as `None` |
| `Decoder.either.envelope({ ok, err })` | `#[serde(rename_all = "lowercase")] enum Envelope<R, L> { Ok(R), Err(L) }` | serde's externally tagged enum rejects **any** extra key (`{"ok": 1, "meta": "x"}` fails). TS ignores extra keys and takes `ok` first when both exist |
| `Decoder.either.discriminated({ tag, leftTag, rightTag }, l, r)` | `#[serde(tag = "<tag>")]` enum with `#[serde(rename = "<leftTag>")]` / `"<rightTag>"` variants | |
| `Decoder.fromThrowing(zod.parse)` | a `Deserialize` type, or `TryFrom` after deserializing | |
| `DecoderError` (`Leaf { path, message }` / `Composite { path, children }`) | `serde_json::Error` (line and column, one error) | For field paths, add `serde_path_to_error` |

### Serialization (`toJSON`)

TS functype types serialize with an `"@functype"` marker and a `_tag`, for example
`{ "@functype": "Option", "_tag": "Some", "value": … }` (`option/Option.ts:195`) and the same for
`Either` (`either/Either.ts:139`). The fields differ by type: a `Try` failure carries `error`, not
`value` (`try/Try.ts:142`). Plain serde does not produce this shape: `Option<T>` serializes as the
value or `null`, and `Result` as `{"Ok": …}`. Code that exchanges functype JSON with a TS service
needs a serde adapter. functype-rs does not ship one yet; until it does, translate such payloads
with explicit wire structs.

## Trim what std covers

Done:
- `OptionExt` keeps only what std lacks: `to_either`, `to_validated`, `to_non_empty_vec` and
  `tap_none`, all taking `self` by value, so none clones. `get_or_else`, `or_else_lazy`, `fold`,
  `tap_some`, `contains_where`, `zip_with` and the free fn `when` are removed; their std forms are
  `unwrap_or_else`, `or_else`, `map_or_else`, `inspect`, `is_some_and`, `a.zip(b).map(|(a, b)| f(a, b))` and
  `cond.then(f)`.
- `ResultExt` keeps `to_either`, `to_validated` and `swap`. `get_or_else`, `fold`, `tap_ok`,
  `tap_err`, `recover`, `recover_with` and `bimap` are removed.

Left as they are, outside this mapping:
- `functype_core::Either` stays as a non-error two-way value. Translated TS `Either` code still
  goes to `Result`.
- `TryExt` on `functype_core::Try` keeps its own names (`get_or_else`, `recover`, …), because
  `Try` holds a caught panic, not a TS `Try`.
- Persistent `List`/`Map` (on `rpds`): TS lists "no persistent data structures" as a non-goal
  (`docs/ROADMAP.md`, line 61). They are Rust-only.

Keep: `fdo!` and `Pure` (they back the `Do` mapping), `Validated`, `NonEmptyVec`,
`functype_core::Try` (for the TS sites that relied on catching a crash), and `ResultExt::swap`
(no std equivalent).

## Next steps

1. Revisit `functype_core::Either` and the persistent collections if translated code never uses them.
2. A serde adapter for functype's `{ "@functype", "_tag", "value" }` JSON, for services that talk to TS.
3. Map `Obj`.
