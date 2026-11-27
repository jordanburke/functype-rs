# Parity app

A small endpoint health checker, written twice: once in TypeScript with
[functype](https://www.npmjs.com/package/functype), and once in Rust by following
[`docs/LIB_SPEC_TS-to-Rust-mapping.md`](../docs/LIB_SPEC_TS-to-Rust-mapping.md).

It exists to test that mapping on real code. The TS version is the reference. The Rust version
must give the same result on every fixture. Where translating needed something the mapping
doc doesn't say, or says wrong, the doc gets fixed.

## What it does

The app reads a config of endpoints, checks each one over HTTP, and prints a JSON report.

- **Config validation** reports every invalid field at once (TS `Decoder.object`; Rust
  `Validated`).
- **Each endpoint** can have several paths: the first that answers wins (`firstSuccessOf`).
- **Retries** use exponential backoff on network errors and 5xx, never on 4xx, 304 or a bad body
  (`retryWithBackoff` with `while`).
- **`waitUntilReady: n`** polls until the body says `ready: true`, at most `n` times
  (`repeatUntil`).
- **`optional: true`** turns a final 404 into `absent` (`catchTag`). With mirrors, the final
  failure is the last mirror's (`firstSuccessOf` returns the last failure).
- **`deadlineMs`** runs each check to an `Exit` under one shared deadline (TS `runExit({ signal:
  AbortSignal.timeout(ms) })`; Rust `run_exit(fut, sleep_until(deadline))`). A check still
  running then is `cancelled`; the others keep their results.
- **Grades** come from the body's `status` (`Match`), and the exit code from the grades (`Cond`):
  0 healthy, 1 something down, not ready or cancelled, 2 invalid config.

## Layout

- `ts/` — the TS app. `functype` is pinned exactly in `package.json`.
- `rust/` — the Rust app, using this repo's crates by path. It is excluded from the Cargo
  workspace and keeps its own `Cargo.lock`.
- `fixtures/<case>/` — `config.json`, the mock server's script `server.json`, and
  `expected.json`. A fixture may leave out `config.json` to test a missing file, and may add
  `harness.json` (`{ "basePath": "/v1/" }`) to change the base URL's path.
- `harness/mock-server.mjs` — a scripted HTTP server with no dependencies.
- `run.mjs` — runs each implementation against each fixture, on a fresh mock server each time.

## The parity check

For each fixture, the harness compares three things with `expected.json`: the exit code, the
JSON report, and how many requests reached each path. The request counts are what show that
retries, mirrors and polling behave the same. The report holds no timings and no
library-generated text, because neither would match across languages.

`expected.json` is generated from the TS app. The Rust app must match it unedited: if a fixture
needs a different expected result for Rust, that is a finding, not a fix.

```bash
# Build both
(cd parity/ts && pnpm install && pnpm build)
(cd parity/rust && cargo build)

# Check both against every fixture
node parity/run.mjs ts rust

# Regenerate expected.json from the TS app (after changing a fixture on purpose).
# The harness refuses --update for any other implementation.
node parity/run.mjs --update ts
```

## Does the oracle catch translation mistakes?

Yes, for every trap tried. Each mutation below made the Rust app commit one mapping-doc trap, and
each turned at least one fixture red:

| Mutation | Caught by |
|---|---|
| `Url::join`-style base URL (drops the base path) | every fixture with requests |
| integer field via `as_u64` (rejects `2.0`) | `float-integers` |
| `error_for_status`-style check (only 4xx/5xx fail) | `bad-responses` (the 304) |
| `.json()` ignoring the content type | `bad-responses` (the `text/plain` body) |
| retrying every error | `bad-responses` (request counts) |
| serde-style first-error-only config | `invalid-config` |
| `catchTag` match without the 404 check | `optional` |
| a missing `ready` counted as ready | `wait-until-ready` |
| mirrors tried in reverse order | `mirrors` |
| network errors not retried | `network-retry` |
| a serde struct accepting a JSON array | `decoder-edges` |
| reqwest without `charset` (BOM kept) | `decoder-edges` |
| deadline ignored | `deadline` |

## Findings

Gaps found while building the app. Each is either fixed in the mapping doc, fixed in this
repo's crates, or noted for the library it belongs to.

### Mapping doc (fixed)

- **`Decoder.object` → `Validated`:** the doc said to use `Validated` for every-field errors but
  showed no recipe. It now has one ("Collecting every field error"), compiled.
- **The `Http` example's `Decode(reqwest::Error)`** can't hold a failure from serde or from a
  non-JSON content type. It is now `Decode(String)`, and the example reads the content type
  before the body, as TS does.
- **TS's content-type rule** has a third case the doc missed: with no JSON or `text/*` type, TS
  hands the decoder the `Response` object itself.
- **`IO.all` over effects that can't fail** maps to `join_all`, not `try_join_all`.
- **`Number.isInteger`** maps to `as_f64()` plus `fract() == 0.0`; `as_u64()` rejects `2.0`.
- **A serde-derived struct accepts a JSON array** by position, which `Decoder.object` rejects.
  `get_json` now checks for an object first.
- **reqwest without default features** keeps a leading BOM in `text()` (it needs `charset`) and
  can't reach `https` URLs. `fetch` strips the BOM.
- **`serde_json` and `JSON.parse` differ** on `1e400` and lone surrogates.
- **TS `Exit.match` without a `Die` arm** sends a defect to `Failure`. A Rust `match` must name
  `Exit::Die`, so the translation has to decide what the TS code meant. The app now names `Die`
  on both sides, and crashes there.
- **`runExit({ signal: AbortSignal.timeout(ms) })`** maps to `run_exit` with one shared
  `sleep_until(deadline)`, and an effect that can't fail goes in as `Ok::<_, Infallible>`.
- **Node timers top out at 2147483647 ms.** A larger `AbortSignal.timeout` fires after 1 ms, and
  one past 2^32 throws; tokio sleeps as asked. Both apps reject a `deadlineMs` over the limit
  (`deadline-too-large`).
- **A defect exits differently:** TS `invariant` rejects the top-level `await` (exit 1, the same
  as unhealthy), Rust `panic!` exits 101. No fixture can cause one, so this isn't pinned.

### functype-rs (fixed)

- **`NonEmptyVec::map` couldn't return a value borrowing the element**, such as a
  `first_success_of` factory that captures a path. It now ties the borrow to the vec, as
  `Iterator::map` over `iter()` does, and accepts `FnMut`. This is a small breaking change:
  `NonEmptyVec::map` used as a function value no longer coerces to a higher-ranked signature,
  such as `let f: fn(&NonEmptyVec<i32>, fn(&i32) -> i32) -> NonEmptyVec<i32> = NonEmptyVec::map;`.
  Ordinary calls compile as before.

### TS functype

- `Http.client` returns a type, `HttpMethods`, that functype doesn't export. The app names it
  with `ReturnType<typeof Http.client>`.
- `eslint-config-functype`'s `recommended` sets rules only. It registers no parser, plugins or
  `files`, so the README's `export default [recommended]` lints no `.ts` files on ESLint 10.
  `ts/eslint.config.mjs` supplies them.
- `DecoderError.format` renders paths as `endpoints[1].name`, but the path formatter itself
  isn't exported, so `config.ts` repeats it to report one path per error.
- `Match(…).caseValue("ok", "healthy")` infers `string` for the result, so matching into a
  string-literal union needs a type argument on each call: `caseValue<Grade>(…)`.
