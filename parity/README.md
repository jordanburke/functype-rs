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
- **`optional: true`** turns a 404 into `absent` (`catchTag`).
- **Grades** come from the body's `status` (`Match`), and the exit code from the grades (`Cond`):
  0 healthy, 1 something down or not ready, 2 invalid config.

## Layout

- `ts/` — the TS app. `functype` is pinned exactly in `package.json`.
- `rust/` — the Rust app, using this repo's crates by path.
- `fixtures/<case>/` — `config.json`, the mock server's script `server.json`, and
  `expected.json`.
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
# TS
cd parity/ts && pnpm install && pnpm build && cd ../..
node parity/run.mjs ts

# Regenerate expected.json from the TS app (after changing a fixture on purpose)
node parity/run.mjs --update ts
```

## Findings

Gaps found while building the app. Each is either fixed in the mapping doc or noted for the
library it belongs to.

### TS functype

- `Http.client` returns a type, `HttpMethods`, that functype doesn't export. The app names it
  with `ReturnType<typeof Http.client>`.
- `eslint-config-functype`'s `recommended` sets rules only. It registers no parser, plugins or
  `files`, so the README's `export default [recommended]` lints no `.ts` files on ESLint 10.
  `ts/eslint.config.mjs` supplies them.
