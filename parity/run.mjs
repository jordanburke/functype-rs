#!/usr/bin/env node
// Parity harness: runs each implementation against each fixture and compares the result with
// the fixture's expected.json.
//
//   node parity/run.mjs ts rust        check both implementations
//   node parity/run.mjs --update ts    rewrite every expected.json from the TS run
//
// A fixture is a directory under parity/fixtures with server.json, expected.json, usually
// config.json (a fixture may leave it out to test a missing file), and optionally harness.json,
// { "basePath": "/v1/" }, to change the base URL's path (default "/v1"). Each implementation
// run gets a fresh mock server, so scripted sequences ("fail twice, then 200") start over. The
// result compared is the exit code, the JSON report on stdout, and how many requests reached
// each path.
import { spawn } from "node:child_process"
import { existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs"
import { deepStrictEqual } from "node:assert/strict"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

import { startMock } from "./harness/mock-server.mjs"

const root = dirname(fileURLToPath(import.meta.url))
const IMPLS = {
  ts: ["node", [join(root, "ts", "dist", "main.js")]],
  rust: [join(root, "rust", "target", "debug", "functype-parity"), []],
}
const RUN_TIMEOUT_MS = 30_000

const args = process.argv.slice(2)
const update = args.includes("--update")
const impls = args.filter((a) => !a.startsWith("--"))
if (impls.length === 0 || impls.some((i) => !IMPLS[i])) {
  console.error(`usage: node parity/run.mjs [--update] <${Object.keys(IMPLS).join("|")}>...`)
  process.exit(64)
}
// The TS app is the reference; expected.json never comes from a translation.
if (update && (impls.length !== 1 || impls[0] !== "ts")) {
  console.error("--update writes expected.json from the TS app only: node parity/run.mjs --update ts")
  process.exit(64)
}
for (const impl of impls) {
  const [cmd, pre] = IMPLS[impl]
  const entry = pre[0] ?? cmd
  if (!existsSync(entry)) {
    console.error(`${impl}: ${entry} not found; build it first (see parity/README.md)`)
    process.exit(66)
  }
}

const run = (impl, configPath, baseUrl) =>
  new Promise((resolve, reject) => {
    const [cmd, pre] = IMPLS[impl]
    const child = spawn(cmd, [...pre, "--config", configPath, "--base-url", baseUrl], {
      stdio: ["ignore", "pipe", "pipe"],
    })
    let stdout = ""
    let stderr = ""
    child.stdout.on("data", (d) => (stdout += d))
    child.stderr.on("data", (d) => (stderr += d))
    const timer = setTimeout(() => child.kill("SIGKILL"), RUN_TIMEOUT_MS)
    child.on("error", reject)
    child.on("close", (code, signal) => {
      clearTimeout(timer)
      resolve({ code, signal, stdout, stderr })
    })
  })

const sorted = (obj) => Object.fromEntries(Object.entries(obj).sort(([a], [b]) => a.localeCompare(b)))

const fixturesDir = join(root, "fixtures")
const fixtures = readdirSync(fixturesDir, { withFileTypes: true })
  .filter((d) => d.isDirectory())
  .map((d) => d.name)
  .sort()

let failures = 0
for (const name of fixtures) {
  const dir = join(fixturesDir, name)
  const script = JSON.parse(readFileSync(join(dir, "server.json"), "utf8"))
  const harness = existsSync(join(dir, "harness.json")) ? JSON.parse(readFileSync(join(dir, "harness.json"), "utf8")) : {}
  const basePath = harness.basePath ?? "/v1"
  for (const impl of impls) {
    const mock = await startMock(script)
    const out = await run(impl, join(dir, "config.json"), `${mock.url}${basePath}`)
    await mock.close()
    const label = `${name} [${impl}]`
    let report
    try {
      report = JSON.parse(out.stdout)
    } catch {
      failures++
      console.log(`FAIL ${label}: stdout is not JSON (exit ${out.code ?? out.signal})\n${out.stdout}${out.stderr}`)
      continue
    }
    const actual = { exitCode: out.code, report, requests: sorted(mock.requests) }
    const expectedPath = join(dir, "expected.json")
    if (update) {
      writeFileSync(expectedPath, `${JSON.stringify(actual, null, 2)}\n`)
      console.log(`WROTE ${label}`)
      continue
    }
    try {
      deepStrictEqual(actual, JSON.parse(readFileSync(expectedPath, "utf8")))
      console.log(`PASS ${label}`)
    } catch (e) {
      failures++
      console.log(`FAIL ${label}\n${e.message}${out.stderr ? `\nstderr:\n${out.stderr}` : ""}`)
    }
  }
}
console.log(failures === 0 ? "\nall fixtures pass" : `\n${failures} failure(s)`)
process.exit(failures === 0 ? 0 : 1)
