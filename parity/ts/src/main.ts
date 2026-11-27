import { readFileSync } from "node:fs"
import { parseArgs } from "node:util"

import { Cond, Http, IO, Try } from "functype"

import { check, type Row } from "./check.js"
import { decodeConfig } from "./config.js"

type Report = { readonly configErrors: readonly string[] } | { readonly checks: readonly Row[] }

const EXIT_OK = 0
const EXIT_UNHEALTHY = 1
const EXIT_INVALID_CONFIG = 2
const EXIT_USAGE = 64

const values = Try(
  () =>
    parseArgs({
      options: { config: { type: "string" }, "base-url": { type: "string" } },
      strict: true,
    }).values,
).fold(
  (e) => {
    process.stderr.write(`${e.message}\n`)
    return process.exit(EXIT_USAGE)
  },
  (v) => v,
)

const configPath = values.config ?? "config.json"
const baseUrl = values["base-url"] ?? ""

const exitCodeFor = (rows: readonly Row[]): number =>
  Cond.of<number>()
    .when(
      rows.some((r) => r.grade === "down" || r.grade === "not_ready"),
      EXIT_UNHEALTHY,
    )
    .else(EXIT_OK)

const print = (report: Report, exitCode: number): void => {
  process.stdout.write(`${JSON.stringify(report, null, 2)}\n`)
  process.exitCode = exitCode
}

const parsed = Try(() => JSON.parse(readFileSync(configPath, "utf8")) as unknown)
  .toEither((): readonly string[] => ["(root)"])
  .flatMap(decodeConfig)

await parsed.fold(
  (configErrors) => {
    print({ configErrors }, EXIT_INVALID_CONFIG)
    return Promise.resolve()
  },
  async (config) => {
    const http = Http.client({ baseUrl })
    const rows = await IO.all(config.endpoints.map((e) => check(http, e))).runOrThrow()
    print({ checks: rows }, exitCodeFor(rows))
  },
)
