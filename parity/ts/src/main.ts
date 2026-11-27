import { readFileSync } from "node:fs"
import { parseArgs } from "node:util"

import { Cond, Http, invariant, Try } from "functype"

import { cancelledRow, check, type Row } from "./check.js"
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
      rows.some((r) => r.grade === "down" || r.grade === "not_ready" || r.grade === "cancelled"),
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
    // One deadline for the whole run. Each check runs to an Exit, so a check the deadline stops
    // reports Interrupted while the others keep their results.
    const options = config.deadlineMs.fold(
      () => ({}),
      (ms) => ({ signal: AbortSignal.timeout(ms) }),
    )
    const rows = await Promise.all(
      config.endpoints.map(async (e) =>
        (await check(http, e).runExit(options)).match({
          Success: (row) => row,
          // A check can't fail (its E is never), so this arm never runs.
          Failure: () => cancelledRow(e.name),
          Interrupted: () => cancelledRow(e.name),
          // Without a Die arm, match routes a defect to Failure; a defect here is a bug, so crash.
          Die: (defect): Row => {
            invariant(false, () => `check ${e.name} died: ${String(defect)}`)
          },
        }),
      ),
    )
    print({ checks: rows }, exitCodeFor(rows))
  },
)
