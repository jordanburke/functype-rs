import type { HttpError } from "functype"
import { Decoder, type Http, IO, Match, type Option, RepeatExhausted, type Wire } from "functype"

import type { Endpoint } from "./config.js"

// TODO(functype): `Http.client` returns `HttpMethods`, which functype doesn't export.
type HttpClient = ReturnType<typeof Http.client>

type Health = { readonly status: string; readonly ready: Option<boolean> }

const health: Decoder<Health> = Decoder.object({ status: Decoder.string, ready: Decoder.option(Decoder.boolean) })

export type Grade = "healthy" | "degraded" | "unknown" | "absent" | "down" | "not_ready"

/** One line of the JSON report. It's the wire format the parity harness compares. */
export type Row = Wire<{
  readonly name: string
  readonly grade: Grade
  readonly path: string | null
  readonly error: "network" | "status" | "decode" | "exhausted" | null
  readonly status: number | null
}>

/** The mirror that answered, and what it said. */
type Hit = { readonly path: string; readonly health: Health }

type CheckError = HttpError | RepeatExhausted<Hit>

const RETRY_BASE_MS = 5
const POLL_DELAY_MS = 5

/** Retry a network failure or a 5xx; a 4xx, a 304 or a decode failure won't change on retry. */
const isRetryable = (e: HttpError): boolean =>
  e._tag === "NetworkError" || (e._tag === "HttpStatusError" && e.status >= 500)

const gradeOf = (h: Health): Grade =>
  Match(h.status).caseValue<Grade>("ok", "healthy").caseValue<Grade>("degraded", "degraded").default<Grade>("unknown")

const okRow = (name: string, hit: Hit): Row => ({
  name,
  grade: gradeOf(hit.health),
  path: hit.path,
  error: null,
  status: null,
})

const absentRow = (name: string): Row => ({ name, grade: "absent", path: null, error: null, status: 404 })

const errorRow = (name: string, err: CheckError): Row => {
  const down = { name, grade: "down", path: null, status: null } as const
  if (err instanceof RepeatExhausted) return { ...down, grade: "not_ready", error: "exhausted" }
  if (err._tag === "HttpStatusError") return { ...down, error: "status", status: err.status }
  if (err._tag === "DecodeError") return { ...down, error: "decode" }
  return { ...down, error: "network" }
}

/**
 * Checks one endpoint, and always succeeds with a row.
 *
 * Each path is fetched with retries; the first path that answers wins (`firstSuccessOf`). With
 * `waitUntilReady`, the whole thing is re-run until the body says `ready: true`. An optional
 * endpoint that answers 404 everywhere is `absent`, not `down`.
 */
export const check = (http: HttpClient, e: Endpoint): IO<never, never, Row> => {
  const attempt = (path: string): IO<never, HttpError, Hit> =>
    http
      .get(path, { decode: health })
      .map((res): Hit => ({ path, health: res.data }))
      .retryWithBackoff({ n: e.retries, baseMs: RETRY_BASE_MS, while: isRetryable })

  const mirrors = IO.firstSuccessOf(e.paths.map(attempt))

  const polled: IO<never, CheckError, Hit> = e.waitUntilReady.fold(
    () => mirrors,
    (max) => mirrors.repeatUntil((hit) => hit.health.ready.getOrElse(() => false), { max, delayMs: POLL_DELAY_MS }),
  )

  return polled
    .map((hit) => okRow(e.name, hit))
    .catchTag("HttpStatusError", (err) =>
      e.optional && err.status === 404 ? IO.succeed(absentRow(e.name)) : IO.fail(err),
    )
    .fold(
      (err) => errorRow(e.name, err),
      (row) => row,
    )
}
