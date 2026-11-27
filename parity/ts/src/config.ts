import { Decoder, DecoderError, type Either, Left, type Option, Right } from "functype"

/** One endpoint to check. `paths` are tried in order: the first is the primary, the rest are mirrors. */
export type Endpoint = {
  readonly name: string
  readonly paths: readonly string[]
  readonly retries: number
  readonly optional: boolean
  readonly waitUntilReady: Option<number>
}

export type Config = {
  readonly endpoints: readonly Endpoint[]
}

const nonEmptyString: Decoder<string> = (raw) =>
  Decoder.string(raw).flatMap((s) =>
    s.length > 0 ? Right<DecoderError, string>(s) : Left<DecoderError, string>(DecoderError.leaf([], "empty string")),
  )

const nonNegativeInt: Decoder<number> = (raw) =>
  Decoder.number(raw).flatMap((n) =>
    Number.isInteger(n) && n >= 0
      ? Right<DecoderError, number>(n)
      : Left<DecoderError, number>(DecoderError.leaf([], "expected a non-negative integer")),
  )

const positiveInt: Decoder<number> = (raw) =>
  nonNegativeInt(raw).flatMap((n) =>
    n > 0 ? Right<DecoderError, number>(n) : Left<DecoderError, number>(DecoderError.leaf([], "expected at least 1")),
  )

const nonEmptyArray =
  <A>(inner: Decoder<A>): Decoder<readonly A[]> =>
  (raw) =>
    Decoder.array(inner)(raw).flatMap((items) =>
      items.length > 0
        ? Right<DecoderError, readonly A[]>(items)
        : Left<DecoderError, readonly A[]>(DecoderError.leaf([], "expected at least one item")),
    )

const endpoint: Decoder<Endpoint> = (raw) =>
  Decoder.object({
    name: nonEmptyString,
    paths: nonEmptyArray(nonEmptyString),
    retries: nonNegativeInt,
    optional: Decoder.option(Decoder.boolean),
    waitUntilReady: Decoder.option(positiveInt),
  })(raw).map((e) => ({ ...e, optional: e.optional.getOrElse(() => false) }))

const config: Decoder<Config> = Decoder.object({ endpoints: Decoder.array(endpoint) })

/** Renders a decoder path as `endpoints[1].name`, the format `DecoderError.format` uses. */
const formatPath = (path: ReadonlyArray<string>): string =>
  path.length === 0
    ? "(root)"
    : path.reduce((acc, seg) => (seg.startsWith("[") || acc === "" ? `${acc}${seg}` : `${acc}.${seg}`), "")

/** Every invalid field's path, sorted, or the decoded config. */
export const decodeConfig = (raw: unknown): Either<readonly string[], Config> =>
  config(raw).mapLeft((e) =>
    DecoderError.flatten(e)
      .toArray()
      .map((leaf) => formatPath(leaf.path))
      .sort(),
  )
