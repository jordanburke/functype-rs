//! Config decoding. TS: `config.ts`, built on `Decoder.object`.
//!
//! TS `Decoder.object` reports every invalid field at once. serde stops at the first error, so
//! this walks a `serde_json::Value` and builds each field as a `Validated`, which accumulates.
//! Each error is the field's path, in the format TS `DecoderError.format` uses
//! (`endpoints[1].name`).

use functype_core::non_empty_vec::NonEmptyVec;
use functype_core::validated::{sequence, Validated};
use serde_json::{Map, Value};

/// One endpoint to check. `paths` are tried in order: the first is the primary, the rest are
/// mirrors.
#[derive(Clone, Debug)]
pub struct Endpoint {
    pub name: String,
    pub paths: NonEmptyVec<String>,
    pub retries: usize,
    pub optional: bool,
    pub wait_until_ready: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub endpoints: Vec<Endpoint>,
    /// Checks still running after this many milliseconds are reported as `cancelled`.
    pub deadline_ms: Option<usize>,
}

/// A field's result. The error is the field's path.
type Field<A> = Validated<String, A>;

/// TS `obj[key]`: a missing key reads as `undefined`, which every decoder here treats like `null`.
fn get<'a>(obj: &'a Map<String, Value>, key: &str) -> &'a Value {
    obj.get(key).unwrap_or(&Value::Null)
}

fn non_empty_string(v: &Value, path: &str) -> Field<String> {
    match v.as_str() {
        Some(s) if !s.is_empty() => Validated::valid(s.to_string()),
        _ => Validated::invalid(path.to_string()),
    }
}

/// TS `Number.isInteger(n) && n >= 0`. JSON `2.0` is an integer in TS, so this reads the value
/// as `f64` rather than `as_u64`, which would reject it. TS has no upper bound; `as usize`
/// saturates a huge value instead of rejecting it.
fn non_negative_int(v: &Value, path: &str) -> Field<usize> {
    match v.as_f64() {
        Some(n) if n >= 0.0 && n.fract() == 0.0 => Validated::valid(n as usize),
        _ => Validated::invalid(path.to_string()),
    }
}

fn positive_int(v: &Value, path: &str) -> Field<usize> {
    non_negative_int(v, path).and_then(|n| {
        if n > 0 {
            Validated::valid(n)
        } else {
            Validated::invalid(path.to_string())
        }
    })
}

/// TS `timerMs`: a positive integer no larger than Node's timer limit, 2^31 - 1 ms. Tokio has no
/// such limit, but TS would fire a larger deadline after 1 ms, so both sides reject it.
const MAX_TIMER_MS: usize = 2_147_483_647;

fn timer_ms(v: &Value, path: &str) -> Field<usize> {
    positive_int(v, path).and_then(|n| {
        if n <= MAX_TIMER_MS {
            Validated::valid(n)
        } else {
            Validated::invalid(path.to_string())
        }
    })
}

/// TS `Decoder.option(inner)`: `null` or a missing key is `None`.
fn option<A>(v: &Value, inner: impl FnOnce(&Value) -> Field<A>) -> Field<Option<A>> {
    if v.is_null() {
        Validated::valid(None)
    } else {
        inner(v).map(Some)
    }
}

/// TS `nonEmptyArray(nonEmptyString)`: item errors first; only a clean array is checked for
/// emptiness.
fn paths(v: &Value, path: &str) -> Field<NonEmptyVec<String>> {
    let Some(items) = v.as_array() else {
        return Validated::invalid(path.to_string());
    };
    sequence(
        items
            .iter()
            .enumerate()
            .map(|(i, item)| non_empty_string(item, &format!("{path}[{i}]"))),
    )
    .and_then(|ps| match NonEmptyVec::from_vec(ps) {
        Some(ps) => Validated::valid(ps),
        None => Validated::invalid(path.to_string()),
    })
}

fn endpoint(v: &Value, path: &str) -> Field<Endpoint> {
    let Some(obj) = v.as_object() else {
        return Validated::invalid(path.to_string());
    };
    let at = |key: &str| format!("{path}.{key}");
    let name = non_empty_string(get(obj, "name"), &at("name"));
    let paths = paths(get(obj, "paths"), &at("paths"));
    let retries = non_negative_int(get(obj, "retries"), &at("retries"));
    let optional = option(get(obj, "optional"), |v| match v.as_bool() {
        Some(b) => Validated::valid(b),
        None => Validated::invalid(at("optional")),
    });
    let wait = option(get(obj, "waitUntilReady"), |v| positive_int(v, &at("waitUntilReady")));
    name.zip4(&paths, &retries, &optional)
        .zip(&wait)
        .map(|((name, paths, retries, optional), wait_until_ready)| Endpoint {
            name,
            paths,
            retries,
            optional: optional.unwrap_or(false),
            wait_until_ready,
        })
}

/// Every invalid field's path, sorted, or the decoded config.
pub fn decode_config(raw: &Value) -> Result<Config, Vec<String>> {
    let Some(obj) = raw.as_object() else {
        return Err(vec!["(root)".to_string()]);
    };
    // TS reports a non-array `endpoints` with any other field errors, so keep collecting.
    let endpoints = match get(obj, "endpoints").as_array() {
        Some(items) => sequence(
            items
                .iter()
                .enumerate()
                .map(|(i, e)| endpoint(e, &format!("endpoints[{i}]"))),
        ),
        None => Validated::invalid("endpoints".to_string()),
    };
    let deadline = option(get(obj, "deadlineMs"), |v| timer_ms(v, "deadlineMs"));
    endpoints
        .zip(&deadline)
        .map(|(endpoints, deadline_ms)| Config { endpoints, deadline_ms })
        .to_result()
        .map_err(|errors| {
            let mut paths = errors.into_vec();
            paths.sort();
            paths
        })
}
