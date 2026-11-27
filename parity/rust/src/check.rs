//! One endpoint check. TS: `check.ts`.

use std::time::Duration;

use functype_io::{first_success_of, repeat_until, retry_with_backoff_while, Backoff, RepeatError};
use reqwest::StatusCode;
use serde::{Deserialize, Serialize};

use crate::config::Endpoint;
use crate::http::{Http, HttpError};

const RETRY_BASE: Duration = Duration::from_millis(5);
const POLL_DELAY: Duration = Duration::from_millis(5);

/// TS `Decoder.object({ status: Decoder.string, ready: Decoder.option(Decoder.boolean) })`.
/// serde reads a missing or `null` `ready` as `None`, as `Decoder.option` does.
#[derive(Clone, Debug, Deserialize)]
struct Health {
    status: String,
    ready: Option<bool>,
}

/// The mirror that answered, and what it said.
#[derive(Clone, Debug)]
struct Hit {
    path: String,
    health: Health,
}

/// TS `HttpError | RepeatExhausted<Hit>`, as one enum widened with `From`.
#[derive(Debug, thiserror::Error)]
enum CheckError {
    #[error(transparent)]
    Http(#[from] HttpError),
    #[error("not ready")]
    NotReady,
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Grade {
    Healthy,
    Degraded,
    Unknown,
    Absent,
    Down,
    NotReady,
}

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ErrorKind {
    Network,
    Status,
    Decode,
    Exhausted,
}

/// One line of the JSON report: the wire format the parity harness compares.
#[derive(Clone, Debug, Serialize)]
pub struct Row {
    pub name: String,
    pub grade: Grade,
    pub path: Option<String>,
    pub error: Option<ErrorKind>,
    pub status: Option<u16>,
}

/// TS `Match(h.status).caseValue("ok", "healthy")…default("unknown")`.
fn grade_of(h: &Health) -> Grade {
    match h.status.as_str() {
        "ok" => Grade::Healthy,
        "degraded" => Grade::Degraded,
        _ => Grade::Unknown,
    }
}

impl Row {
    fn down(name: &str) -> Self {
        Row {
            name: name.to_string(),
            grade: Grade::Down,
            path: None,
            error: None,
            status: None,
        }
    }

    fn ok(name: &str, hit: Hit) -> Self {
        Row {
            grade: grade_of(&hit.health),
            path: Some(hit.path),
            ..Row::down(name)
        }
    }

    fn absent(name: &str) -> Self {
        Row {
            grade: Grade::Absent,
            status: Some(404),
            ..Row::down(name)
        }
    }

    fn error(name: &str, err: &CheckError) -> Self {
        let down = Row::down(name);
        match err {
            CheckError::NotReady => Row {
                grade: Grade::NotReady,
                error: Some(ErrorKind::Exhausted),
                ..down
            },
            CheckError::Http(HttpError::Status { status, .. }) => Row {
                error: Some(ErrorKind::Status),
                status: Some(status.as_u16()),
                ..down
            },
            CheckError::Http(HttpError::Decode(_)) => Row {
                error: Some(ErrorKind::Decode),
                ..down
            },
            CheckError::Http(HttpError::Network(_)) => Row {
                error: Some(ErrorKind::Network),
                ..down
            },
        }
    }
}

/// TS `attempt`: `http.get(path, { decode }).map(…).retryWithBackoff({ n, baseMs, while })`.
async fn attempt(http: &Http, path: &str, retries: usize) -> Result<Hit, HttpError> {
    let policy = Backoff::new(retries, RETRY_BASE);
    let health = retry_with_backoff_while(
        policy,
        |e: &HttpError, _attempt| e.is_retryable(),
        || http.get_json::<Health>(path),
    )
    .await?;
    Ok(Hit {
        path: path.to_string(),
        health,
    })
}

/// TS `IO.firstSuccessOf(e.paths.map(attempt))`.
async fn mirrors(http: &Http, e: &Endpoint) -> Result<Hit, HttpError> {
    first_success_of(e.paths.map(|p| move || attempt(http, p, e.retries))).await
}

/// TS `e.waitUntilReady.fold(() => mirrors, (max) => mirrors.repeatUntil(…))`.
async fn polled(http: &Http, e: &Endpoint) -> Result<Hit, CheckError> {
    let Some(max) = e.wait_until_ready else {
        return Ok(mirrors(http, e).await?);
    };
    repeat_until(
        max,
        Some(POLL_DELAY),
        |hit: &Hit| hit.health.ready.unwrap_or(false),
        || mirrors(http, e),
    )
    .await
    .map_err(|err| match err {
        RepeatError::Failure(e) => CheckError::Http(e),
        RepeatError::Exhausted(_) => CheckError::NotReady,
    })
}

/// Checks one endpoint, and always gives a row. TS `check`.
pub async fn check(http: &Http, e: &Endpoint) -> Row {
    match polled(http, e).await {
        Ok(hit) => Row::ok(&e.name, hit),
        // TS `.catchTag("HttpStatusError", …)`: handle the one case, pass the rest through.
        Err(CheckError::Http(HttpError::Status { status, .. })) if e.optional && status == StatusCode::NOT_FOUND => {
            Row::absent(&e.name)
        }
        Err(err) => Row::error(&e.name, &err),
    }
}
