//! The mapping doc's `get_json`, for TS `Http.client({ baseUrl }).get(url, { decode })`.

use reqwest::header::CONTENT_TYPE;
use reqwest::StatusCode;
use serde::de::DeserializeOwned;
use serde_json::Value;

/// TS `NetworkError | HttpStatusError | DecodeError`.
#[derive(Debug, thiserror::Error)]
pub enum HttpError {
    #[error("network error: {0}")]
    Network(#[source] reqwest::Error),
    #[error("HTTP {status}")]
    Status { status: StatusCode, body: String },
    /// The doc's `Decode(reqwest::Error)` can't hold a failure from our own decoding (a non-JSON
    /// content type, or a body of the wrong shape), so this holds the message.
    #[error("decode error: {0}")]
    Decode(String),
}

impl HttpError {
    /// The TS app's `isRetryable`: a network failure or a 5xx.
    pub fn is_retryable(&self) -> bool {
        match self {
            HttpError::Network(_) => true,
            HttpError::Status { status, .. } => status.as_u16() >= 500,
            HttpError::Decode(_) => false,
        }
    }
}

/// TS `HttpClientConfig.baseUrl`: a client plus a base URL.
pub struct Http {
    client: reqwest::Client,
    base_url: String,
}

impl Http {
    pub fn new(base_url: &str) -> Self {
        Http {
            client: reqwest::Client::new(),
            base_url: base_url.to_string(),
        }
    }

    /// TS `client.get(url, { decode })`.
    pub async fn get_json<T: DeserializeOwned>(&self, url: &str) -> Result<T, HttpError> {
        let resp = self
            .client
            .get(resolve_url(&self.base_url, url))
            .send()
            .await
            .map_err(HttpError::Network)?;
        let status = resp.status();
        if !status.is_success() {
            // TS fails on any status outside 200-299 (`!response.ok`) and keeps the body.
            let body = resp.text().await.unwrap_or_default();
            return Err(HttpError::Status { status, body });
        }
        // TS parses JSON only for an application/json content type, and otherwise hands the
        // decoder the body text, which a decoder expecting an object rejects.
        let is_json = resp
            .headers()
            .get(CONTENT_TYPE)
            .and_then(|v| v.to_str().ok())
            .is_some_and(|ct| ct.contains("application/json"));
        // A failed body read is a NetworkError in TS; only parsing is a DecodeError.
        let text = resp.text().await.map_err(HttpError::Network)?;
        let raw = if is_json {
            serde_json::from_str::<Value>(&text).map_err(|e| HttpError::Decode(e.to_string()))?
        } else {
            Value::String(text)
        };
        serde_json::from_value(raw).map_err(|e| HttpError::Decode(e.to_string()))
    }
}

/// TS `resolveUrl` concatenates (`fetch/Http.ts:20-26`); `Url::join` would drop the base path.
pub fn resolve_url(base: &str, url: &str) -> String {
    if base.is_empty() || url.starts_with("http://") || url.starts_with("https://") {
        return url.to_string();
    }
    let base = base.strip_suffix('/').unwrap_or(base);
    if url.starts_with('/') {
        format!("{base}{url}")
    } else {
        format!("{base}/{url}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_url_matches_ts() {
        assert_eq!(resolve_url("http://h/v1", "/users"), "http://h/v1/users");
        assert_eq!(resolve_url("http://h/v1/", "users"), "http://h/v1/users");
        assert_eq!(resolve_url("", "/users"), "/users");
        assert_eq!(resolve_url("http://h/v1", "https://other/x"), "https://other/x");
    }
}
