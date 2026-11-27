//! The parity app's Rust half: an endpoint health checker, translated from `parity/ts` by
//! following `docs/LIB_SPEC_TS-to-Rust-mapping.md`.

mod check;
mod config;
mod http;

use std::io::Write;
use std::process::ExitCode;

use serde::Serialize;

use crate::check::{check, Grade, Row};
use crate::config::decode_config;
use crate::http::Http;

const EXIT_OK: u8 = 0;
const EXIT_UNHEALTHY: u8 = 1;
const EXIT_INVALID_CONFIG: u8 = 2;
const EXIT_USAGE: u8 = 64;

#[derive(Serialize)]
#[serde(untagged)]
enum Report {
    Invalid {
        #[serde(rename = "configErrors")]
        config_errors: Vec<String>,
    },
    Checked {
        checks: Vec<Row>,
    },
}

struct Args {
    config: String,
    base_url: String,
}

/// TS `parseArgs({ options: { config, "base-url" }, strict: true })`.
fn parse_args() -> Result<Args, String> {
    let mut args = Args {
        config: "config.json".to_string(),
        base_url: String::new(),
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        let value = it.next().ok_or_else(|| format!("{flag} needs a value"))?;
        match flag.as_str() {
            "--config" => args.config = value,
            "--base-url" => args.base_url = value,
            other => return Err(format!("unknown option {other}")),
        }
    }
    Ok(args)
}

/// TS `Cond.of<number>().when(anyDown, EXIT_UNHEALTHY).else(EXIT_OK)`.
fn exit_code_for(rows: &[Row]) -> u8 {
    if rows.iter().any(|r| matches!(r.grade, Grade::Down | Grade::NotReady)) {
        EXIT_UNHEALTHY
    } else {
        EXIT_OK
    }
}

fn print(report: &Report, code: u8) -> ExitCode {
    let json = serde_json::to_string_pretty(report).expect("a report always serializes");
    let mut out = std::io::stdout().lock();
    let written = writeln!(out, "{json}").and_then(|()| out.flush());
    match written {
        Ok(()) => ExitCode::from(code),
        Err(_) => ExitCode::FAILURE,
    }
}

#[tokio::main(flavor = "current_thread")]
async fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(msg) => {
            eprintln!("{msg}");
            return ExitCode::from(EXIT_USAGE);
        }
    };

    // TS `Try(() => JSON.parse(readFileSync(path))).toEither(() => ["(root)"]).flatMap(decodeConfig)`.
    let parsed = std::fs::read_to_string(&args.config)
        .ok()
        .and_then(|text| serde_json::from_str::<serde_json::Value>(&text).ok())
        .ok_or_else(|| vec!["(root)".to_string()])
        .and_then(|raw| decode_config(&raw));

    match parsed {
        Err(config_errors) => print(&Report::Invalid { config_errors }, EXIT_INVALID_CONFIG),
        Ok(config) => {
            let http = Http::new(&args.base_url);
            // TS `IO.all(rows)`: every check runs at once, and each always gives a row.
            let rows = futures::future::join_all(config.endpoints.iter().map(|e| check(&http, e))).await;
            let code = exit_code_for(&rows);
            print(&Report::Checked { checks: rows }, code)
        }
    }
}
