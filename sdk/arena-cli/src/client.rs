//! Blocking HTTP client for the arena API v1 (`docs/CONTRACTS.md` §10).
//! Responses are kept as raw `serde_json::Value` so `--json` output is the
//! server's object verbatim; typed views are parsed only where logic needs them.

use crate::config::Config;
use crate::exit::{CliError, CliResult, Exit};
use serde_json::Value;
use std::io::{BufRead, BufReader};
use std::time::Duration;

pub struct Client {
    pub base: String,
    token: Option<String>,
    agent: ureq::Agent,
    stream_agent: ureq::Agent,
}

/// One Server-Sent Event.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SseEvent {
    pub event: String,
    pub data: String,
    pub id: Option<String>,
}

fn user_agent() -> String {
    format!("arena-cli/{}", env!("CARGO_PKG_VERSION"))
}

pub fn map_status(code: u16, body: &str) -> CliError {
    let body = body.chars().take(2000).collect::<String>();
    let exit = match code {
        401 | 403 => Exit::Auth,
        404 => Exit::NotFound,
        429 | 500..=599 => Exit::Unavailable,
        _ => Exit::Rejected,
    };
    CliError::new(exit, format!("HTTP {code}: {body}"))
}

fn map_err(e: ureq::Error) -> CliError {
    match e {
        ureq::Error::Status(code, resp) => {
            let body = resp.into_string().unwrap_or_default();
            map_status(code, &body)
        }
        ureq::Error::Transport(t) => {
            CliError::new(Exit::Unavailable, format!("cannot reach arena server: {t}"))
        }
    }
}

impl Client {
    pub fn new(cfg: &Config) -> Client {
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(15))
            .timeout(Duration::from_secs(600))
            .user_agent(&user_agent())
            .build();
        let stream_agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(15))
            .user_agent(&user_agent())
            .build();
        Client {
            base: cfg.url.clone(),
            token: cfg.token.clone(),
            agent,
            stream_agent,
        }
    }

    fn req(&self, agent: &ureq::Agent, method: &str, path: &str) -> ureq::Request {
        let mut r = agent.request(method, &format!("{}{}", self.base, path));
        if let Some(t) = &self.token {
            r = r.set("Authorization", &format!("Bearer {t}"));
        }
        r
    }

    fn json(resp: ureq::Response) -> CliResult<Value> {
        let s = resp
            .into_string()
            .map_err(|e| CliError::new(Exit::Unavailable, format!("reading response: {e}")))?;
        serde_json::from_str(&s)
            .map_err(|e| CliError::new(Exit::Unavailable, format!("server sent invalid JSON: {e}")))
    }

    pub fn get_json(&self, path: &str) -> CliResult<Value> {
        let r = self
            .req(&self.agent, "GET", path)
            .set("Accept", "application/json")
            .call()
            .map_err(map_err)?;
        Self::json(r)
    }

    pub fn post_json(&self, path: &str, body: &Value) -> CliResult<Value> {
        let r = self
            .req(&self.agent, "POST", path)
            .set("Content-Type", "application/json")
            .send_string(&body.to_string())
            .map_err(map_err)?;
        Self::json(r)
    }

    /// `POST /v1/uploads` with the raw archive bytes.
    pub fn upload(&self, bytes: &[u8]) -> CliResult<Value> {
        let r = self
            .req(&self.agent, "POST", "/v1/uploads")
            .set("Content-Type", "application/x-tar")
            .send_bytes(bytes)
            .map_err(map_err)?;
        Self::json(r)
    }

    pub fn get_text(&self, path: &str) -> CliResult<String> {
        let r = self.req(&self.agent, "GET", path).call().map_err(map_err)?;
        r.into_string()
            .map_err(|e| CliError::new(Exit::Unavailable, e.to_string()))
    }

    /// Open the SSE stream; `on_event` returns `false` to stop reading.
    pub fn sse(
        &self,
        path: &str,
        last_event_id: Option<&str>,
        mut on_event: impl FnMut(SseEvent) -> CliResult<bool>,
    ) -> CliResult<()> {
        let mut r = self
            .req(&self.stream_agent, "GET", path)
            .set("Accept", "text/event-stream");
        if let Some(id) = last_event_id {
            r = r.set("Last-Event-ID", id);
        }
        let resp = r.call().map_err(map_err)?;
        let mut p = SseParser::default();
        for line in BufReader::new(resp.into_reader()).lines() {
            let line =
                line.map_err(|e| CliError::new(Exit::Unavailable, format!("event stream: {e}")))?;
            if let Some(ev) = p.feed_line(&line) {
                if !on_event(ev)? {
                    return Ok(());
                }
            }
        }
        Ok(())
    }
}

/// Incremental `text/event-stream` parser (WHATWG rules, minus `retry`).
#[derive(Default)]
pub struct SseParser {
    event: String,
    data: Vec<String>,
    id: Option<String>,
}

impl SseParser {
    pub fn feed_line(&mut self, line: &str) -> Option<SseEvent> {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() {
            if self.data.is_empty() && self.event.is_empty() {
                return None;
            }
            let ev = SseEvent {
                event: if self.event.is_empty() {
                    "message".into()
                } else {
                    std::mem::take(&mut self.event)
                },
                data: std::mem::take(&mut self.data).join("\n"),
                id: self.id.clone(),
            };
            self.event.clear();
            return Some(ev);
        }
        if line.starts_with(':') {
            return None;
        }
        let (field, value) = match line.split_once(':') {
            Some((f, v)) => (f, v.strip_prefix(' ').unwrap_or(v)),
            None => (line, ""),
        };
        match field {
            "event" => self.event = value.to_string(),
            "data" => self.data.push(value.to_string()),
            "id" if !value.contains('\0') => self.id = Some(value.to_string()),
            _ => {}
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sse_parse() {
        let mut p = SseParser::default();
        let lines = [
            ": hi",
            "event: stage",
            "id: 3",
            "data: {\"a\":",
            "data: 1}",
            "",
            "data: x",
            "",
        ];
        let evs: Vec<SseEvent> = lines.iter().filter_map(|l| p.feed_line(l)).collect();
        assert_eq!(evs.len(), 2);
        assert_eq!(evs[0].event, "stage");
        assert_eq!(evs[0].data, "{\"a\":\n1}");
        assert_eq!(evs[0].id.as_deref(), Some("3"));
        assert_eq!(evs[1].event, "message");
        assert_eq!(evs[1].id.as_deref(), Some("3"));
    }
    #[test]
    fn status_mapping() {
        assert_eq!(map_status(401, "").exit, Exit::Auth);
        assert_eq!(map_status(404, "").exit, Exit::NotFound);
        assert_eq!(map_status(503, "").exit, Exit::Unavailable);
        assert_eq!(map_status(422, "").exit, Exit::Rejected);
    }
}
