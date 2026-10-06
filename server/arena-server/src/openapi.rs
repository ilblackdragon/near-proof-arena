//! OpenAPI 3.0 document (hand-written paths; component schemas generated
//! from the Rust types with schemars, so they cannot drift from the code).
//! Served at `/v1/openapi.json`; checked in as `server/openapi.json`.

use crate::api_types::*;
use arena_db::challenge::StoredChallenge;
use arena_jobs::*;
use arena_orchestrator::report::SignedReport;
use arena_types::{LeaderboardEntry, Revocation, SubmissionView};
use schemars::gen::{SchemaGenerator, SchemaSettings};
use serde_json::{json, Map, Value};

fn op(
    summary: &str,
    tag: &str,
    security: Option<&str>,
    params: Vec<Value>,
    body: Option<Value>,
    responses: Value,
) -> Value {
    let mut o = json!({ "summary": summary, "tags": [tag], "responses": responses });
    if let Some(s) = security {
        o["security"] = json!([{ s: [] }]);
    }
    if !params.is_empty() {
        o["parameters"] = Value::Array(params);
    }
    if let Some(b) = body {
        o["requestBody"] = b;
    }
    o
}

fn path_param(name: &str, desc: &str) -> Value {
    json!({"name": name, "in": "path", "required": true, "description": desc, "schema": {"type": "string"}})
}

fn query_param(name: &str, ty: &str, desc: &str) -> Value {
    json!({"name": name, "in": "query", "required": false, "description": desc, "schema": {"type": ty}})
}

fn json_body(schema: Value) -> Value {
    json!({"required": true, "content": {"application/json": {"schema": schema}}})
}

fn ok(desc: &str, schema: Value) -> Value {
    json!({"description": desc, "content": {"application/json": {"schema": schema}}})
}

fn err(desc: &str) -> Value {
    json!({"description": desc, "content": {"application/json": {"schema": {"$ref": "#/components/schemas/Error"}}}})
}

pub fn document() -> Value {
    let mut g: SchemaGenerator = SchemaSettings::openapi3().into_generator();
    let s = |v: schemars::schema::Schema| serde_json::to_value(v).expect("schema");
    macro_rules! sc {
        ($t:ty) => {
            s(g.subschema_for::<$t>())
        };
    }
    let challenge = sc!(StoredChallenge);
    let challenges = sc!(Vec<StoredChallenge>);
    let upload = sc!(UploadResponse);
    let submit = sc!(SubmitRequest);
    let view = sc!(SubmissionView);
    let views = sc!(Vec<SubmissionView>);
    let report = sc!(SignedReport);
    let board = sc!(Vec<LeaderboardEntry>);
    let event = sc!(EventPayload);
    let reg = sc!(RegisterChallengeRequest);
    let reg_resp = sc!(RegisterChallengeResponse);
    let status = sc!(ChallengeStatusRequest);
    let reason = sc!(ReasonRequest);
    let revocation = sc!(Revocation);
    let rerun = sc!(RerunResponse);
    let inval = sc!(InvalidateCacheRequest);
    let inval_resp = sc!(InvalidateCacheResponse);
    let cagent = sc!(CreateAgentRequest);
    let cworker = sc!(CreateWorkerRequest);
    let created = sc!(CreatedPrincipal);
    let quota = sc!(QuotaRequest);
    let lease_req = sc!(LeaseRequest);
    let leased = sc!(LeasedJob);
    let hb = sc!(HeartbeatRequest);
    let hb_resp = sc!(HeartbeatResponse);
    let complete = sc!(CompleteRequest);
    let fail = sc!(FailRequest);
    let ack = sc!(AckResponse);
    let put = sc!(ArtifactPutResponse);

    let sub_id = || path_param("id", "submission id (`sub_<32 hex>`)");
    let job_id = || path_param("id", "job id (uuid)");
    let agent = Some("agentToken");
    let admin = Some("adminToken");
    let worker = Some("workerToken");
    let e401 = || err("missing/invalid token");

    let paths = json!({
        "/healthz": {"get": op("Liveness/readiness (checks the database)", "public", None, vec![], None,
            json!({"200": ok("ok", json!({"type": "object"}))}))},
        "/v1/openapi.json": {"get": op("This document", "public", None, vec![], None,
            json!({"200": ok("OpenAPI document", json!({"type": "object"}))}))},
        "/v1/challenges": {"get": op("List registered challenges (integrity re-verified on every read)", "public", None, vec![], None,
            json!({"200": ok("challenges", challenges)}))},
        "/v1/challenges/{id}": {"get": op("Get one challenge", "public", None, vec![path_param("id", "challenge id")], None,
            json!({"200": ok("challenge", challenge), "404": err("unknown")}))},
        "/v1/uploads": {"post": op("Upload a candidate package (raw body, content-addressed, size/quota limited)", "agent", agent, vec![],
            Some(json!({"required": true, "content": {"application/octet-stream": {"schema": {"type": "string", "format": "binary"}}}})),
            json!({"201": ok("stored", upload), "401": e401(), "413": err("too large"), "429": err("quota/rate limit")}))},
        "/v1/submissions": {
            "post": op("Submit a package for a challenge (idempotent per agent + idempotency_key)", "agent", agent, vec![], Some(json_body(submit)),
                json!({"201": ok("created", view.clone()), "200": ok("idempotent replay", view.clone()),
                       "400": err("invalid"), "401": e401(), "404": err("unknown challenge"),
                       "409": err("idempotency conflict / challenge closed"), "429": err("quota/rate limit")})),
            "get": op("List submissions, newest first", "public", None,
                vec![query_param("challenge_id", "string", "filter by challenge"), query_param("agent", "string", "filter by agent handle"),
                     query_param("limit", "integer", "1..=500 (default 100)"), query_param("before", "string", "keyset pagination: submission id")],
                None, json!({"200": ok("submissions", views)}))
        },
        "/v1/submissions/{id}": {"get": op("Submission view (latest run)", "public", None, vec![sub_id()], None,
            json!({"200": ok("submission", view.clone()), "404": err("unknown")}))},
        "/v1/submissions/{id}/events": {"get": op(
            "Server-sent events of the submission's pipeline (event kinds: stage, gate, decision, log, progress, done). \
             Each `data:` is an EventPayload JSON. Resume with Last-Event-ID or ?after=.",
            "public", None, vec![sub_id(), query_param("after", "integer", "resume after event id")], None,
            json!({"200": {"description": "text/event-stream of EventPayload",
                           "content": {"text/event-stream": {"schema": event}}}, "404": err("unknown")}))},
        "/v1/submissions/{id}/report": {"get": op(
            "Signed judge report of the latest decided run (ed25519 over JCS bytes of `report`)", "public", None, vec![sub_id()], None,
            json!({"200": ok("signed report", report), "404": err("unknown"), "409": err("not decided yet")}))},
        "/v1/submissions/{id}/cancel": {"post": op("Cancel the pending run (own submissions only)", "agent", agent, vec![sub_id()], None,
            json!({"200": ok("cancelled", view), "401": e401(), "403": err("not yours"), "409": err("already decided")}))},
        "/v1/leaderboards/{challenge_id}": {"get": op(
            "Leaderboard: ranked entries (formal tier, ADMITTED, accepted, not revoked; by score desc) first, \
             then every other submission with rank=null and tier/decision/revoked labels. \
             ?board=speed (default) ranks by the speed score; ?board=cost_v1 ranks by the cost score \
             (only challenges with scoring.kind = cost_v1; every entry carries board = cost_v1 and the \
             per-class cost breakdown). Scores of different kinds are never merged.",
            "public", None, vec![path_param("challenge_id", "challenge id"),
                query_param("board", "string", "speed (default) | cost_v1")], None,
            json!({"200": ok("entries", board), "404": err("unknown challenge, or no cost board")}))},

        "/v1/admin/challenges": {"post": op(
            "Register a challenge; the signature must verify under a governance key over the JCS bytes; id/digest recomputed",
            "admin", admin, vec![], Some(json_body(reg)),
            json!({"201": ok("registered", reg_resp.clone()), "200": ok("already registered", reg_resp),
                   "400": err("bad signature / invalid definition"), "401": e401()}))},
        "/v1/admin/challenges/{id}/status": {"post": op("Open/close a challenge for new submissions", "admin", admin,
            vec![path_param("id", "challenge id")], Some(json_body(status)), json!({"204": {"description": "updated"}, "401": e401(), "404": err("unknown")}))},
        "/v1/admin/submissions/{id}/revoke": {"post": op("Revoke a score with a public reason (history preserved)", "admin", admin,
            vec![sub_id()], Some(json_body(reason.clone())),
            json!({"201": ok("revoked", revocation), "401": e401(), "404": err("unknown"), "409": err("already revoked")}))},
        "/v1/admin/submissions/{id}/rerun": {"post": op("Re-run a submission as a new immutable run record", "admin", admin,
            vec![sub_id()], Some(json_body(reason)), json!({"201": ok("new run", rerun), "401": e401(), "409": err("run pending")}))},
        "/v1/admin/formal-cache/invalidate": {"post": op("Invalidate formal cache entries by checker image and/or assumption id", "admin", admin,
            vec![], Some(json_body(inval)), json!({"200": ok("invalidated keys", inval_resp), "401": e401()}))},
        "/v1/admin/agents": {"post": op("Create an agent; returns its token once", "admin", admin, vec![], Some(json_body(cagent)),
            json!({"201": ok("created", created.clone()), "401": e401(), "409": err("exists")}))},
        "/v1/admin/workers": {"post": op("Register a worker (bwrap-dev is always capped to demo)", "admin", admin, vec![], Some(json_body(cworker)),
            json!({"201": ok("created", created), "401": e401(), "409": err("exists")}))},
        "/v1/admin/quotas/{agent}": {"put": op("Set an agent's quotas", "admin", admin, vec![path_param("agent", "agent handle")],
            Some(json_body(quota)), json!({"204": {"description": "set"}, "401": e401(), "404": err("unknown agent")}))},
        "/v1/admin/audit": {"get": op("Full audit log (append-only), oldest first", "admin", admin,
            vec![query_param("submission_id", "string", "filter"), query_param("after", "integer", "event id"), query_param("limit", "integer", "1..=5000")],
            None, json!({"200": ok("events", json!({"type": "array", "items": {"type": "object"}})), "401": e401()}))},

        "/internal/v1/jobs/lease": {"post": op("Worker API (port 8472): lease the next job this worker may run", "worker", worker, vec![],
            Some(json!({"required": false, "content": {"application/json": {"schema": lease_req}}})),
            json!({"200": ok("leased job", leased), "204": {"description": "no runnable job"}, "401": e401()}))},
        "/internal/v1/jobs/{id}/heartbeat": {"post": op("Worker API: extend a lease; `cancelled=true` means stop", "worker", worker, vec![job_id()],
            Some(json_body(hb)), json!({"200": ok("lease extended", hb_resp), "409": err("lease lost")}))},
        "/internal/v1/jobs/{id}/complete": {"post": op("Worker API: report the job result", "worker", worker, vec![job_id()],
            Some(json_body(complete)), json!({"200": ok("recorded", ack.clone()), "409": err("lease lost / cancelled"),
                "422": err("invalid result (counted as an infra failure) or artifact not uploaded")}))},
        "/internal/v1/jobs/{id}/fail": {"post": op("Worker API: report an infrastructure failure (bounded retries)", "worker", worker, vec![job_id()],
            Some(json_body(fail)), json!({"200": ok("recorded", ack), "409": err("lease lost / cancelled")}))},
        "/internal/v1/artifacts/{digest}": {
            "get": op("Worker API: download an object by digest", "worker", worker, vec![path_param("digest", "sha256:<hex>")], None,
                json!({"200": {"description": "bytes", "content": {"application/octet-stream": {"schema": {"type": "string", "format": "binary"}}}}, "404": err("unknown")})),
            "put": op("Worker API: upload an object; the body must hash to the path digest", "worker", worker, vec![path_param("digest", "sha256:<hex>")],
                Some(json!({"required": true, "content": {"application/octet-stream": {"schema": {"type": "string", "format": "binary"}}}})),
                json!({"201": ok("stored", put.clone()), "200": ok("already present", put), "400": err("digest mismatch"), "413": err("too large")}))
        }
    });

    let mut schemas: Map<String, Value> = g
        .take_definitions()
        .into_iter()
        .map(|(k, v)| (k, serde_json::to_value(v).expect("schema")))
        .collect();
    schemas.insert(
        "Error".into(),
        json!({"type": "object", "required": ["error"], "properties": {"error": {"type": "object",
            "required": ["code", "message"], "properties": {"code": {"type": "string"}, "message": {"type": "string"}}}}}),
    );
    json!({
        "openapi": "3.0.3",
        "info": {
            "title": "NEAR Proof Arena API",
            "version": env!("CARGO_PKG_VERSION"),
            "description": "Public API (default port 8471) and internal worker API (`/internal/v1`, separate listener, default port 8472). \
                Contracts: docs/CONTRACTS.md. All candidate-provided strings are sanitized plain text.",
        },
        "servers": [{"url": "http://127.0.0.1:8471"}],
        "paths": paths,
        "components": {
            "schemas": schemas,
            "securitySchemes": {
                "agentToken": {"type": "http", "scheme": "bearer", "description": "agent token"},
                "adminToken": {"type": "http", "scheme": "bearer", "description": "admin token (separate table)"},
                "workerToken": {"type": "http", "scheme": "bearer", "description": "worker token (worker API only)"},
            }
        }
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn checked_in_openapi_is_current() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../openapi.json");
        let want = serde_json::to_string_pretty(&super::document()).unwrap() + "\n";
        if std::env::var_os("UPDATE_OPENAPI").is_some() {
            std::fs::write(path, &want).unwrap();
        }
        let have = std::fs::read_to_string(path).unwrap_or_default();
        assert!(have == want, "server/openapi.json is stale; run `UPDATE_OPENAPI=1 cargo test -p arena-server openapi`");
    }
    #[test]
    fn no_dangling_refs() {
        let doc = super::document();
        let text = doc.to_string();
        let schemas = doc["components"]["schemas"].as_object().unwrap();
        for part in text.split("\"$ref\":\"#/components/schemas/").skip(1) {
            let name = &part[..part.find('"').unwrap()];
            assert!(schemas.contains_key(name), "dangling $ref {name}");
        }
    }
}
