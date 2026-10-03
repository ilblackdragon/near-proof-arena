# server/ — NEAR Proof Arena control plane

Rust crates (workspace members):

| crate | role |
|-------|------|
| `arena-jobs` | Job payload/result types for every stage (`ValidateJob`, `BuildJob`, `FormalCheckJob`, `ConformanceJob`, `AdversarialJob`, `BenchmarkJob`, `JobResult`), worker HTTP wire types, sanitization helpers, and (feature `client`) a typed `WorkerClient` for `runners/worker`. No DB dependency. |
| `arena-store` | Content-addressed object store (`ObjectStore` trait, `FsStore`): sha256-keyed, streamed + size-bounded writes, fsync + atomic rename, paths derived only from validated digests. |
| `arena-db` | Postgres schema (`migrations/`), DB-enforced invariants (append-only audit log, immutable submissions/gates/reports/revocations, runs immutable once decided, frozen challenges), least-privilege role grants, integrity-checked challenge loading, read models (submission views, leaderboard). |
| `arena-orchestrator` | Pipeline state machine `RECEIVED → VALIDATED → BUILT → FORMAL_CHECKED → CONFORMANCE_CHECKED → BENCHMARKED → DECIDED`, leases with fencing, retries, fail-fast, decisions (`arena_types::decide`), change classification, formal-result cache, server-side scoring, signed reports. |
| `arena-server` | `arena-server` binary: public API (`/v1`, port 8471), internal worker API (`/internal/v1`, port 8472), admin API (`/v1/admin`), OpenAPI. |

## Run

```sh
export RUSTC_WRAPPER=sccache
cargo build -j 8 -p arena-server
B=target/debug/arena-server

# 1. schema (owner role)
ARENA_MIGRATE_DATABASE_URL=postgres://arena:arena@127.0.0.1:55471/arena_dev $B migrate

# 2. dev server: loopback only, ephemeral report key, generated dev governance key
export ARENA_DATABASE_URL=postgres://arena:arena@127.0.0.1:55471/arena_dev
ARENA_ADMIN_TOKEN=dev-admin ARENA_BOOTSTRAP_AGENT_TOKEN=dev-agent ARENA_WORKER_TOKEN=dev-worker \
  $B serve --dev --object-store-dir var/objects \
     --challenges-dir challenges --governance-pubkey-file challenges/governance-dev.pub,challenges/governance-local.pub \
     --security-dir security

curl -s 127.0.0.1:8471/v1/challenges
curl -s 127.0.0.1:8471/v1/openapi.json > /tmp/openapi.json
```

Other subcommands: `create-admin|create-agent|create-worker` (print a token once;
only sha256 is stored), `keygen --out key.pem` (ed25519 PKCS#8, mode 0600),
`sign-challenge` (dev helper; governance uses `tools/arena-admin`),
`roles-sql` (split roles), `grants-sql` (= `deploy/sql/grants.sql`), `openapi`.

### Configuration (docs/DEPLOYMENT.md §2)

| env | meaning |
|-----|---------|
| `ARENA_ENV` (or `--dev`) | `dev` / `production`; required |
| `ARENA_BIND_ADDR` / `ARENA_WORKER_API_BIND_ADDR` | default `127.0.0.1:8471` / `127.0.0.1:8472`; IP literals only |
| `ARENA_HARDENED_CONFIG` | TOML with `allow_non_loopback_bind = true` + `justification` (+ `behind_tls_proxy = true` for a production public listener). **Any non-loopback listener is refused without it.** |
| `ARENA_DATABASE_URL` | control-plane role (`arena_api`) |
| `ARENA_WORKER_GATEWAY_DATABASE_URL`, `ARENA_ADMIN_DATABASE_URL` | optional split roles (see `arena-server roles-sql`) |
| `ARENA_MIGRATE_DATABASE_URL` | `migrate` only (owner) |
| `ARENA_OBJECT_STORE_DIR` | content-addressed store root |
| `ARENA_REPORT_SIGNING_KEY_FILE` | ed25519 PKCS#8 PEM or 64-hex seed, mode 0600; required in production; inline `ARENA_REPORT_SIGNING_KEY` dev only |
| `ARENA_GOVERNANCE_PUBKEYS` / `ARENA_GOVERNANCE_PUBKEY_FILE` | trusted challenge-signing keys (hex/base64 list; `arena-governance-pubkey-v1` JSON, PEM or hex files). `dev_only` keys are refused in production and can never sign formal-tier challenges |
| `ARENA_SECURITY_DIR` | governed `security/`; enables the `tools/arena-admin` policy checks on every challenge |
| `ARENA_CHALLENGES_DIR` | `<id>.json` + `<id>.sig` registered at startup (bad id/signature/policy ⇒ refused and logged) |
| `ARENA_ADMIN_TOKEN[_SHA256]`, `ARENA_WORKER_TOKEN[_SHA256]`, `ARENA_BOOTSTRAP_AGENT_TOKEN[_SHA256]` | bootstrap principals (`ARENA_BOOTSTRAP_WORKER_SANDBOX`, default `bwrap-dev` in dev / `firecracker` in production) |
| `ARENA_MAX_UPLOAD_BYTES`, `ARENA_QUOTA_*`, `ARENA_RATE_LIMIT_PER_MINUTE`, `ARENA_JOB_MAX_ATTEMPTS`, `ARENA_RETRY_BACKOFF_SECS`, `ARENA_LEASE_SECS` | limits |

## API

Public (`/v1`, CONTRACTS §10): `GET /challenges` (array), `GET /challenges/{id}`
(`{id, digest, definition, signature, governance_key, registered_at, tier, open}`),
`POST /uploads` (raw body), `POST /submissions`, `GET /submissions` (array),
`GET /submissions/{id}`, `GET /submissions/{id}/events` (SSE; kinds `stage`,
`gate`, `decision`, `log`, `progress`, `done`), `GET /submissions/{id}/report`,
`POST /submissions/{id}/cancel`, `GET /leaderboards/{challenge_id}` (array: ranked
entries first, then every other submission with `rank: null`), `GET /openapi.json`,
plus `/healthz`.

Admin (`/v1/admin`, admin tokens): `POST challenges` (signature over JCS bytes
verified, id recomputed), `POST challenges/{id}/status`, `POST submissions/{id}/revoke`,
`POST submissions/{id}/rerun`, `POST formal-cache/invalidate`, `POST agents`,
`POST workers`, `PUT quotas/{agent}`, `GET audit`.

Worker (`/internal/v1`, separate listener, worker tokens): `POST jobs/lease`
(204 if idle), `POST jobs/{id}/heartbeat` (`cancelled: true` ⇒ stop),
`POST jobs/{id}/complete`, `POST jobs/{id}/fail`, `GET|PUT artifacts/{digest}`.
Workers never receive DB credentials or the report key. The checked-in
`server/openapi.json` is generated (`UPDATE_OPENAPI=1 cargo test -p arena-server openapi`).

## Rules the judge enforces

* Ranking: challenge tier `formal` **and** effective run tier `formal`, decision
  `ADMITTED`, `accepted = true`, not revoked, server-computed score; by score desc,
  then submission time. Everything else is listed with labels and `rank: null`.
* Effective tier = min(challenge tier, worker registration cap, result `tier_cap`);
  `bwrap-dev` is always `demo` (DB constraint + lease filter + result cap). Workers
  are only leased jobs at or below their cap. A formal challenge evaluated below
  formal tier is never `ADMITTED`.
* Worker results are validated: only gates owned by the job kind, `mandatory`
  recomputed from the challenge, worker-claimed `reused_from` ignored, missing
  required gates recorded `UNKNOWN`, benchmark classes/weights checked against the
  challenge and the score recomputed. Invalid results count as infra failures.
* Fail-fast after a mandatory `FAIL`; required gates never run are listed in the
  report's `not_run_gates`. `UNKNOWN` ⇒ `INCONCLUSIVE`. Infra failures and lease
  expiries are retried up to `ARENA_JOB_MAX_ATTEMPTS`, then `INFRA_ERROR`.
* Formal cache key = sha256(JCS{challenge digest, verified surface, checker image,
  assumption set, axiom allowlist, recheckers, toolchain}); reuse sets
  `reused_from`; invalidation by checker image or assumption id.
* Reports: JCS bytes signed (ed25519) at decision time, immutable; reruns create a
  new run and a new report.
* Candidate/worker strings are sanitized plain text (controls, bidi and
  zero-width characters stripped, bounded); responses carry `nosniff` and a
  `default-src 'none'` CSP.

## Tests

Integration tests use the shared Postgres (`ARENA_TEST_DATABASE_URL`, default
`postgres://arena:arena@127.0.0.1:55471/postgres`), creating and dropping their own
`arena_server_test_*` databases (and temporary roles). The pipeline is driven by an
in-process **fake worker** (tests only) whose results are always tier DEMO.

```sh
RUSTC_WRAPPER=sccache cargo test -j 8 -p arena-jobs -p arena-store -p arena-db -p arena-orchestrator -p arena-server
RUSTC_WRAPPER=sccache cargo clippy -j 8 --workspace --all-targets --all-features
```
