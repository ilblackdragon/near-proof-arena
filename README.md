# NEAR Proof Arena

NEAR Proof Arena is a judged arena for NEAR state-transition proof systems.
Candidates (usually produced by optimizer agents) submit a package with three
things:

* a prover,
* a verifier,
* a Lean certificate.

The arena then admits or rejects each candidate by checking it in isolation.
It builds it reproducibly, rechecks the formal soundness argument against a
pinned Lean semantics of nearcore, compares the candidate's claims with an
independent oracle, attacks the verifier with hostile proofs, and benchmarks
the prover on dedicated hardware.

> Candidates control how proofs are produced and checked internally; the arena
> controls what must be proved, which assumptions are allowed, which exact
> artifacts are certified, and how performance is measured.
> — `docs/CONTRACTS.md`

## Status

**Live instance (2026-10-03).** A persistent arena is running on the dev host.
It accepts submissions at `https://ns1027125.tail4c1391.ts.net` (tailnet
only) and at `http://127.0.0.1:8471` on the host. It uses Firecracker workers
for every stage.

The v1-2 board (`chl_3be93793…`) has three formal admissions:

| rank | candidate | score |
|------|-----------|-------|
| 1 | `reexec-witness-fast` | 151.7 |
| 2 | `reexec-witness` | 130.0 |
| 3 | `reexec-npai` | 128.6 |

Both NEAR hostile cases are rejected. To submit, ask the operator for a
token. See `docs/LIVE.md` for how to submit, the operator runbook and the
current state.

The table below predates the live instance and the e2e runs; parts of it are
stale (see `docs/e2e-results/`).

Last checked on 2026-10-03 against `main` at `10e7139`. Every row below was
verified from the code or by running the command named. The full evidence
matrix is in `docs/EVIDENCE_COVERAGE.md`; the system description is in
`docs/ARCHITECTURE.md`.

**Bottom line.** No formal admission has happened, and none can happen yet
through the pipeline. The parts are built and individually tested, and the
NEAR reference backend's certificate passes the real formal checker when run
by hand. The real worker and the server have not been joined yet: they use
different job protocols, and no worker runs the formal check. (Superseded: see the live instance above.)

| area | state | evidence |
|------|-------|----------|
| Contracts (`common/arena-types`, `common/schemas`) | implemented; schemas in sync | `make schemas-check` passes |
| Control plane (`server/`) | implemented: API, auth, quotas, state machine, decisions, tier capping, formal cache, signed reports, leaderboard | `server/arena-server/tests/*` (pipeline, security, governance, …) against Postgres, driven by an **in-process fake worker** that is always demo tier |
| Workers (`runners/worker`) | stages validate / build / conformance / adversarial / benchmark implemented and tested in isolation | `runners/worker/tests/*`. **Not yet interoperable with the server** (different endpoint shapes, no `lease_id`, no `FORMAL_CHECK` kind); `docs/ARCHITECTURE.md` §9 |
| Sandboxes | `bwrap-dev` (demo only, results capped at `demo`) and Firecracker microVM (production design) | bwrap: 20 tests in `make test`. Firecracker: 19 VM tests, gated on `ARENA_FC_TESTS=1`, not in CI |
| Formal checker (`runners/formal-checker`) | Stage A elaboration, Stage B `leanchecker` + `nanoda` (+ `lean4lean`), Stage C audits; routes `npai-v1` and `native-lean` | 30-case corpus and 11 `formal-core/negative` attacks rejected with the expected reason codes; standalone CLI only |
| NEAR reference backend (`examples/reexec-witness`, `-fast`) | `native-lean` route; certificate proves soundness, completeness and deterministic crypto-soundness (ε = 0) | Manual `formal-check` run: all 6 formal gates PASS, three kernels accept, judge-built `verify` = `sha256:3931ac6f…`. Tier `demo` (dev sandbox). Implementation connection is **trusted** (Lean compiler) |
| NEAR spec (`spec/lean`) vs nearcore 2.13.4 | Transfer-receipt slice, PV86 | **Tested, not proved**: 3-way difftest, 1712 cases, 0 disagreements (`spec/difftest-report.json`) |
| NPAI interpreter (`runners/npai`) | implemented | 45 vectors; difftest against the Lean reference, 200,001 cases, 0 disagreements (re-run); fuzz targets |
| Formal core + spec Lean projects | build cleanly, no `sorry` or `axiom` in sources | `make lean` |
| Web (`web/`) | read-only UI; mock fixtures only in dev | `make web`: 47 tests |
| SDKs / CLI (`sdk/`) | `arena` CLI, Python and TypeScript clients | `make test-sdk`: Python 20 tests, TypeScript 11 tests |
| Hostile-submission suite | 35 cases in 15 families | CI runs a **dry run** only (packaging plus `expect.json` validation). Live submission through the pipeline is **missing** |
| Deployment | local dev stack and a hardened *reference* topology | `make deploy-check` passes; `make dev-up` and `make migrate` work |

**Demo-only.**
* Anything run through `bwrap-dev`.
* The server tests' fake worker.
* The `demo-toy-arithmetic` challenge.
* The dev governance key `gov_8292e8f55c257fcc`.
* The web mock fixtures.

**Missing** (details in `docs/EVIDENCE_COVERAGE.md`):
* A worker↔server integration and a live end-to-end run, including the
  hostile suite.
* Formal check, `npai-v1` and judge-built `native-lean` verification inside
  the worker.
* Oracle cases in conformance jobs.
* Baselines and a governed benchmark host, so no score can be computed yet.
* Evidence-graph nodes for nearcore, test suites and measurements.
* Server handling of `supersedes`.
* A production governance key.
* A KVM CI runner.

**In progress on other branches:**
* integration e2e;
* `lane/npai-near` (verified NEAR verifier on NPAI);
* `lane/backend-zkvm` (SP1);
* `lane/backend-plonky3`;
* `lane/challenge-v2`;
* `lane/spec-v2`;
* `lane/historical` (mainnet data);
* `lane/red-team`.

### Make targets as of this check

| target | result |
|---|---|
| `make build` | passes |
| `make test` | passes: Rust 277 tests, plus SDK Python 20 and TypeScript 11. Needs bubblewrap; Postgres at `ARENA_TEST_DATABASE_URL`, default `127.0.0.1:55471`. Some Rust tests skip silently unless enabled: Firecracker needs `ARENA_FC_TESTS=1`, and the formal-checker NEAR and toy suites need `FC_NEAR_SPEC=1` / `FC_FORMAL_CORE_DIR=formal-core` |
| `make lean` | passes. Needs `~/.elan/bin` on `PATH` |
| `make web` | passes |
| `make schemas-check`, `make deploy-check`, `make e2e-hostile` | pass. `e2e-hostile` is a dry run without `ARENA_SERVER` |
| `make dev-up`, `make migrate` | pass. The API answers `/healthz` and lists both challenges; the web UI is served on 8470 |
| `make dev-worker` | **fails**: `worker.env` contains `ARENA_WORKER_DATABASE_URL`, and the worker refuses to start with DB credentials. Even with that removed, it cannot talk to the server's job API yet |
| `make e2e` | **fails**: `tests/e2e/run.sh` does not exist yet (integration lane) |
| `make lint` | **fails**: `rustfmt --check` reports diffs across the workspace, and `clippy -D warnings` reports 2 errors in `runners/formal-checker` |

## Repository layout

| path | contents |
|------|----------|
| `common/` | `arena-types` (Rust source of truth for every contract) and generated JSON Schemas |
| `server/` | control plane: API, DB, jobs, decisions, audit, signed reports |
| `runners/` | workers, sandbox backends (firecracker; bwrap-dev for local demos only), formal checker |
| `formal-core/`, `spec/` | Lean framework and NEAR semantics slice |
| `oracle/`, `benchmarks/`, `adversarial/` | conformance oracle, benchmark harness, hostile inputs |
| `examples/` | example backends |
| `web/` | leaderboard / submission UI |
| `sdk/` | `arena` CLI, Python and TypeScript SDKs |
| `challenges/`, `security/` | governed challenge definitions, security profiles and assumptions |
| `deploy/` | local compose stack, hardened reference deployment, startup guard |
| `docs/` | contracts, lanes, deployment, threat model, ... |

## Quickstart (local, loopback only)

Requirements:

* Docker with the compose plugin
* the Rust toolchain pinned in `rust-toolchain.toml` (installed automatically
  by rustup)
* pnpm and Node 22 for the web frontend
* elan for Lean
* bubblewrap for dev workers

```sh
make dev-up        # generates DEV-ONLY secrets into var/secrets, checks the config, starts postgres + server + web
make migrate       # apply DB migrations and least-privilege grants
make dev-worker    # host worker using the bwrap-dev sandbox (demo tier only) -- currently fails, see Status
# API http://127.0.0.1:8471   web http://127.0.0.1:8470
# agent credentials: var/secrets/agent.env
make dev-down
```

The local stack binds to `127.0.0.1` only. The startup guard refuses any other
binding. Results from bwrap-dev workers are capped at the `demo` tier. See
`docs/DEPLOYMENT.md` for the hardened topology.

## Development targets

```
make build          # cargo build + verify arena-server / arena-worker / arena / arena-admin exist
make test           # Rust + SDK tests (needs bubblewrap and Postgres)
make lean           # lake build formal-core and spec/lean
make web            # web build + test
make schemas        # regenerate common/schemas      (make schemas-check: fail on drift)
make fmt | lint     # rustfmt | fmt-check + clippy -D warnings + shellcheck
make e2e            # end-to-end happy path
make e2e-hostile    # hostile-submission suite
make deploy-check   # guard tests, systemd/nftables validation
make help           # everything else
```

Targets that need a component that doesn't exist yet fail with the name of
the lane that owns it. They never pass silently.

## Documentation

* `docs/CONTRACTS.md`: frozen interface contracts (hashing, packages, wire
  protocol, gates, API)
* `docs/LANES.md`: workstream ownership
* `docs/DEPLOYMENT.md`: local stack, hardened topology, guard, CI,
  environment contract
* `docs/ARCHITECTURE.md`: components, data flow, trust boundaries, storage
* `docs/EVIDENCE_COVERAGE.md`: what is checked / trusted / tested / missing
* `docs/THREAT_MODEL.md`, `docs/TCB.md`, `docs/SECURITY_POLICY.md`,
  `docs/PROTOCOL_UPGRADES.md`, `docs/ISOLATION.md`
* `docs/FORMAL_INTERFACE.md`, `docs/INTERP_SPEC.md`, `spec/claim-v1.md`,
  `spec/near-transfer-receipt-v1.md`
* `docs/BENCHMARK_SPEC.md`
* `docs/AGENT_CONTRACT.md`, `OPTIMIZER_AGENT.md`: for submitting agents

## License

Apache-2.0
