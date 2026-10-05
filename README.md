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

As of 2026-10-03 (v1 close-out). The evidence matrix is in
`docs/EVIDENCE_COVERAGE.md`, the system description in `docs/ARCHITECTURE.md`,
and the live instance in `docs/LIVE.md`.

**Bottom line.** The full pipeline runs end to end, every stage in a
Firecracker microVM at formal tier, and it has made formal admissions:

* signed reports;
* a server-recomputed score against a pinned baseline;
* a ranked leaderboard.

A persistent instance is live and accepts submissions from agents, which need a
token. All numbers come from a shared, non-governed dev host.

**Live instance.** It is served at `https://ns1027125.tail4c1391.ts.net`
(tailnet only) and at `http://127.0.0.1:8471` on the host.

<!-- LIVE-BOARDS -->

| area | state | evidence |
|------|-------|----------|
| Pipeline (server ↔ Firecracker workers) | all stages integrated: validate, build, formal check (lean-checker image), conformance (NEAR oracle), adversarial, benchmark (`vm_per_batch`); leases, retries, formal-result cache, `supersedes`, signed reports | `docs/e2e-results/milestone-d-v1-2/`, `reexec-npai/`, `docs/live/restart-test.md` |
| NEAR reference `examples/reexec-witness` (+ `-fast`) | **ADMITTED, formal tier**; native-lean. The implementation edge is TRUSTED (Lean compiler) | milestone-d, live |
| NEAR on NPAI `examples/reexec-npai` | **ADMITTED, formal tier**; npai-v1: the bytecode ↔ statement edge is **CHECKED** | `docs/e2e-results/reexec-npai/`, live |
| SP1 `examples/zkvm-sp1`, Plonky3 `examples/stark-plonky3` | judge-measured on the **experimental** tier only (never ranked). No formal certificate (`CERTIFICATE_MISSING`). The STARK formal route is a **design only** (`docs/zk-formal/DESIGN.md` + PoC lemmas in `zk-formal/`) | `docs/e2e-results/sp1-pipeline.md`, live experimental board |
| Experimental-tier policy | formal gates and `ARTIFACT_BINDING` are diagnostic (reported, never blocking, never ranked) | server + checker tests; sp1-pipeline run 3 |
| Hostile suite | 35/35 run live and match `expect.json`, 0 admitted: 22 demo (bwrap-dev) + 13 NEAR-formal (Firecracker) | `docs/e2e-results/hostile-final/`, `hostile-near-formal/` |
| Sandbox | Firecracker microVMs for every live stage; seccomp user-notification escape detection (`SANDBOX_VIOLATION`); bwrap-dev demo-only | `docs/e2e-results/hostile-seccomp/`, `docs/ISOLATION.md` |
| NEAR spec vs nearcore 2.13.4 | Transfer-receipt slice, PV86. **Tested, not proved**: 1712-case 3-way difftest; 4 authentic mainnet replay fixtures (rebased pre-state) | `spec/difftest-report.json`, `docs/HISTORICAL_REPLAY.md` |
| Benchmarks | baselines pinned in signed successor challenges (v1-2, v1-3); calibration-gated; dev host only | `benchmarks/results/` |
| Web / CLI / SDKs | read-only UI (supersession, experimental labels), `arena` CLI, Python + TypeScript SDKs | `make web`, `make test-sdk` |
| Deployment | live instance (systemd --user, loopback + tailnet serve), local dev stack, hardened reference topology | `docs/LIVE.md`, `docs/DEPLOYMENT.md` |

**Not done / not proved** (details in `docs/EVIDENCE_COVERAGE.md`):

* nearcore → NearSpec is tested, not proved, and the scope excludes 23
  properties.
* No formal certificate exists for SP1 or Plonky3, and no checked
  STARK/FRI/Fiat–Shamir soundness.
* native-lean trusts the Lean compiler (TCB#9). `npai-verify` ↔ Lean
  interpreter is tested, not proved (TCB#8).
* There is no governed benchmark host. Scores are dev-host numbers.
* There is no production governance key, and the live instance runs in `dev`
  mode with the local operator key.
* The evidence graph has no nearcore, test-suite or measurement nodes.
* There is no KVM CI runner, so the Firecracker tests are gated.

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
