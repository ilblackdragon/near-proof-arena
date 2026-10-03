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

<!-- INTEGRATOR: fill this section from evidence (CI runs, e2e results). Do
not claim a hosted deployment, ranked board, or formal admission that has not
actually happened. -->

| area | state | evidence |
|------|-------|----------|
| Frozen contracts (`common/arena-types`, `common/schemas`) | _TBD_ | |
| Control plane (`server/`) | _TBD_ | |
| Workers / sandbox (`runners/`) | _TBD_ | |
| Formal core + NEAR spec (`formal-core/`, `spec/`) | _TBD_ | |
| Web (`web/`) | _TBD_ | |
| SDKs / CLI (`sdk/`) | _TBD_ | |
| Hostile-submission e2e | _TBD_ | |
| Deployment | Local dev stack and a hardened *reference* topology (`deploy/`). **No hosted instance.** | `make deploy-check` |

Known limitations: _TBD by the integrator._

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
make dev-worker    # host worker using the bwrap-dev sandbox (demo tier only)
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
make test           # Rust + SDK tests
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

## License

Apache-2.0
