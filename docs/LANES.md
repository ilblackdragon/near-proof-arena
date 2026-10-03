# Workstream lanes (ownership)

Each lane owns its directories. Touch other lanes' files only through the
contracts in `docs/CONTRACTS.md` / `common/arena-types`. If a contract change
is needed, make the minimal additive change in `common/arena-types`, describe
it in `docs/CHANGELOG-contracts.md`, and call it out in your final report.

| lane | owns |
|------|------|
| server | `server/` (control plane, DB, jobs, API, decisions, audit, reports) |
| runners-core | `runners/sandbox`, `runners/archive`, `runners/worker` (build/test/bench workers, bwrap-dev) |
| runners-vm | `runners/firecracker`, `deploy/images/` (microVM backend, rootfs), GPU route doc |
| formal-core | `formal-core/` Lean framework (admission theorem type, games, assumptions) |
| formal-checker | `runners/formal-checker/` (isolated elaboration, export, recheck, axiom audit) |
| spec-oracle | `spec/`, `oracle/` (Lean NEAR semantics slice, claim encoding, nearcore oracle, fixtures) |
| backend-* | `examples/<backend>/` |
| bench | `benchmarks/` |
| web | `web/` |
| sdk | `sdk/`, `docs/AGENT_CONTRACT.md`, `OPTIMIZER_AGENT.md` |
| adversarial | `adversarial/` |
| governance | `challenges/`, `security/`, `docs/{THREAT_MODEL,TCB,SECURITY_POLICY,PROTOCOL_UPGRADES}.md`, `tools/upgrade-monitor` |
| deploy-ci | `deploy/` (except images), `.github/`, `Makefile` |

Shared infra on this host:
* Postgres 17 at `postgres://arena:arena@127.0.0.1:55471/<db>`; create your
  own database (e.g. `arena_<lane>`) for tests. Never drop others' databases.
* Pinned nearcore checkout: `/data/illia/nearproof-deps/nearcore` (tag 2.13.4).
* No GPU on this host. 32 cores; be considerate: `cargo build -j 8`.
* `/dev/kvm` is not accessible to the user directly, but the user is in the
  `docker` group (so a container with `--device /dev/kvm` can use KVM).
* Use `RUSTC_WRAPPER=sccache` to share compilation.
