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
* Nothing is zero-knowledge. Every challenge uses `validity-classical-128`
  (`privacy: validity_only`, `FORMAL_ZK` not applicable), and formal-core has
  no zero-knowledge predicate. See the next section.

## What an admitted proof establishes

An `ADMITTED` result proves **validity**, that is, soundness of the claim,
for one fixed relation. It does not establish witness privacy, chain
authenticity or full NEAR execution. The binding text is the challenge's
`semantic_scope` (`restrictions`, `excludes`, `formal_spec`). The same
statement in contract form is in `docs/AGENT_CONTRACT.md` §6.1.

* **v1** (`near-transfer-receipt-v1` and its successors v1-1 … v1-4, claim
  `near-arena-claim-v1`, `spec/near-transfer-receipt-v1.md`). Proves
  `NearSpec.TransferV1.NearRelation`, the receipt-batch transition of a
  Transfer-receipt slice. Its output is the *projected* `slice_post_root`:
  the pre-state with only the account writes applied, so it is not the chunk's
  on-chain post-state root (spec §5). The pre-state root, the receipts
  commitment and the block context (height, gas price, gas limit) are
  **supplied commitments**. The proof binds the witness to them but does not
  show that they come from a real, finalized block. The challenge's `excludes`
  (`challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json`) are, verbatim:
  `block_finality`, `data_availability`, `receipt_inclusion`,
  `pre_state_root_on_chain`, `epoch_and_protocol_version_selection`,
  `onchain_post_state_root`, `transactions`, `signature_verification`,
  `function_calls_and_wasm`, `non_transfer_actions`,
  `implicit_account_creation`, `failure_paths_and_rollback`,
  `refund_receipt_inputs`, `data_postponed_yield_receipts`,
  `delayed_receipt_queue`, `congestion_control_and_buffering`,
  `bandwidth_scheduler`, `outgoing_receipts_root_and_routing`,
  `validator_updates_and_rewards`, `account_v2_global_contracts`,
  `receipt_enum_action_v2`, `other_protocol_versions`, `testnet_parameters`.
  So v1 does **not** establish block finality, receipt inclusion, that the
  pre-state root is on chain, data availability, or full chunk validation.
* **v2** (draft only: `challenges/drafts/near-transfer-receipt-v2.draft.json`,
  claim `near-arena-claim-v2`, `spec/near-transfer-receipt-v2.md`). Claims the
  actual runtime `post_state_root` (`ApplyResult.state_root`, including the
  bandwidth-scheduler write), but only for a restricted **single-shard**
  transition: the restrictions include `single_shard_layout`,
  `zero_congestion` and `no_bandwidth_requests`. It is explicitly **not**
  current multi-shard mainnet, and no current mainnet chunk is in its domain.
  The chain-anchoring exclusions of v1 (`block_finality`, `receipt_inclusion`,
  `pre_state_root_on_chain`, …) still apply.
* **Not claimed (future v3).** Full stateless-validator equivalence, meaning
  chain authentication of headers, roots and receipts, multi-shard execution
  and finality, is not claimed by any challenge.
* **Out-of-domain inputs are rejected, not passed off as verified.** The
  relation includes its domain predicate, so an out-of-domain claim has no
  valid proof. The oracle re-checks the domain without nearcore runtime code
  (`oracle/src/domain.rs`, `oracle/src/v2.rs` `check`). It never emits a claim
  for an out-of-domain case: the committed rejection cases in
  `oracle/fixtures/rejection/` (v1) and `oracle/fixtures/v2/rejection/` (v2)
  carry no claim, and the judge must not issue them as jobs. Before any
  sandbox runs, the worker's `RequestPin` (`runners/worker/src/jobs.rs`)
  checks each oracle request's encoding, statement id (scope),
  protocol version and chain id, the expected claim's encoding and statement,
  and `params.bin` (incl. the runtime-config digest) against the challenge,
  and fails the job closed on a mismatch.
* **Validity only, not zero knowledge.** Formal admission under
  `validity-classical-128` proves validity only. It does not establish
  witness privacy. This also covers succinct backends: `np-udr-stark`, SP1 and
  Plonky3 proofs are checked here as validity proofs, and their openings can
  reveal witness-derived values. A privacy claim would require a `FORMAL_ZK`
  gate discharged by a closed privacy theorem. formal-core does not define
  one yet, and no challenge requires it.

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
