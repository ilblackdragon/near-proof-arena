# NEAR Proof Arena — handover (updated 2026-10-09)

This is for the next lead agent. Read it first. The raw working log for 2026-10-07 to 2026-10-09 (≈6,500 lines) now lives in `docs/logs/v3-progress-log-2026-10.md`. Use it only for evidence lookup.

**Rule for this file:** keep it short and current. Append progress to `docs/logs/`, not here.

## 0. Goal and standing user directives

**Goal.** A self-hostable arena where candidates submit NEAR state-transition provers. Each submission comes with a machine-checked Lean certificate. The judge independently builds the submission, checks it formally (fixed trusted root), tests it, and benchmarks it.

**Current target.** A **succinct proof of a NEAR chunk state transition, with a formal proof of correctness.** It must be a drop-in replacement for the stateless validator's `validate_chunk_state_witness`.

User directives (binding):
* **Don't shortcut.**
  * Use explicit, decidable domain conditions rather than hidden assumptions.
  * Prove things where possible; don't settle for testing alone.
  * Never loosen measurement rules to make something pass.
* **Proof size and verify time are first-class.** Proofs must be succinct.
* **One challenge.** `near-chunk-v3` covers the whole chunk transition with coverage tiers D0a < D0 < D1 < D2 < D3α. Do not create one challenge per domain.
* **The strategic value of ZK** is one proof across *all* shards, which standard validator hardware cannot re-execute. Single-proof capacity (`G_α`) is the key metric.
* **Recursion: R5.** No proof composition and no bounded R1. Single-proof capacity is raised through the prover, table and verifier levers listed in `docs/requirements/D3_WASM_REQUIREMENTS.md` §2.4.
* **Decisions already taken by the user:**
  * Price model: N_v = 50 validators **per shard**.
  * B0 = 2.0 MB for D0a.
  * A8 is in RelD0a.
  * A9 and A10 are in RelD0a (2026-10-09): ChaCha words drawn by all scheduler runs ≤ W0 = 770,000, and every used source Merkle path ≤ Dp0 = 32 items.
  * D3 error kinds count as one failure; floats come in a later stage; block facts are derived from headers.
* **Security and operations:**
  * Repo: GitHub `ilblackdragon/near-proof-arena`, private.
  * Remote access is through `tailscale serve` only, never funnel. Everything binds to loopback.
  * Keys and secrets live outside the repo. Never print keys, env files or env vars.
  * Never modify signed challenges (`challenges/chl_*.json`), the frozen `oracle/v3`, or any pinned file. `make pin-check` must pass.

## 1. Host rules (the host OOM-crashed twice; follow these strictly)

* **Run heavy builds through the wrapper:** `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy <cmd>`.
  * The wrapper is a systemd scope in `zkbuild.slice` with a 48G cap, and `mem-watchdog` runs alongside.
  * Use `HEAVY_MEM=32G` only for the D2 kernel-eval proofs.
  * At most about 3 lanes, and at most 2 heavy builds per lane at a time.
* **CPUs 0-7 and 16-23 are reserved for the live benchmark worker w1.**
  * Stop w1 only in short, logged windows with an empty queue (`docs/LIVE.md` §5f).
  * If a run is interrupted, restart w1.
* **Disk:** `/` is at **96%** and `/data` at **92%**.
  * Delete merged worktrees and their `target/` dirs.
  * Session scratchpads under `/tmp/claude-1002/...` are large (`lean`, `npai-e2e`, `elan` ≈ 25 GB) and can go once you have confirmed nothing needs them.
* **Merging:**
  * Use explicit `git add <paths>` only; other agents work in worktrees. Check `git status` before committing.
  * Merge lanes to main **before** installing live.
  * Run `cargo fmt --check`, clippy with `-D warnings`, the affected tests and `make pin-check` before pushing.
  * Commit trailer: `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.
* **Worktrees:** lanes live in `/data/illia/nearproof-wt/<lane>`, one per concurrent agent. Never share a worktree between agents.
* **Helper:** `/data/illia/nearproof-deps/bin/resolve-members.py` resolves `Cargo.toml` member conflicts.


## 2. Repository state

* **main** contains everything below. It was merged from `integration/v3-20261009` on 2026-10-09, which combined:
  * `lane/v3-air`, `lane/v3-hpl`, `lane/v3-assembly`, `lane/v3-qvals`, `lane/v3-public`;
  * `lane/v3-d3`;
  * `codex/near-state-proof-20261008`, which was recovered from the local bundle `checkpoints/near-state-proof-20261008.bundle` because the codex sandbox could not push;
  * the uncommitted work that sat in the main checkout: about 160 newer files, the web Research page and the PR template.
* **Merge checks:**
  * Conflicts were limited to import lists, axiom-audit files and status docs. They were resolved by taking the union, with duplicates removed.
  * Every `import ZkFormal.*` resolves.
  * No new `sorry`, `axiom`, `native_decide` or `implemented_by`.
  * `make pin-check` OK. Rust: fmt, clippy `-D warnings` and 355 workspace tests pass.
  * Lean build of all ZkFormal modules: see §6.
* **Not merged, on purpose:** two old WIP commits that don't build, kept on origin:
  * `lane/v3-trie-h` `1d8b2f12`;
  * `lane/v3-rcpt-h` `4ae51a13`.
* **Live arena:** unchanged since 2026-10-06 (`docs/LIVE.md`). Nothing new was signed or deployed.

## 3. What is DONE

* **v1 arena: milestones A–D, live.** NPAI (CHECKED) and native-lean routes. The succinct STARK np-udr-stark is formally admitted; it is a validity proof, not zero-knowledge.
* **Cost scoring:**
  * governed price model `pm-near-mainnet-2026q4@v2` (N_v = 50 per shard);
  * paired baseline control and pinned calibration (bench-spec-v1.6);
  * v1-7 cost board live.
* **v3 D0 (`chl_4b431651…`):** the proven normal-form reference and its fast child (rank 1) are ADMITTED.
* **v3 spec ladder:** D1, D2 and D3α, each difftested three ways (nearcore / Lean / Python) with 0 disagreements. RelD0a has B0 = 2.0 MB and A1/A2/canon0f/A7/A8.
* **Read-logging checker** (`checkD2L_eq`, `checkD3L_eq`, plus the stack-safe WASM loop):
  * proved equal to the trusted checker;
  * D3: the 115,284 saved results reproduce;
  * fresh D2 regressions recorded over both the D2 corpus and the D1 corpus;
  * WASM and trie harness parity recorded.
* **D3α read-set reference** (`examples/reexec-v3-d3`):
  * complete read-set normalisation is proved, with a single run;
  * strict public and held-out worker gates pass;
  * all 3,062 mutations rejected, including unread-value and unread-code injection.

## 4. Stream A: unified challenge `near-chunk-v3`

**Design.** One challenge whose statement is `RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3`. Candidates declare a tier, D0a < D0 < D1 < D2 < D3α, and may abstain outside it. Ranking is by tier, then cost. See `CONTRACTS.md` §11 and `BENCHMARK_SPEC.md` §17.
* **Draft:** `challenges/drafts/near-chunk-v3.draft.json`, unsigned.
* **Class weights:** ASSUMED until a mainnet replay measures them.
* **Known limitation:** four transcriptions are trusted. The follow-up is to make `Rel_Dk := RelD3 ∧ InDk`.

**Blockers, in order:**
1. **lean4lean fails on the D3α reference.** It hits a recursion failure (`memFill`), while leanchecker and nanoda pass. This blocks formal admission.
   * Options: proof-only refactoring of the offending terms (experiments are preserved under `/data/illia/nearproof-deps/validation/`), or an upstream fix to lean4lean.
   * Do not weaken the three-checker policy.
2. **The D0a tier needs real workload-class coverage in the draft.** An empty class list would silently allow abstention on every input.
3. **Domain bounds A9/A10** (decided by the user on 2026-10-09) are implemented on `lane/v3-domain-bounds`, which is not merged yet. Merge it before the freeze.
4. **Freeze, then measure, then release:**
   * freeze once;
   * run the joint w1 paired-baseline window with the cost tooling;
   * sign, register and deploy;
   * submit the reference (expect ADMITTED) and `near-v3-d3-lenient-codes` (expect REJECTED);
   * record the results.

## 5. Stream B: succinct D0a STARK (np-udr-stark-v2), the critical path

**Location:** `zk-formal/ZkFormal/NearV3/` (Assembly, Candidates, Rcpt, Qv, Render, Sched, Extract, Link, Public) and `ZkFormal/V3`, `ZkFormal/Size`.
* About 5,000 modules. Integration target: `ZkFormal.V3.Integration`.
* About 2,400 axiom-audit files in `zk-formal/test/`. Run each with `lake env lean test/<file>`.

**Assembly lane (`agent/v3-assembly`, 2026-10-09):** the assembled AIR and the admission
certificate now exist; see `docs/zk-formal/STATUS-V3-ASSEMBLY.md` and
`zk-formal/ZkFormal/NearV3/Assembly/{NearAir,NearAirCheck,NearAirSize,HintCodec,NearAdmission}.lean`.
* `nearAirV3` (25 tables, `pubSegs = Public.preparedSegments`), `nearAirV3_wf`, `nearAirV3_npOkPg`.
* Aligned size bound at `auxGroup = 2`: `6,276,897` B (`nearV3_size`).
* `nearV3_admission` / `nearV3_admission_with_extract_b`: `AdmissionStatement` of
  `near-chunk-validation-d0-stark`, with the soundness premise discharged from `ExtractV3Stmt`
  through the proved `factorSound`.
* The A9/A10 domain decisions (`W0 = 770,000`, `Dp0 = 32`) are merged from `lane/v3-domain-bounds`.
* Still open: `ExtractV3Stmt`, `RenderV3Stmt`, `AlignedV3Stmt`, `FitsV3Stmt`, the Rust prover.

**Parallel work packages for other agents.**  The assembly layer is frozen
(`nearAirV3`, its table indices, and the three statements).  Each package below is
self-contained and plugs into a fixed interface; full detail in
`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §5.  One worktree + lane branch per agent;
integrate to `agent/v3-assembly`.

| pkg | item | deliverable / file | deps |
|---|---|---|---|
| **Rust prover** | 8 | `np-udr-stark-v2` Rust prover + candidate package (`examples/np-udr-stark-v2/`, new). AIR/buses/public segments are frozen; export format in `docs/zk-formal/FORMATS.md`. **Fully independent — start now.** | none |
| **rcpt-view** | 2 | prove `RcptV3ViewStmt` (`Rcpt/Extract/RcptView.lean:215`) | none |
| **srcp-render** | 2 | `srcpV3` render (`Rcpt/Render/Srcp/**`) | none |
| **qv-render** | 2 | `qvV3` render (`Qv/Candidates/**`) | none |
| **ups-render** | 2 | `upsV3` render M7d (`Render/Ups/**`) | none |
| **link** | 3 | prove `LinkV3Stmt` (`Assembly/LinkV3.lean`) ⇒ `ExtractV3Stmt`; per-table `*Local` and `*ViewStmt` wiring is fixed in `Assembly/ExtractV3.lean`. | views (most exist) |
| **heights** | 5 | `FitsV3Stmt`/`honestTrace_fits` for `nearAirV3` from `InD0a`; `Sched/Complete/Height.lean` exists. | views |
| **render-assembly** | 4 | `renderV3` + `RenderV3Stmt` + `AlignedV3Stmt` | renders |
| **governance** | 9 | D0a tier + weights, freeze, sign/register/deploy, judge run | Rust prover |

Critical path: `link` → `render-assembly` → governance.  The **Rust prover** (item 8)
is on no critical path and can proceed in parallel immediately.

**Done:**
* soundness views and links for the trie, scheduler, ChaCha and receipts;
* ChaCha completeness;
* memory constraints (29/29);
* field constraints (62/62);
* R1 indexed public segments (protocol);
* many native-execution extraction bridges (prepared IDs, SDL, codec, raw frames, queue traffic);
* the roll-in aligned size bound. The padded two-SHA model is 6,176,224 B, leaving 917,367 B under 8 MiB after the maximum hint. This holds only if padding that preserves `HoldsP` is constructed.
* the domain bounds (`lane/v3-domain-bounds`): `srcpV3` at `maxLog` 22 under A10, and the ChaCha lane row bound at W0. The size margin is unchanged.

**Not done:**
* the global assembled AIR `nearAirV3`;
* `FactorSound` / `FactorComplete` against `checkD0a`;
* `honestTrace_fits`;
* the admission certificate;
* the padding construction;
* the remaining byte and receipt-render constraints;
* the Rust v2 prover;
* any real judge run;
* `Chacha.Table.maxLog` 21 → 22, which the A9 lane needs. It is held because four candidate families would exceed the 2^36 fingerprint budget; see STATUS-V3-AIR §5.

The work so far is an extensive collection of conditional lemmas. The end-to-end theorem does not exist yet.

**Hard feasibility risk: judge elaboration budget.** A clean, serial elaboration diagnostic hit the 1,800 s total cutoff after 927 of 1,110 modules (`/data/illia/nearproof-deps/validation/v3-clean-elaboration-20261007-attempt2`). The tree is now about 5,000 modules, so the final certificate must be a pruned closure.
* Measure its clean elaboration early.
* If it cannot fit, raising the budget is a decision for the user, made with numbers. Do not change it silently.

**Quality notes for whoever continues:**
* Prefer converging on the top-level theorem over adding more `Candidates/*` lemmas.
* Each new module should sit on the path to `FactorSound` / `FactorComplete`.
* Keep the guarded axiom audits.

## 6. Verification status of this merge

The Lean build of all ZkFormal modules on the integration branch is filled in below once it finishes.

* **Lean build (2026-10-09):** `lake build` over all 5,102 ZkFormal targets on the integration branch. Every module builds except `NearV3/Candidates/ProcActualGrantOperands`.
  * That file is an uncommitted WIP file from the main checkout: it has typeclass errors, and nothing imports it.
  * It was left out of main. It is still untracked in `/data/illia/nearproof`, so finish it or delete it.
* **Not re-run in this merge:**
  * the about 2,400 audit files in `zk-formal/test/`, which are run individually;
  * the D3 reference check-local;
  * the difftests.

  Their last results are in `docs/e2e-results/` and in the log.

## 7. Process rules learned (2026-10-07 to 2026-10-09)

* **Push every checkpoint to origin.** If the sandbox has no network, say so in the final report. Do not leave work only in bundles or as untracked files in the main checkout.
* **One worktree per agent.** Never work in `/data/illia/nearproof` itself; integrate on an `integration/*` branch.
* **Progress notes go to `docs/logs/`, not this file.** Don't make commits that only touch the log on main.
* **Never overwrite another lane's module.** Rename instead; this already caused one collision, which was caught and restored.

## 8. Smaller follow-ups

* **Succinct badge:** 2 MiB / 50 ms, log-log growth test. Not implemented.
* **Mainnet replay:** real class weights and a measured `G_α`.
* **Independence of the clean-room Python VM:** it was tuned against nearcore black-box runs.
* **Future challenges:**
  * 1 Pgas as a single STARK, which needs Goldilocks, a distributed prover and precompiles;
  * a cross-shard whole-block proof (`BENCHMARK_SPEC.md` §14.11).
* **Disk:** `/` about 96%, `/data` about 87%. Remove merged worktrees and their build dirs once they are clean and pushed.

## 9. Key documents

| Topic | Documents |
|---|---|
| Architecture and contracts | `ARCHITECTURE.md`, `CONTRACTS.md`, `CHANGELOG-contracts.md` |
| Security model | `TCB.md`, `THREAT_MODEL.md`, `SECURITY_POLICY.md` |
| Benchmarking and operation | `BENCHMARK_SPEC.md`, `LIVE.md` |
| v3 domain specs | `spec/near-chunk-validation-{d0,v0a,d1,d2,d3}.md` |
| Requirements | `docs/requirements/` |
| ZK formalisation | `docs/zk-formal/` (DESIGN, V3-D0-DESIGN, STATUS-*) |
| Lane status files | `STATUS-V3-AIR.md`, `STATUS-V3-D3.md` |
| Raw log | `docs/logs/v3-progress-log-2026-10.md` |
