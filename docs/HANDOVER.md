# NEAR Proof Arena — handover (2026-10-07)

This is for the next lead agent. Read this first, then the two lane status files named in §3 and §4.

## Resumption plan (2026-10-07)

Main is `048fc45d`; the D0a spec merge is already present. Treat the older lane
status files' requests to merge it, and their receipt-lane pause claims, as stale.
Work proceeds in the following order, retaining the release gates below:

1. **Restore checked baselines.** Build `ZkFormal` on `lane/v3-air`, then repair
   `Logged/WasmRun.lean` on `lane/v3-d3` and rebuild the logged checker. Check the
   transitive theorem axioms and reproduce the formerly stack-overflowing case.
2. **Validate the logged reference.** Run all D3 corpora and the D2/D1/D0
   regressions, WASM harness and trie traces. Implement the exact read-set normal
   form in the D3 reference and run check-local, including unread-value/code
   injection. Record full-case counts and missing results as failures.
3. **Finish the succinct prover.** Resume receipt proofs; finish trie/scheduler
   completeness, indexed public segments, roll-in alignment, assembly and the
   Rust v2 prover. Keep B0 at 2,000,000 and the existing proof-size cap; prove
   the size savings before relying on them. Measure clean elaboration and real
   judge verification before declaring admission feasible.
4. **Resolve domain choices before freezing.** The ChaCha word bound and source
   Merkle-path budget remain user decisions. Until resolved, keep capacity
   statements conditional and do not freeze a newly narrowed domain.
5. **Release only after the gates pass.** Add D0a to the unified tier ladder,
   merge tested lanes, freeze once, measure the paired baseline in a logged w1
   window, then sign/register/deploy and verify reference admission and hostile
   rejection. Preserve signed challenges and all existing pinned files.

Recovery completed on the two lanes (not merged to main):
`lane/v3-d3` at `77b844e0`; `lane/v3-air` at `d455885a`.
* **D3:** repaired and kernel-checked the stack-safe logged loop; built the
  checker and D0a tier (195 jobs). All 115,284 D3 cases agree with the saved
  original Lean and independent Python baselines and nearcore expectations;
  all 1,720 public-fixture comparisons agree in verdict and reason. Saved
  baselines were reused, not rerun. Eight guarded axiom audits and seven
  regression-driver tests pass. Full D1/D2 corpora, WASM/trie harnesses and the
  read-set reference remain next. Evidence: lane file
  `docs/e2e-results/v3-logged-checker/report.json`.
* **AIR:** merged the saved receipt lane at `8c40110e`. The default `ZkFormal`
  root missed hundreds of proof modules. New target
  `lake build ZkFormal.V3.Integration` covers 369 additional modules and passes
  all 1,089 jobs. It exposed and fixed a stale upsV3 width (186 → 187), adding
  928 bytes to each synthetic size bound. Kernel checks now compare all trie,
  scheduler and receipt shapes; seven guarded axiom audits pass. This is an
  incremental integration check, not a clean judge-budget measurement or a
  completed STARK. Evidence: lane file `docs/e2e-results/v3-integration/report.json`.
* **Domain:** the conditional W = 770,000 capacity theorem needs ChaCha
  maxLog 22 (4,141,411 padded rows), whereas the current table uses 21.
  The W and source-path choices remain unanswered; no domain or cap changed.
* Full validation artifacts are preserved at
  `/data/illia/nearproof-deps/validation/v3-recovery-20261007-023334`.
  No live worker was stopped, and no challenge was frozen, signed or deployed.

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

## 2. What is DONE (on main, `5ce7c42e`)

* **v1 arena: milestones A–D complete and live.**
  * Firecracker sandboxing, a formal checker with three kernel rechecks and audits, the hostile suite and signed reports.
  * The NPAI (CHECKED) and native-lean routes.
  * Succinct STARK np-udr-stark (L1–L8), formally admitted. It is a validity proof, **not** zero-knowledge.
* **Live instance (`docs/LIVE.md`).**
  * Runs from `/data/illia/nearproof-live` as systemd user units `arena-live.target`.
  * Reachable over the tailnet at `https://ns1027125.tail4c1391.ts.net`.
  * Deploy only with `arena-live build` followed by `arena-live install`. Install refuses stale or dirty builds.
  * The calibration binary at `bin/arena-calibrate` is not copied by install; keep it in place.
* **Cost scoring.**
  * Governed price model `pm-near-mainnet-2026q4@v2`.
  * Paired baseline control and a pinned calibration binary (bench-spec-v1.6, contracts v1.8).
  * Verify time is scored as the lower quartile of 25 runs.
  * The v1-7 challenge `chl_93d98910…` has a live cost board.
* **v3 D0.**
  * Challenge `chl_4b431651…`, speed-scored.
  * The proven normal-form reference (4.5) and its fast prover-only child (104.6, rank 1) are ADMITTED.
  * The old canonical-only reference has been re-run and is now REJECTED.
* **v3 spec ladder.** Each domain was difftested three ways: nearcore vs Lean vs independent Python.

  | Domain | Cases | Disagreements |
  |---|---|---|
  | D1 | 53,048 | 0 |
  | D2 | 67,384 | 0 |
  | D3α (WASM, `G_α` = 3.45 Tgas) | 115,284 | 0 |

* **RelD0a** (B0 = 2.0 MB, A1/A2/canon0f/A7/A8) and `relD0a_relD0`: merged at `5ce7c42e`. Spec: `spec/near-chunk-validation-v0a.md`.
* **Research closed:** recursion (`docs/research/recursion-summary.md`, R5). The cross-shard plan is in `docs/BENCHMARK_SPEC.md` §14.11.

## 3. Stream A: unified challenge `near-chunk-v3`

Branch `lane/v3-d3`, worktree `nearproof-wt/v3-d3`. **Read `STATUS-V3-D3.md` at the lane root.**

**Recovery builds and audits pass.** The open `runUntil_spec` goals and long-run stack overflow are fixed; see the resumption evidence above.

* **Design.**
  * Statement: `RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3`, with `rel_mono` and `sound_lift`.
  * Candidates declare a tier and may abstain with UNSUPPORTED (prove exit code 3). Ranking is by tier, then cost.
  * Documented in `docs/CONTRACTS.md` §11 (contracts v1.7+) and `docs/BENCHMARK_SPEC.md` §17.
  * The coverage code is on main.
  * Draft: `challenges/drafts/near-chunk-v3.draft.json` on the lane, unsigned id `chl_b44dc871…`. Class weights are **ASSUMED** until a mainnet replay measures them.
* **Known limitation.** The union statement means four transcriptions are trusted. The follow-up for a successor version is to define `Rel_Dk := RelD3 ∧ InDk`, so the statement can be `RelD3` alone.

Remaining, in order:
1. **Read-logging refactor.** `checkD2L_eq` and `checkD3L_eq` are already proved; the logged run equals the trusted checker.
   * Completed: close the loop proof and validate the tail-recursive executable.
2. **Re-run every regression with the logged checker:**
   * Completed: D3 three-way on all four corpora;
   * D2 and D1 full corpora remain; D0/D1/D2 public fixtures pass;
   * the WASM harness and trie-accounting traces.
3. **Rebuild the D3α reference `examples/reexec-v3-d3` on the read-set normal form.**
   * base_state must be exactly the logged read set, and verify must accept only those bytes.
   * Run check-local, including the `values/inject-unread` and `codes/inject-unread` mutators.
4. **D0a formal tier is added and builds.** Draft activation still needs checked workload-class coverage and final domain bounds; an empty class list would silently allow abstention on every input.
5. **Re-freeze the trusted tree once**, covering the logged spec and RelD0a.
6. **Run the joint w1 cost-baseline window** for the paired-mode draft. The procedure is in `docs/LIVE.md` §5f and BENCHMARK_SPEC §14.
7. **Release and record.**
   * Sign with the local operator tooling (never print key material), register, and deploy.
   * Submit the reference (expect ADMITTED) and the hostile case `near-v3-d3-lenient-codes` (expect REJECTED).
   * Record the results in `docs/LIVE.md` and `docs/e2e-results/`.

Corpora have been **moved to `/data/illia/nearproof-deps/corpora/`**: `d3c7`, `d3c8`, `d3c9`, `d3c10`, `d2corpus.v2`, `d1run`. The STATUS file still lists the old scratchpad paths. Regeneration commands are in STATUS-V3-D3 §5.

Open nearcore findings and spec ambiguities: STATUS-V3-D3 §6, and `oracle/tools/README-d3.md`.

## 4. Stream B: succinct D0a STARK (np-udr-stark-v2), the critical path

Integration branch `lane/v3-air`, which also carries 13 sub-lane branches. **Read `STATUS-V3-AIR.md` at the lane root.** Design: `docs/zk-formal/V3-D0-DESIGN.md`.

Integration gate: `lake build ZkFormal.V3.Integration` on `lane/v3-air`, now passing. Use this target rather than the incomplete historical root. Next: finish completeness and indexed public segments, then assemble the real AIR and size proof.

* **Proved:**
  * the v2 protocol: public bus, auxGroup and admission;
  * size lever (a), a dedup bound;
  * ChaCha20 tables, sound and complete;
  * trie soundness, through `upsV3_linkB`;
  * scheduler soundness;
  * spec D0a.
* **Partial:**
  * trie completeness: the upsV3 render, M7d;
  * scheduler completeness: M4;
  * the receipt side (rcpt, srcp, qv).
* **Not started:**
  * indexed public segments (R1);
  * assembly: `nearAirV3`, FactorSound and FactorComplete, `honestTrace_fits`, and the certificate;
  * the Rust prover v2;
  * timing of a real judge run.
* **Branches that don't build (WIP):**
  * `lane/v3-trie-h` `1d8b2f12`;
  * `lane/v3-rcpt-h` `4ae51a13`.
* **Correction:** the status file says the receipt lane was "paused by the user". It was not; it stopped only because of a usage-limit interruption. Resume it, since it is on the critical path.
* **Elaboration-budget risk:** v1 alone uses 647 s of the 1,800 s budget, and the v3 additions are large. Measure early.

**Decisions to bring to the user** (STATUS-V3-AIR §5):
1. **Size cap.** With two SHA tables at B0 = 2.0 MB, the bound is about 150 KB over 8 MiB. One SHA table only fits if B0 ≤ about 1.95 MB.
   * Recommendation: lever (1), roll-in alignment, which saves about 1.6 MB.
2. **ChaCha words bound W in RelD0a.** Options are 360k or 770k.
   * It is not a deterministic nearcore invariant, so it carries a liveness note like A7's.
   * If it is approved, add it before the near-chunk-v3 freeze.
3. **Receipt lane edits to PrepD0.lean** (unsigned).
4. **Source-proof Merkle path length.** Bound it as a domain conjunct, or count it in a budget.

Cost-model levers to keep in mind: compact refund codec (about −0.45 MB), width cuts.

## 5. Stream C: cost scoring (done; one task left)

The work is merged and deployed (see §2). The only thing left is the joint near-chunk-v3 baseline window (§3 step 6).

Known issue: per-class verify time varies a lot between inputs. The paired mode already handles this; the speed-scored boards are not paired.

## 6. Smaller follow-ups

* **Succinct badge.** Max proof bytes, max verify time, and a log-log check that neither grows with gas. Proposed values: 2 MiB / 50 ms. Display only; not implemented.
* **Mainnet replay.** Real chunks would provide real class weights and a measured `G_α` (rows per WASM op). The current `G_α` is a checkpoint value.
* **Re-check the D3 spec on the clean-room Python VM.** That VM was tuned against nearcore black-box runs, so it is not fully independent.
* **Future challenge: 1 Pgas in a single STARK, without recursion.** Not started; the user prioritised finishing v3.
  * It needs a field with larger 2-adicity, e.g. Goldilocks with 2^32.
  * It needs a distributed prover.
  * It needs dedicated precompile tables.
* **Future challenge: cross-shard, whole-block proof.** Documented in BENCHMARK_SPEC §14.11.
* **Old worktrees.** About 100 merged lanes under `nearproof-wt/` can be removed with `git worktree remove` once you have checked each one is clean and merged, to free disk.

## 7. Key documents

| Topic | Documents |
|---|---|
| Architecture and contracts | `ARCHITECTURE.md`, `CONTRACTS.md`, `CHANGELOG-contracts.md` |
| Security model | `TCB.md`, `THREAT_MODEL.md`, `SECURITY_POLICY.md` |
| Benchmarking and operation | `BENCHMARK_SPEC.md`, `LIVE.md` |
| v3 domain specs | `spec/near-chunk-validation-{d0,v0a,d1,d2,d3}.md` |
| Requirements | `docs/requirements/` |
| ZK formalisation | `docs/zk-formal/` (DESIGN, STATUS-L*, V3-D0-DESIGN) |
| Audits and reviews | `UNTRUSTED_NEAR_ZK_AUDIT_2026-10-05.md`, `reviews/D3_REVIEW_2026-10-06.md` |
