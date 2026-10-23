# Handover — 2026-10-23

Only unfinished work and shared rules belong here. Evidence/history: [logs](logs/).
Remove completed items; update their logs instead. Old lane labels are not proof of live activity.

## Pending integration

- `plan/lean-chunk-transition` / `lean-chunk-L{0,1,2,3,5,7,8}`: all at `833f3311c`, clean at this audit; **plan only**, not implementation. Review the branch's `docs/requirements/LEAN_CHUNK_TRANSITION_PLAN.md`: full PV86 Lean semantics and arena admission are separate from succinct/PQ completion. Plan is now merged onto main (document + its handover pointer only); **none of its milestones is newly certified** by this merge and all gates A/B/C remain open as tabulated in the plan's completion record.
- `pq-chunk-e2e` (`lane/pq-chunk-perf`): committed checkpoint already integrated; three local log edits remain (aggregation plan/tail/gap analysis). Reconcile before retirement.
- Check fresh Git/process state before touching any worktree, including the Claude checkout. MEMIO is merged; its remaining proof obligations are below. Recovery inventory: [worktree audit](logs/worktree-reconciliation-2026-10-23.md).

## 0. Goal and standing user directives

**2026-10-23 priority:** complete the proof-system-independent Lean chunk transition and arena
before treating any particular succinct-proof implementation as a prerequisite. Agent workstreams,
dependencies and acceptance gates are in
[`requirements/LEAN_CHUNK_TRANSITION_PLAN.md`](requirements/LEAN_CHUNK_TRANSITION_PLAN.md).
The full PV86 semantic target is broader than today's D3α domain; existing signed challenges remain
unchanged and broader coverage requires a versioned successor.

## Remaining work

- **D3 succinct proof:** build the D2/D3 chunk AIR, state render/overlay replay and real Wasm/state/recursion connection. The shipped D3 artifact proves witness re-execution, not succinctness. `compose_pv86` is a reduction, not an independent join; under call agreement its state premise is equivalent to the desired verdict. `Read.check` supplies a stronger, artifact-bound acceptance condition. Hook-level `functionCall`→preparation lift remains open; do not import the untracked `Final.lean` containing `sorry`. [Latest preparation/join analysis](logs/pq-prepare-link-2026-10-23.md).
- **Host/state:** discharge `H0`/`HoldRow`, per-row gas/boundary and HOST message-tape correspondence. MEMIO still assumes `HostBLinked.linked`/`unique`, consumed-byte liveness and `BufOK`. CD needs `RealStoreMatchesTables`, `CdKeynibFromHostB`, `UpsV3AppliesLog`, memory-bound preservation and a parameterised upsert AIR (current polynomial hard-codes `[0,15]`). [MEMIO](logs/pq-memio-finalized-2026-10-23.md), [CD](logs/pq-d3-air-2026-10-22.md).
- **Wasm coverage:** IF checker soundness/full execution integration, result-carrying IF, and `loop`/`memory.grow`/`call_indirect` coverage. Conditional IF row facts are already on main. [IF](logs/pq-if-air-2026-10-22.md).
- **Hashes/receipts:** RIPEMD `round_agrees` (`bl'`/`br'`), general rotation bridge, feed-forward/digest bus and message binding; Keccak round agreement, absorb/squeeze and state bus; `RIDS`/`SRC`/`RCL`, `newReceipts`, host-trace/generator/byte-binding obligations. Promise encodings are done; `promise_yield_resume*` result-tag mismatch remains. Separate Ed25519/SHA-512 proof layer is unbuilt. [Host/receipt gaps](logs/pq-hostfinal-2026-10-22.md).
- **Recursion/security:** production-parameter aggregation node, real D3 segment leaves, wider size margin, single-database `NodeOK`, concrete family-QROM instantiation, WHIR transfer, arbitrary-trace NV semantics and concrete-hash bridge. The 299,967 B D0a packet is a linear chain with 33 B margin; another valid replay exceeds 300 KB. Test-target tree measurements do not certify production trees. Keep `security_established=false` until obligations close. [Aggregation](logs/pq-agg-tail-2026-10-22.md), [security](logs/pq-paper-blockers-recheck-2026-10-21.md).
- **D1:** `A7D1Step`, `LinkD1CoreStmt`, R1/R2/A1; exercise stub/nmem queries and reprove the 33-table path. Archived phase-2 drafts fail through `LinkSched`/`RecModel`/`A7Bound`; L4's reference-prover draft fails honest tests. [Plan](zk-formal/V3-D1-PHASE2.md), [recovery](logs/worktree-reconciliation-2026-10-23.md).
- **Arena:** verify actual signed admission reports; deployment/local PASS is not admission. Resolve D0a supplied-witness rejection/resubmission status against [live-run evidence](logs/v3-deploy-d0a-2026-10.md). Successor work: one canonical relation with proved tier restrictions, measured workload weights/succinct thresholds, full semantic coverage, guest-image isolation upgrade. Python VM independence remains unresolved ([provenance](research/python-vm-independence.md)).

## Shared rules and lessons

- Target: artifact-bound, independently checked chunk validation replacing `validate_chunk_state_witness`. No weakened measurement rules or hidden domain assumptions. Prove semantic claims; label tests, conditional lemmas and estimates accurately.
- Keep one `near-chunk-v3` challenge with coverage tiers. Signed challenges, frozen `oracle/v3` and pins are immutable (`make pin-check`). Broader semantics/scoring need a versioned successor. Signed R5 forbids composition; long-term recursion research is separate. `G_α≈3.45 Tgas` is not 1 Pgas. Decisions: [D3 study](zk-formal/V3-D3A-STUDY.md), [contracts](CONTRACTS.md).
- One worktree per agent; integrate on `integration/*`, preserve concurrent edits, verify ancestry **and content**, push checkpoints. Never hard-link `.lake`; copy/reflink or rebuild. Check free disk before builds; retire merged worktrees only after preserving unique evidence.
- Rebuild Lean tools **and** Rust binaries before KATs; tracked binaries and mtimes can lie. Ensure new modules are root-imported and actually compiled. Audit theorem axioms and premises; green job counts, named `Prop`s, differential vectors and vacuous reductions do not establish soundness. Run relevant builds/tests, axiom audits, pin-check and affected proof manifests before promotion.
- Use dependency setup scripts; a compiling stale deps checkout may not match the recorded patch. Never bypass drift checks.
- Heavy work: `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy <cmd>` (32G only for D2 kernel evaluation). CPUs 0–7/16–23 belong to w1; stop only in logged empty-queue windows and restart. Avoid concurrent memory oversubscription.
- Loopback + `tailscale serve` only, never funnel. Keep secrets outside Git and output.
- Check AIR activity/count semantics: inactive HOSTB response/register rows invalidate inverse grouping; host restarts require fresh gas bounds; `HOSTO.mult` need not be a bit. Use the real table in active-row filters. Storage host IDs are 57–60; older canonical numbering collides with hashes.
