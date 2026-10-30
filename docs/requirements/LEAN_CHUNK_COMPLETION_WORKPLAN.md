# Lean chunk validation — what is left

Status 2026-10-31, after the workplan-finish round (items 2–12, 2026-10-29/31). Scope: **stateless
chunk validation** at PV86 against pinned nearcore 2.13.4 (`44f7ae6c`), mainnet parameters.
Block/header validity, finality and the epoch manager are out of scope: their answers enter the
claim as trusted facts ([claim-v3 §2.4](../../spec/claim-v3.md#24-classification-of-every-claim-value)),
bound to the verifier by admission contract A1 (UQ-013, below).
The previous version of this file is `ecd5ac86c`; the long form is in git history (`b6b01df77`).
Gates A–C are defined in the [transition plan](LEAN_CHUNK_TRANSITION_PLAN.md); all three are open.

## TL;DR

- **One checker, two tiers.** `nearspec-v3-check-successor --tier allFeatures` is the full
  successor; `--tier signed` (`D3.checkD3`/`RelD3`, `D3/Signed.lean`) is the statement of record.
  The signed tier is now the old pipeline (`D3.checkD3Core`) plus a proved hand-over to the recorder
  engine for resharding claims and witnesses over the storage-proof bound (`checkD3_of_core_ok`,
  `checkD3_cases`; `G_α` is not applied on the hand-over path).
- **Full corpus, pre-freeze replay (2026-10-31, checker `197e28fe…`, all 235,716 cases), 0
  disagreements with cold nearcore on either tier.** `allFeatures`: 76,431 accept / 159,190 reject /
  95 out of domain (the preparation-pipeline races, `e.code_prep_race`). `signed`: 73,783 / 159,175 /
  2,758 out of domain (2,513 oracle-asserted, 245 not yet asserted). The 224 code-less `d2corpus.v2`
  rejects are gone (re-captured cold with code). Results: `/data/illia/nearproof-deps/gateb-prefreeze/`.
- **Fixture families**, each with honest chunks, mutants, blind replay and a breakage control, no
  Lean accept of a nearcore reject: the earlier ones (curve hosts, keys, ML-DSA, yield, resharding,
  cross-family, Gate-B caps, runtime errors, size limits) plus this round's
  [code-cache](../evidence/lean-chunk-completion/w08-warm-cache/README.md) (4,730), [remaining shapes](../evidence/lean-chunk-completion/remaining-shapes/README.md) (6,272 rows),
  [boundary sizes](../evidence/lean-chunk-completion/size-limit-fixtures/README.md) (48 MiB encoded / 64 MiB code response),
  [eval loops](../evidence/lean-chunk-completion/eval-budget/README.md), [signed completeness](../evidence/lean-chunk-completion/signed-completeness/README.md),
  [pipeline race](../evidence/lean-chunk-completion/pipeline-race-fixtures/README.md). Gap census 3,138/3,138 accept; mainnet shard 13
  1,223/1,223.
- **Blind observables** ([w01-observables-v3](../evidence/lean-chunk-completion/w01-observables-v3/README.md)): 28,070 chunk rows, 0
  mismatches on failure kinds (46,673), per-outcome compute (1,098,587) and per-receipt storage
  attribution (894,074 entries); d1run and d2corpus.v2 expected values re-captured cold.
- **Proved** (only `propext`, `Classical.choice`, `Quot.sound`): tier lifts and genesis overlap,
  fuel monotonicity, **fuel sufficiency** for the successor `FunctionCall` hook
  (`functionCall_fuel_sufficient`; `HostsOK` per arm; `CodeCertified` as the checked guard
  `w.fuel_certificate`, which fires on no corpus module), the arcs fast path and the label memo,
  PV86 layout reachability, loading-before-execution order, **rungs and `WitnessLift`**
  (`RelRungDk := RelD3 ∧ InRungDk`, `D0 ⊂ D1 ⊂ D2 ⊂ D3` by projection, `witnessLift`; `D1 ⊄ D2` for the
  old checkers is kernel-proved), D2 ⊂ D3 for the checkers, split correctness (W11), float range (W04)
  and float overlap, tier refinement O1 (floats), O5 and **O7** (`completeCodeGlobal ⇄ globalActions`),
  the `StorageExecution` flag refactor (`run_eq_orig`), the versioned claim/witness envelope
  (`SchemaVersion.lean`), and kernel non-vacuity of `RelD3`/`allFeatures` on storage-writing,
  multi-receipt and split-child chunks.
- **Evaluator budget** ([eval-budget](../evidence/lean-chunk-completion/eval-budget/README.md)): ≤ 15 min CPU and 16 GB per chunk on
  this host; worst measured 105 s / 2.2 GB (64 MiB cold code); zstd 64 MiB in ~2 s; loop shapes
  43–63 s per 300 Tgas (were ~4–5 h).

## Open work

| # | Item | State / done when |
|---|---|---|
| 1 | **W13 all-shard mainnet replay** ([runbook](../../tools/mainnet-replay/ALL_SHARDS_RUNBOOK.md)) | waits on the sponsor machine; `make w13-gate` at 100% coverage, 0 mismatches / unsupported / missing / errors |
| 5 | **Tier refinement** O2 (curve hosts), O3 (global actions), O4 (storage resolution), O6 (resharding on non-genesis segments) — O1, O5, O7 proved | in progress (three lanes, 2026-10-31); proofs build with the allowed axioms. Status: [tier-refinement-w12 §5](../evidence/lean-chunk-completion/tier-refinement-w12/README.md) |
| 13 | **W14–W16**: freeze one package and replay everything on it (Gate B); restricted reference admission (Gate A); successor admission and release (Gate C) | Gate B after item 5; Gate A/C need signed admissions by the owner |

**Closed this round** (evidence linked; residuals listed so they are not lost):

| # | Item | Residual, not blocking |
|---|---|---|
| 2 | Evaluator speed and memory ([eval-budget](../evidence/lean-chunk-completion/eval-budget/README.md)) | memory is still ~104 B per witness byte (`List UInt8`); the worst 64 MiB-witness chunk is projected, not measured |
| 3 | Fuel sufficiency ([fuel-sufficiency](../evidence/lean-chunk-completion/fuel-sufficiency/README.md)) | a general proof of `CodeCertified` would make the `w.fuel_certificate` guard provably dead |
| 4 | Size-limit fixtures ([size-limit-fixtures](../evidence/lean-chunk-completion/size-limit-fixtures/README.md)) | code-response family is one seed (64 MiB cases); no natural 48 MiB witness can be generated |
| 6 | Signed-tier completeness, UQ-010 ([signed-completeness](../evidence/lean-chunk-completion/signed-completeness/README.md)) | remaining signed exclusions outside item 6 are recorded there (`e.g_alpha` on the core path, ML-DSA, curve hosts, …) |
| 7 | Warm-cache coherence + UQ-001 ([w08-warm-cache](../evidence/lean-chunk-completion/w08-warm-cache/README.md)) | 27 conservative race exclusions where only nearcore's failure point races |
| 8 | Open UQs ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md), [register](../research/lean-chunk-w00-owner-map.md)) | UQ-007 has no whole-chunk fixture (pre-PV83 accounts) |
| 9 | Observables ([w01-observables-v3](../evidence/lean-chunk-completion/w01-observables-v3/README.md)) | failure-kind payloads compared by name only; the corpus CI gate needs a self-hosted `near-corpora` runner (owner action) |
| 10 | Remaining shapes ([remaining-shapes](../evidence/lean-chunk-completion/remaining-shapes/README.md)) | no fixture for a compute-deferred timeout callback that runs a host |
| 11 | Proof debt ([proof-debt](../evidence/lean-chunk-completion/proof-debt/README.md)) | `d3rich` storage kernel case needs > 60 GB |
| 12 | Environment assumptions ([spec/environment-v3.md](../../spec/environment-v3.md)) | aarch64 excluded by statement |

## Decisions in force

- `checkD3`/`RelD3` is the statement of record. Its widenings toward nearcore are accepted as
  strengthenings: the UQ-010 secp delegates; on 2026-10-27 V3 bandwidth chaining, instance loading
  limits and the V2 parent-map rule; on 2026-10-29/30 the resharding and storage-bound hand-over with
  `G_α` lifted on that path, and signed fuel = `wasmFuel` ([record](../research/lean-chunk-w00-owner-map.md) §3.4).
- **Rungs** (2026-10-30): `RelRungDk := RelD3 ∧ InRungDk` in the new statement module
  `ChallengeChunkV3R.lean`; the existing signed names `RelD0…RelD2` are unchanged
  ([record](../research/lean-chunk-w00-owner-map.md) §3.5).
- **New challenge draft** `challenges/drafts/near-chunk-v3-1.draft.json` (built by
  `spec/tools/build_challenge_draft_v3_chunk_r.py`): rungs, `max_witness_bytes` 75,497,501
  (`maxWitnessChunk`), the resharding / secp / storage-proof restrictions dropped. Unsigned; no
  published challenge file changed. Regenerate its `tree_digest` at the freeze.
- **UQ-013**: admission contract A1 — a proof is admitted only by a verifier that rebuilds the claim's
  trusted section from its own chain state and finds it byte-identical.
- `w.fuel_certificate` is a kept out-of-domain reason (allFeatures). aarch64 is excluded by statement.
- ML-DSA-65 is implemented, not excluded. W13 runs on a sponsor-provided all-shard machine.
- Kernel non-vacuity runs on demand, not in CI (`HEAVY_MEM=40G /data/illia/nearproof-deps/bin/heavy lake build NearSpecV3.Examples.RealCaseD3`, likewise `RealCaseD3Store`, `RealCaseD3Split`).
- The witness may be the compressed bytes as distributed (`near-arena-cwitness-v3`); a cold code
  fetch over the 64 MiB response cap is out of domain (`w.code_response_size`); preparation-pipeline
  races are out of domain (`e.code_prep_race`).
- Zero-fee control runs and label-keeping loops execute as proved fast paths in compiled code only
  (`@[csimp]`, `Wasm/Arcs.lean`). The spec and the kernel proofs still use single steps.

## Rules for remaining work

- Ground truth is pinned nearcore run cold. Produced values are never Lean inputs (`--blind`).
- Each semantic change needs:
  - whole-chunk positive and negative fixtures (≥ 1,000 comparisons over ≥ 4 seeds per new
    family);
  - a deliberate-breakage control;
  - a before/after verdict table on the corpus, fixtures and census.
- A Lean accept of a nearcore reject is a soundness bug. Nearcore nondeterminism is a named
  out-of-domain reason, never an accept.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Keep `make pin-check` ok (signed sources unchanged).
