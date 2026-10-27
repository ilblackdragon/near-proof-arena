# Lean chunk validation — what is left

Status 2026-10-27, after the arcs, size-limit, UQ-014 and signed-tier merges. Scope: **stateless
chunk validation** at PV86 against pinned nearcore 2.13.4 (`44f7ae6c`), mainnet parameters.
Block/header validity, finality and the epoch manager are out of scope: their answers enter the
claim as trusted facts ([claim-v3 §2.4](../../spec/claim-v3.md#24-classification-of-every-claim-value)).
The long form of this file (per-package history and criteria) is in git history (`b6b01df77`) and
[workplan-review-2026-10-25.md](../evidence/lean-chunk-completion/workplan-review-2026-10-25.md).
Gates A–C are defined in the [transition plan](LEAN_CHUNK_TRANSITION_PLAN.md); all three are open.

## TL;DR

- **One checker, two tiers.** `nearspec-v3-check-successor --tier allFeatures` is the full
  successor; `--tier signed` (`checkD3`/`RelD3`) is the statement of record.
- **Agreement with cold nearcore (`allFeatures`).** Corpus, 235,716 cases: 235,397 agree, 95 out of
  domain, 224 Lean rejects in `d2corpus.v2` (those witnesses carry no code and their `ok` is the
  producer's warm verdict, not a cold one). Fixtures: 640/640 across the committed families
  ([curve hosts](../evidence/lean-chunk-completion/curve-host-fixtures/README.md),
  [key families](../evidence/lean-chunk-completion/key-family-fixtures/README.md),
  [ML-DSA-65](../evidence/lean-chunk-completion/mldsa-fixtures/README.md),
  [yield](../evidence/lean-chunk-completion/yield-fixtures/README.md),
  [resharding](../evidence/lean-chunk-completion/resharding-fixtures-2/README.md),
  [cross-family](../evidence/lean-chunk-completion/cross-family-fixtures/README.md),
  [Gate-B caps](../evidence/lean-chunk-completion/gate-b-caps/README.md),
  [runtime errors](../evidence/lean-chunk-completion/runtime-errors/README.md),
  [size limits](../evidence/lean-chunk-completion/size-limits/README.md), …; each generated family
  has honest chunks, mutants, blind replay and a deliberate-breakage control). Gap census 3,138/3,138
  accept. Mainnet shard 13: 1,223/1,223 consecutive chunks. **No Lean accept of a
  nearcore-rejected chunk anywhere.**
- **Blind.** Lean computes every header output from the witness: 39,452 corpus chunks match all 11
  fields; per-outcome observables match on 17,338 chunks with 0 mismatches
  ([full-observables](../evidence/lean-chunk-completion/full-observables/README.md)).
- **Out of domain (`allFeatures`):** the 95 preparation-pipeline thread races (nearcore is itself
  nondeterministic there and rejects all 95), and a cold code fetch over the 64 MiB response cap
  (`w.code_response_size`: the verdict depends on the validator's cache).
- **Closed in this round.**
  - Size limits: Lean takes the compressed witness (`near-arena-cwitness-v3`), decodes zstd, and
    applies nearcore's 48 MiB encoded / 64 MiB decoded limits exactly
    ([size-limits](../evidence/lean-chunk-completion/size-limits/README.md)).
  - UQ-014: every runtime error kind has a disposition. Loading errors and import link errors are
    modelled; `WasmUnknownError` is unreachable; host-state failures are an environment assumption.
    Evidence: 33,930 verdicts, 0 disagreements
    ([runtime-errors](../evidence/lean-chunk-completion/runtime-errors/README.md)).
  - Signed tier: the 4 valid-chunk rejects are fixed (V3 bandwidth chaining, instance loading
    limits). Both engines now honour the V2 parent-map buffer rule in bandwidth requests. Before
    this fix they accepted 21 of 24 mutants that nearcore rejects
    ([signed-valid-rejects](../evidence/lean-chunk-completion/signed-valid-rejects/README.md)).
  - Speed: zero-fee control runs execute as proved arcs (`@[csimp]`). The worst loop went from
    ~10.6 h to ~50 s per 300 Tgas. Verdicts are identical on every population.
- **Signed tier, corpus.** 112,036 agree and 120,716 agree outside its domain. 2,758 are out of
  domain, of which 2,513 are oracle-asserted. 206 reject valid chunks: the same code-less
  `d2corpus.v2` cases. No signed accept of a nearcore reject.
- **Proved:** tier lifts and genesis overlap, fuel monotonicity, PV86 layout reachability, the
  arcs fast path, loading-before-execution order, and kernel non-vacuity (`decide +kernel`, no
  `native_decide`) of `RelD3` and `Tier.rel .allFeatures`, each with its negation on real chunks.
  Only `propext`, `Classical.choice` and `Quot.sound` are used.

## Open work, by what blocks Gate B

| # | Item | Done when |
|---|---|---|
| 1 | **W13 all-shard mainnet replay**, the only real-traffic evidence beyond shard 13. Needs: a 1,000-block all-shard window on the sponsor machine ([runbook](../../tools/mainnet-replay/ALL_SHARDS_RUNBOOK.md), [replay gate](../../tools/mainnet-replay/README.md)), the cold native adapter, and the finality/authentication boundary | `make w13-gate`: 100% coverage, 100% verified matches, 0 mismatches / unsupported / missing / errors (with zero comparisons, `mismatch_percent` is `null`, never a pass) |
| 2 | **Evaluator speed and memory** (W02/W16). Still slow: push-then-pop and `br_if`-back-edge loops (~3–4 h per 300 Tgas); the zstd decoder (~145 s per MB of entropy-coded witness, hours at 48 MiB); ~106 B of memory per witness byte | every worst-case fixture meets a stated per-chunk time/memory budget |
| 3 | **Fuel sufficiency theorem** (W02): obligations O-W1b–O-W4 in `Wasm/Fuel.lean`. The largest is finite-wasm charges before execution | proved: no valid execution is rejected as fuel exhaustion |
| 4 | **Size-limit fixtures** (W02): the 48 MiB encoded boundary is tested at frame level only, and the 64 MiB code-response cap by unit tests only. No whole-chunk fixture exists at either boundary | whole-chunk nearcore fixtures at both boundaries, or a stated reason they cannot be generated |
| 5 | **Tier refinement** (W12): obligations O1–O7 (floats, curve hosts, global actions, storage resolution, loading limits, resharding on non-genesis segments, complete-code). `completeCodeGlobal` refines no tier | proofs build with the allowed axioms |
| 6 | **Signed-tier completeness** (UQ-010), where the signed tier excludes valid chunks: (a) a non-empty outgoing buffer to a split parent (`c.same_layout`) and pre-split gating (`c.no_split_gate`); (b) eval-time worst-case loops that exhaust the signed fuel budget (`e.wasm-α … fuel exhausted`, 9 fixtures); (c) the signed `witness.bin` bound (64 MiB including code, `ChallengeChunkV3`), which can exclude code-heavy chunks; (d) `DomainD3` reconciliation | each removed, or accepted by decision as a signed restriction |
| 7 | **Warm-cache coherence** (W08): historical and warm compiled-cache behaviour. `completeCodeGlobal` rejects 178 valid warm-cache chunks. The generator labels race mutants `e.code_cache` | every code-resolution case is deterministic and justified, or rests on an authenticated input |
| 8 | **Open UQs** (W00): 001 (cold-cache statement), 002, 003 (NaN payloads), 004 (curve gas pins), 007 (`LegacyEthWallet`), 013 (binding trusted facts), 015 (recorder bound; W09), 016 (action-log equivalence), 017 (genesis header set); versioned claim/witness schema | each has a source-backed disposition and a test or proof |
| 9 | **Observables** (W01): failure kinds, per-receipt storage attribution, per-outcome compute; expected per-outcome values for d1run/d2corpus.v2; the corpus CI gate on a provisioned runner | every case has an asserted outcome and a full observable comparison |
| 10 | **Remaining shapes** (W05–W07): curve hosts from timed-out yield callbacks; post-NEP-488 `version = 1`; ML-DSA `z` exactly at the norm bound; mismatched distribution code identities; state init followed by a successful emit | fixtures, or a source-backed unreachability argument |
| 11 | **Proof debt**: float overlap/range (W04); split correctness and authentication (W11); `WitnessLift` (`Coverage.lean:191`); wider kernel non-vacuity (storage-writing, multi-receipt and resharding cases); `Logged.API`/`D3LSpec` no longer build (`Logged/WasmStepE.lean:185/200`, outside the default build) | proved, with no `sorry` and only the allowed axioms |
| 12 | **Environment assumptions** (from UQ-014): host-state failures (slot exhaustion, mmap, cache I/O) are assumed absent; the instance-layout model is measured on x86_64 only | stated in the frozen package; aarch64 measured, or excluded by statement |
| 13 | **W14–W16**: freeze one package and replay everything on it (Gate B); restricted reference admission (Gate A); successor admission and release (Gate C) | signed admissions |

## Decisions in force

- `checkD3`/`RelD3` is the statement of record. Its widenings toward nearcore are accepted as
  strengthenings: the UQ-010 secp delegates and, on 2026-10-27, V3 bandwidth chaining, instance
  loading limits and the V2 parent-map rule ([record](../research/lean-chunk-w00-owner-map.md)).
- ML-DSA-65 is implemented, not excluded. W13 runs on a sponsor-provided all-shard machine.
- Kernel non-vacuity (`Examples/RealCaseD3`, ~3.5 min, ~21 GB) runs on demand, not in CI:
  `HEAVY_MEM=40G /data/illia/nearproof-deps/bin/heavy lake build NearSpecV3.Examples.RealCaseD3`.
- Successor storage maps are `TTN.BMap` (`Std.TreeMap`), so the kernel can evaluate them.
- The witness may be the compressed bytes as distributed (`near-arena-cwitness-v3`). Lean decodes
  zstd and applies nearcore's 48 MiB encoded / 64 MiB decoded limits. A chunk whose cold code
  fetch exceeds the 64 MiB response cap is out of domain (`w.code_response_size`).
- Zero-fee control runs execute as proved arcs in compiled code only (`@[csimp]`,
  `Wasm/Arcs.lean`). The spec and the kernel proofs still use single steps.

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
