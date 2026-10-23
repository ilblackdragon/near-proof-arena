# L2 — floating-point Wasm: lane log

Date: 2026-10-23. Owner: L2 lane. Status: **the float domain is implemented, proved where a proof
exists, and measured against the pinned engine; L2 is not complete** (see §7).

| | |
|---|---|
| Worktree | `/data/illia/nearproof-wt/lean-chunk-L2` |
| Branch | `lane/lean-chunk-L2` |
| Base commit named in the task | `a5ef42e0c` (L1 tip: `checkD3Proto` + protocol gas bound) |
| Branch tip at the end of this session | `aa2a0a7a3` |
| Merged to `main`? | No. Not pushed. |
| Toolchain | `leanprover/lean4:v4.34.1`; nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86 |

---

## 1. Inventory rows owned, and final status

The five rows were read from
`/data/illia/nearproof-wt/lean-chunk-L0/docs/research/lean-chunk-coverage.json` as instructed (the
219-row L0 inventory). That file is **not on this branch**; this branch's generator emitted only
`L0-instr-float` for L2. The generator now derives all five from the Lean source
(`tools/d3/lean_chunk_coverage.py:float_coverage`), so the statuses below are read out of the code,
not asserted by hand. `--check` passes.

| Row | Subject | Final status | Evidence |
|---|---|---|---|
| `L0-instr-float` | float instruction family | **implemented** | 70/70 no-immediate opcodes decided (`Wasm/Float.lean:evalFloatOp`), plus loads/stores/consts (`Exec.lean`); 141 kernel-decided tests; measured against nearcore (§4) |
| `L0-W-001` | float in an imported function type | **implemented** | guard gated on `!cfg.floats` (`Prepare.floatGuardImport`); directed test `float_prepare.py` — import-only f32 *and* f64 signature, `floatPv86` outcome line **identical to nearcore's**, incl. burnt gas 88,821,418 |
| `L0-W-002` | float global | **implemented** | `Prepare.floatGuardGlobal`; `float_prepare.py` — immutable, mutable and read-then-dropped f64 globals, `floatPv86` line identical to nearcore's (95,403,466 / 100,316,863 gas) |
| `L0-W-003` | float type or operator in a function body | **implemented** | `Prepare.floatGuardBody`; 20 recorded whole `d3float` chunks accepted through `checkD3F` where D3α gave a float exclusion (`chunk_float.py`) |
| `L0-W-012` | float operator in interpreter / validator / analyzer | **implemented** | all four sites: `Exec.execFloat` (the only float entry point), `Validate` signatures + loads/stores/consts, `FiniteWasm` max-stack and `floatPartial`, `InstrSize` float consts |

Whole-domain caveat, recorded in the row itself: the operator set is complete, but **agreement with
nearcore is measured, not proved**, and whole-chunk coverage is 26 recorded chunks rather than a
generated float workload.

## 2. What was implemented

### 2.1 Kernel — `NearSpecV3/Wasm/Float.lean` (579 lines)

A format-generic IEEE 754 kernel over **bit patterns as `Nat`**: no `Float`, no `Float32`, no
`native_decide`, no `axiom`. One rounding routine (`roundPackS`: round-to-nearest-ties-to-even,
sticky bit for division and square root, gradual underflow, overflow to infinity at the IEEE
threshold). A float is never a host float anywhere in the pipeline — `Val.f32`/`Val.f64` carry bit
patterns and `ConstE.f32`/`.f64` carry the initialising bits, so a float global's value is
byte-exact.

Covered: comparisons 0x5B–0x66; abs/neg/ceil/floor/trunc/nearest/sqrt and add/sub/mul/div/min/max/
copysign for both formats; the 8 trapping and 8 saturating truncations; the 10 `convert_i*` plus
`demote`/`promote`; the 4 reinterprets. Plus, in the surrounding modules, float loads/stores and
constants with real little-endian immediates, validation signatures, the finite-wasm stack and gas
analyses, and the preparation switch.

**Canonicalising vs bit-preserving** — the distinction the plan asks for, stated as kernel-checked
theorems, not prose:

| | operators | pinned source |
|---|---|---|
| canonicalise to `+qNaN` (payload dropped, sign 0) | add, sub, mul, div, min, max, sqrt, ceil, floor, trunc, nearest, demote, promote, all trapping/saturating truncations | `winch-codegen-45.0.0/src/visitor.rs:602-960,1159`; `isa/x64/masm.rs:716-738`; constants `masm.rs:16-17` |
| bit-preserving (payload and sign kept) | abs, neg, copysign, the 4 reinterprets | `isa/x64/masm.rs:607-690,1310-1328`; no canonicalisation pass follows them |

Theorems: `add_nan_canonical_f32/f64`, `qnan_f32_bits` (= `0x7FC00000`), `qnan_f64_bits`
(= `0x7FF8000000000000`), `abs_f32_payload`, `neg_f32_payload`, `copysign_f32_body`,
`copysign_f32_sign`.

### 2.2 Successor relation — `NearSpecV3/ChallengeChunkV3Float.lean`

`checkD3F` / `RelD3F` are the D3 pipeline with `NearCfg.floats = true` (`Wasm.floatPv86`);
`checkD3ProtoFloat` composes this with L1's protocol gas bound. **`RelD3` and `gAlpha` are
untouched** (verified against the true base in §6).

Theorem statements, with every residual premise:

```lean
-- the checker decides the relation (no residual premise; `Iff.rfl`)
theorem checkD3F_characterization (c w : Bytes) : RelD3F c w ↔ checkD3F c w = .ok ()
theorem relD3F_iff_acceptsD3F (c w : Bytes) : RelD3F c w ↔ acceptsD3F c w = true
instance (c w : Bytes) : Decidable (RelD3F c w)

-- the two checkers differ only in the configuration argument (premise: the configs are equal,
-- which is false by construction — this records the shape of the difference, nothing more)
theorem checkD3F_eq_checkD3_of_cfg (c w : Bytes) (h : floatPv86 = pv86) : checkD3F c w = checkD3 c w

-- the configurations differ in exactly one field
theorem floatPv86_fields : floatPv86.regularOpCost = pv86.regularOpCost ∧ … ∧ floatPv86.floats = true
```

**Additivity, at the granularity that is actually provable.** The three guards are named predicates
in `Prepare.lean`, each literally `!cfg.floats && <module property>`:

```lean
-- residual premise: the module has no float at the relevant site (that is the sub-domain)
theorem floatGuardImport_eq_of_noFloat (ft) (h : anyFloatVT ft.params = false)
    (h2 : anyFloatVT ft.results = false) : floatGuardImport pv86 ft = floatGuardImport floatPv86 ft
theorem floatGuardGlobal_eq_of_noFloat (gs) (h : gs.any (·.type.isFloat) = false) : …
theorem floatGuardBody_eq_of_noFloat (groups ft code) (h : floatInBody groups ft code = false) : …
-- no premise: under floatPv86 the guards are false for every module
theorem floatGuard_lifted (ft gs groups code) :
    floatGuardImport floatPv86 ft = false ∧ floatGuardGlobal floatPv86 gs = false ∧
      floatGuardBody floatPv86 groups ft code = false
```

**Not proved, and not claimed:** `checkD3F = checkD3` on float-free *chunks*. The guard equalities
above are the only float-specific step; the rest would need an induction over `prepare` and the
chunk pipeline showing no other site reads `NearCfg.floats`. This module must not be cited for
chunk-level additivity.

### 2.3 The four guard sites the task named

| Site | File | Change |
|---|---|---|
| `Prepare.lean:205` import type | `Prepare.floatGuardImport` | `!cfg.floats ∧` |
| `Prepare.lean:234` global | `Prepare.floatGuardGlobal` | `!cfg.floats ∧` |
| `Prepare.lean:315` body | `Prepare.floatGuardBody` | `!cfg.floats ∧`, extended to cover `floatLoad`/`floatStore`/`f32Const`/`f64Const` |
| `Exec.lean:325`, `Validate.lean:270,293`, `FiniteWasm.lean:132` | `execFloat`, signatures, `floatPartial` | real semantics |

## 3. Tests

All numbers below were produced in this session.

### 3.1 Directed kernel tests — build-gated (`Wasm/FloatTests.lean`, 141 theorems)

Imported from `NearSpecV3.lean`, so `lake build` runs them: a wrong bit pattern breaks the build.
Every case is `decide`d by the kernel. Coverage by branch:

* **signed zero**: `+0+-0=+0`, `-0+-0=-0`, `x-x=+0`, `-0-+0=-0`, `+0·-3=-0`, `min(+0,-0)=-0`,
  `max(+0,-0)=+0`, `sqrt(-0)=-0`, `ceil(-0.5)=-0`, `floor(0.5)=+0`, `nearest(-0.4)=-0`,
  `trunc(-0.5)=-0`;
* **subnormals**: exact sums, the `minSub·0.5` underflow tie → `0`, `minSub·0.75` → `minSub`,
  `maxSub+minSub = minNorm` and back, `1/minSub = +inf`, promote/demote round-trip, the f64 grid
  exponent `2^-1074`;
* **infinities and overflow**: `maxFin+maxFin`, `inf-inf`, `inf·0`, `0/0`, `inf/inf`, `1/±0`,
  `maxFin·2`, `sqrt(±inf)`, `sqrt(-1)`, the packing kernel's overflow threshold and the value just
  below it;
* **NaN payloads**: every canonicalising op drops a `0x7FC12345` / `0x7FF8…12345` payload and the
  input's sign; a signalling NaN becomes the quiet canonical; `abs`/`neg`/`copysign`/`reinterpret`
  keep it; the two comparison rules (`ne` true, everything else false);
* **rounding ties**: 1.5→2, 2.5→2, 3.5→4, −1.5→−2; `trunc`/`floor`/`ceil` on ±1.5; the `2^24`
  significand ties (`2^24+1 → 2^24`, `2^24+3 → 2^24+4`); integer→float ties at `2^53`;
* **inexact `sqrt`**: `sqrt(0.5)` and `sqrt(2)` in both formats against independently computed
  IEEE values, plus a neighbour-inequality test (a one-ulp error fails the build);
* **conversion boundaries and traps**: `2^31−128` / `2^31` / `2^31+256`, `2^32−256` / `2^32`,
  `2^64−2048` / `2^64`, negative-for-`_u`, NaN, ±inf; the saturating forms (NaN→0, clamp both
  ways, 64-bit);
* **dispatch coverage**: one case per arm for all 70 opcodes, and `floatPartial`'s exact eight.

### 3.2 Operator differential vs an independent IEEE statement

`oracle/wasm-d3/tests/difftest_float.py` + `float_ref.py` (Python IEEE, with the two
nearcore-specific rules: canonical NaN, bit-preserving abs/neg/copysign/reinterpret):

```
seed 1..4, --cases 4:  79,742 cases/seed, 70 opcodes, 0 disagreements
                       (79,462 directed = every ordered edge pair; 280 generated/seed;
                        generated total 1,120 over 4 seeds)
```

### 3.3 Operator differential vs **pinned nearcore's own engine**

`float_nearcore.py`: a real Wasm module per opcode (constants → the operator → store →
`value_return`), executed by `oracle/wasm-d3`'s harness (nearcore 2.13.4 `prepare`+`run`, PV86,
Wasmtime/Winch, real instrumentation).

| check | result |
|---|---|
| values and trap kinds, directed edge pairs | 1,260 cases, **0 disagreements** (3,220 with `--limit 40`) |
| gas: full outcome line (`status burnt used`) for 1/2/3 copies of each operator | 210 modules, **0 disagreements** |
| **instrumented-module length** (nearcore `prepare` output vs `NearSpecV3.Wasm.Size`) | 140 modules, **0 disagreements** |

The gas check compares **totals**, not deltas: an earlier version compared one copy against two and
expected zero delta for pure operators, which was wrong because each repetition also re-emits its
store address, its constants and its store. That version was deleted, not left green.

### 3.4 Evidence paths

Every result in §3 is reproducible from `oracle/wasm-d3/tests/` and was re-run at the end of the
session with its output kept under `var/l2/evidence/` (git-ignored, like the rest of `var/`):

```
var/l2/evidence/difftest_float_s1.log    family=float cases=79742 opcodes=70 disagreements=0
var/l2/evidence/float_nearcore.log       values cases=1260 disagreements=0 ; gas modules=210 disagreements=0
                                         size modules=140 disagreements=0
var/l2/evidence/float_prepare.log        family=float-prepare cases=6 disagreements=0
var/l2/evidence/float_regression.log     both experiments DISCRIMINATE
var/l2/evidence/chunk_float.log          20 lifted, 80/80 tamper mutants rejected
```

### 3.5 Whole chunks

`chunk_float.py`, over the recorded corpus (26 cases naming `d3float`, `e.float`, nearcore `ok`):

```
candidates=26  float_blocked_and_lifted=20  blocked_earlier_by_other_lane=2
still_excluded_other_reason=4  failures=0
tamper: 80/80 rejected  {claim:20, witness:20, code:20, root:20}
```

A chunk only accepts if the computed state root, outcome root, receipts, gas and balance match the
endorsed header, so "accept" is a whole-chunk statement, not just a guard check. The four cases
that remain excluded carry another lane's condition (`gAlpha` gas ×3, ETH-implicit local contract
×1); two more were already excluded by D3α *before* reaching the float guard. `chunk_float.py`
counts those separately rather than as passes.

### 3.6 Preparation-only guards (`float_prepare.py`)

| module | D3α | floatPv86 |
|---|---|---|
| import-only f64 signature | `out-of-domain float in an imported function type` | `abort … LinkError`, gas **88,821,418** = nearcore |
| import-only f32 signature | same | same |
| f64 global | `out-of-domain float global` | `ok`, gas **95,403,466** = nearcore |
| f64 global, read and dropped | same | `ok`, gas **100,316,863** = nearcore |
| mutable f64 global | same | `ok`, gas 95,403,466 = nearcore |
| float signature called with the wrong type | — | `LinkError` on **both** sides (negative) |

### 3.7 Regression experiment (plan §5 item 2)

`float_regression.py` removes each mechanism and shows the targeted test fails:

* A. the D3α/floatPv86 verdict **pair** on a real `d3float` chunk — the lift is what changes the
  verdict (`out_of_domain (float type or operator in a function body)` → `accept`);
* B. the reference with the canonical-NaN rule removed disagrees with the kernel on **28/168** NaN
  cases. If canonicalisation were a no-op in the kernel this would pass in both modes.

## 4. Pinned semantics: where each rule comes from

| rule | pinned source |
|---|---|
| NaN results canonicalise; canonical value is `0x7FC00000` / `0x7FF8000000000000` | `wasmtime_runner/mod.rs:534` (`cranelift_nan_canonicalization(true)`), `:1243-1290` (nearcore's own regression test); Winch `visitor.rs:602-960,1159`, `isa/x64/masm.rs:716-738`, constants `masm.rs:16-17` |
| abs/neg/copysign/reinterpret are bit operations | Winch `isa/x64/masm.rs:607-690,1310-1328`; Cranelift's `is_fp_arith` excludes them |
| round-to-nearest, ties-to-even; `nearest` = `roundsd` imm 0 | Winch `isa/x64/asm.rs:1565-1588`; SSE add/sub/mul/div are RN-even |
| `min`/`max` sign-of-zero via `orps`/`andps`; NaN via add | `cranelift-codegen-0.132.0/src/isa/x64/inst/emit.rs:783-880` |
| trapping conversions → `WasmTrap(IllegalArithmetic)` | `wasmtime_runner/mod.rs:393`, `trap_classification.rs:18` |
| float gas: one `regular_op_cost`; the 8 truncations are `cvtop_partial` (a `pre` point) | `finite-wasm-0.6.1/src/instruction_categories.rs:167-180`, `src/gas/mod.rs:419-420`; `regular_op_cost = 822_756` at `runtime_configs/parameters.snap:110` |
| floats are in the validator's feature set at PV86 | `features.rs:47-59` (`floats: true`, `saturating_float_to_int: true`) |

The compiler/wrapper versions and the harness build recipe are in
`oracle/wasm-d3/README.md`; the harness binary used here is
`/tmp/opencode/target-wasm-d3/release/near-wasm-d3-harness` (the shared
`/data/illia/nearproof-deps/target-wasm-d3` was deleted mid-session under disk pressure and was
rebuilt into the lane's own target dir).

## 5. Artifact hashes

```
8c50747c442ba4e67c5e1ae98c24cc31f9eded50a89adf17e89ebd27861fe820  Wasm/Float.lean
a7735325dade0120d4909033747c516727655e0e01853c11be183d5c0334287a  Wasm/FloatTests.lean
c4732c25fe30d47bfa63d54087c7a6863b2064044d0a3f934ed44e8b55c3aefb  ChallengeChunkV3Float.lean
11efdae5445ade42a4b3073896aea047c96439a9e694ca9742810bff6bbecf8a  Wasm/Prepare.lean
2a831b0f5c9d2a55de330ef4d806990a3cd9be3c31adcef5cb7169c422a3ccf9  nearspec-v3-check-d3f
40c193a408b5ead4ab2c9f8462c0a32323eb650338ce80c170eea6989324865b  nearspec-v3-check-d3
```

The D3α checker binary's hash differs from the one recorded in
`var/d3-runs/report-d3-full.json` (`b4154b21…`) because the Lean library was rebuilt by this lane.
The *relation* is unchanged; the binary is not byte-reproducible across library edits. That is why
the replay in §6 compares verdicts against the recorded per-case JSONL rather than trusting a hash.

## 6. Verification commands and results

```sh
cd spec/lean/v3 && lake build                       # exit 0, 168 jobs; FloatTests is in the closure
cd spec/lean/v3 && lake env lean NearSpecV3/Wasm/FloatAxioms.lean
                                                    # 33 #print axioms, all ⊆ {propext,
                                                    # Classical.choice, Quot.sound}; no sorryAx
make pin-check                                      # exit 0
python3 tools/d3/lean_chunk_coverage.py --repo . \
    --nearcore /data/illia/nearproof-deps/nearcore \
    --check docs/research/lean-chunk-coverage.json   # "matches pinned sources"
cd oracle/wasm-d3 && cargo build --release --locked   # harness
cd oracle/wasm-d3/lean && lake build nearspec-v3-check-d3f nearspec-v3-check-d3 \
    nearspec-v3-test-float nearspec-v3-wasm
cd oracle/wasm-d3/tests && python3 difftest_float.py --cases 4 --seed 1..4   # 0 disagreements
cd oracle/wasm-d3/tests && python3 float_nearcore.py --limit 12              # 0 value, 0 gas
cd oracle/wasm-d3/tests && python3 float_prepare.py                          # 6/6
cd oracle/wasm-d3/tests && python3 chunk_float.py                            # 20 lifted, 80/80 tamper
cd oracle/wasm-d3/tests && python3 float_regression.py                        # both discriminate
python3 tools/d3/replay_d3_float.py --jobs 20                                # see §6.1
```

**Protected surface, verified untouched against the true base `a5ef42e0c`:**

```sh
git diff --stat a5ef42e0c..HEAD -- \
  spec/lean/v3/NearSpecV3/D3/FunctionCall.lean \
  spec/lean/v3/NearSpecV3/ChunkValidationD2.lean \
  spec/tools/build_challenge_draft_v3_chunk.py
# (no output)
```

`gAlpha`, the D2 cap plumbing and the draft generator are byte-identical. `checkD3` is unchanged;
`checkD3F` is a separate entry point with a separate driver (`nearspec-v3-check-d3f`).

No `sorry`, `admit`, `native_decide` or new `axiom` in any L2 file (grep-checked; the axiom audit
prints the closure of each new theorem).

### 6.1 D3α regression over the recorded corpus

`tools/d3/replay_d3_float.py` runs **both** checkers over all 115,284 recorded cases (4 corpora ×
{d3, mutants, ood}), then compares:

* each D3α verdict against the rules in `var/d3-runs/make_report.py` (an `out_of_domain` on an
  in-D3α case is a disagreement; accept/reject must match `meta.expected_rel`; the `e.g_alpha` and
  `e.code_cache` conditions must coincide with the oracle's marks);
* each verdict *change* against `meta.json`: the only admissible change is
  `out_of_domain → accept|reject` on a case with `e.float`, landing on nearcore's own verdict.

Report: `/tmp/opencode/d3replay-full/report.json`. **Status at hand-off: the run was still in
progress** (it was restarted once after a mid-run library rebuild briefly unlinked the checker
binary; see §7). The subsample results below are complete runs of the same script; the full run's
report must be read when it finishes. This is the one open verification item — see §7.

Subsample results (complete runs, same script):

```
--limit 40, all 4 corpora: 480 cases, 112 D3alpha ood, 4 float moves, 0 D3alpha regressions,
                            0 unexpected moves
--limit 200, d3c9:         600 cases, 150 D3alpha ood, 12 float moves, 0 D3alpha regressions,
                            0 unexpected moves
```

Every observed move was a `d3float` chunk going `out_of_domain → accept` with nearcore `ok`.

**Verified against the recorded baseline, not just internally:** 200 D3α cases of `d3c7/d3` were
re-run through the new checker and compared with the recorded per-case JSONL
(`var/d3-runs/full-d3c7/lean.jsonl` in the plan worktree, the 115,284-case run behind
`report-d3-full.json`): **0 mismatches, comparing both the verdict and the exact reason string**.
So `checkD3` is unchanged on that sample, not merely self-consistent — which is the property that
matters, because this lane rebuilt the library the old baseline binary came from.

## 7. What is not done — the honest list

1. **The full 115,284-case D3α replay did not finish within the session.** Nothing in the part
   that ran had regressed, and the 1,080-case subsample is clean, but the complete run must be
   finished before L2 claims "no D3α regression on the recorded corpus". Command in §6 (about
   75 minutes at `--jobs 16` on this host); the report lands in
   `/tmp/opencode/d3replay-full/report.json` and must show `d3alpha_regressions: 0` plus
   `unexpected_moves: 0`.

   *Operational note:* rebuilding the Lean library or the checker exes while the replay is running
   unlinks the binary under it and the worker fails with `FileNotFoundError`. Finish builds first,
   then start the replay.
2. **Chunk-level additivity is not proved** (§2.2). Guard-level additivity is.
3. **Kernel = nearcore is measured, not proved**, and only on the operator and single-chunk level:
   1,260 directed operator cases + 210 gas modules + 20 whole chunks. No refinement theorem.
4. **No generated float workload.** Whole-chunk coverage is the 26 recorded `d3float` chunks (one
   contract). A generator that emits float contracts with varied operators would be the real fix;
   `oracle/v3-d3/contracts/d3float.wat` is the only float contract in the corpus.
5. **`pow`/`fma` are absent by design** — not in the Wasm MVP, and `Decode.lean` rejects them.
6. **Performance is irrelevant but worth knowing**: `sqrt` is a 64-step binary search, `div` a
   scaled integer division. Both are kernel-reducible; neither is fast. `bitLen`'s 4096 fuel
   bounds every operand formed here; an operand beyond that would silently truncate the bit length.
7. **`--floats` is a test-only switch on the driver's `prepare` path.** `checkD3F` uses it through
   `floatPv86`; no signed artifact reads it.

## 8. Files safe for the next agent to edit

* `spec/lean/v3/NearSpecV3/Wasm/Float.lean` — the kernel.
* `spec/lean/v3/NearSpecV3/Wasm/FloatTests.lean` — the directed tests (imported by
  `NearSpecV3.lean`; keep it there so `lake build` runs them).
* `spec/lean/v3/NearSpecV3/Wasm/FloatAxioms.lean` — the axiom audit script.
* `spec/lean/v3/NearSpecV3/ChallengeChunkV3Float.lean` — the successor relation.
* `oracle/wasm-d3/tests/float_ref.py`, `difftest_float.py`, `float_nearcore.py`,
  `float_prepare.py`, `chunk_float.py`, `float_regression.py`.
* `oracle/wasm-d3/lean/{MainD3F,TestFloat}.lean`, `Main.lean`'s `--floats` flag.
* `tools/d3/lean_chunk_coverage.py` (the float rows are derived there) and
  `tools/d3/replay_d3_float.py`.

**Do not edit** `D3/FunctionCall.lean` (`gAlpha`, `checkD3`), `ChunkValidationD2.lean`'s cap
plumbing, `spec/tools/build_challenge_draft_v3_chunk.py`, or `challenges/drafts/*.json`.

## 9. Next executable step

1. Finish the replay: `python3 tools/d3/replay_d3_float.py --jobs 20` and require
   `d3alpha_regressions: 0, unexpected_moves: 0` (§6.1). This is the only outstanding *verification*
   item.
2. Add a float contract to the oracle workload that exercises operators the single `d3float`
   contract does not (comparisons, `min`/`max`, `copysign`, the saturating truncations), then
   regenerate a small float corpus and re-run `chunk_float.py` — that is what turns "20 chunks, one
   contract" into real whole-chunk coverage.
3. If chunk-level additivity is wanted as a theorem, prove it as an induction over `prepare` plus
   the chunk pipeline with a hypothesis "no site other than the three guards reads
   `NearCfg.floats`"; the guard lemmas in `ChallengeChunkV3Float.lean` are the base case.
