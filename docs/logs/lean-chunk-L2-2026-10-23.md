# L2 — floating-point Wasm: lane log

Date: 2026-10-23. Owner: L2 lane. Status: **increment delivered, not merged; L2 as a whole is not
complete.**

| | |
|---|---|
| Worktree | `/data/illia/nearproof-wt/lean-chunk-L2` |
| Branch | `lane/lean-chunk-L2` |
| Base named in the task | `a5ef42e0c` |
| Branch tip before this log's commit | `124470b0b` (`L2: regression experiment (remove the mechanism, the test fails)`) |
| Uncommitted work at the time of writing | see §7 — it is **not** part of `de8cf0aa4` |
| Merged to `main`? | No. Not pushed. |

**The branch was not at the stated base when this session started.** It already carried four L2
commits (`942b94978`, `3dcd2464c`, `3bb189b38`, `1cb0b57f4`) plus later ones. The first thing this
session did was therefore an **audit of existing work**, not a fresh implementation. Finding and
correcting overclaims in that work (§4) is part of the deliverable.

---

## 1. Inventory rows owned

The task named five rows and `UQ-003`. Their definitions live in the **219-row** inventory
(`docs/research/lean-chunk-coverage.json` on `lane/lean-chunk-L0`), which is **not merged** into
`main` or into this branch. This branch's inventory is the older 114-row version and contains only
`L0-instr-float` and `L0-instr-integer` for owner `L2`. Rows below are reported against the task's
list; the two that this branch's generator actually emits are marked.

| Row | Subject | Status after this increment | Evidence / remaining |
|---|---|---|---|
| `L0-instr-float` *(present in this branch's inventory)* | float opcode semantics | **implemented** (operator semantics), **partial** (whole-domain) | §3, §5 |
| `L0-W-001` | float in an imported function type | **implemented and directed-tested** | `float_prepare.py`: import-only f32 + f64 signatures | 
| `L0-W-002` | float global | **implemented and directed-tested** | `float_prepare.py`: immutable, mutable, read-then-dropped f64 globals |
| `L0-W-003` | float type/operator in a function body + NaN determinism (H3) | **lifted and exercised end-to-end**; NaN determinism answered (§6) | §5 |
| `L0-W-012` | float operator in interpreter/validator/analyzer | **implemented** in all four sites | §2 |
| `UQ-003` | NaN payload/sign semantics of the pinned engine | **resolved from pinned source** (§6) | §6 |

`L0-W-001` / `L0-W-002` are covered by `oracle/wasm-d3/tests/float_prepare.py` (6 directed cases, 0
disagreements), which checks D3α excludes, `floatPv86` matches nearcore's outcome line *and gas*, and
that a wrong-arity call to an imported float signature is still a `LinkError` on both sides. Note the
import-only modules **abort** in nearcore (gas 88,821,418) rather than returning `ok` — the float
import carries no code, so the guard lift is evidenced by the *reason* changing from
`out-of-domain` to the same abort nearcore produces, not by an `accept`. That distinction is why the
row is `implemented` rather than `validated`.

## 2. What is implemented

### Kernel — `spec/lean/v3/NearSpecV3/Wasm/Float.lean` (579 lines)

A format-generic IEEE 754 kernel over **bit patterns as `Nat`**. No `Float`, `Float32`, `native_decide`
or `axiom`. One rounding routine (`roundPackS`: round-to-nearest-ties-to-even, sticky bit for
division/sqrt, gradual underflow, overflow to infinity).

Implemented operations — **all 70** float opcodes that carry no immediate:

* comparisons `0x5B–0x66`: eq, ne, lt, gt, le, ge for f32 and f64 (NaN-comparison rules included;
  `ne` is true when unordered, which is why it is `!eq`);
* `0x8B–0x98` / `0x99–0xA6`: abs, neg, ceil, floor, trunc, nearest, sqrt, add, sub, mul, div, min,
  max, copysign (f32 and f64);
* `0xA8–0xAB`, `0xAE–0xB1`: the 8 **trapping** `trunc_f*` conversions (trap = `IllegalArithmetic`);
* `0xB2–0xBB`: the 10 `convert_i*` and demote/promote;
* `0xBC–0xBF`: the 4 reinterprets;
* `0xFC00–0xFC07`: the 8 **saturating** `trunc_sat_f*`.

Plus, in the surrounding modules: float loads/stores (`0x2A/0x2B/0x38/0x39`) and `f32.const`/`f64.const`
with real little-endian immediates (`Wasm/Decode.lean`, `Wasm/Exec.lean`), float operator signatures
(`Wasm/Validate.lean`), max-stack size and gas classification (`Wasm/FiniteWasm.lean`), the
`NearCfg.floats` switch with `floatPv86` (`Wasm/Prepare.lean`), and `Val.f32`/`Val.f64` carrying bit
patterns so no host float can enter (`Wasm/Machine.lean`).

**Distinguish canonicalising from bit-preserving.** Canonicalising (produce `+qNaN` with a zero
payload whenever the mathematical result is NaN): add, sub, mul, div, min, max, sqrt, ceil, floor,
trunc, nearest, demote, promote, the truncating conversions. Bit-preserving (payload and sign kept):
abs, neg, copysign, the 4 reinterprets. This split is what the pinned engine does (§6) and is stated
as kernel-checked theorems (`add_nan_canonical_f32/f64`, `abs_f32_payload`, `neg_f32_payload`,
`copysign_f32_body`, `copysign_f32_sign`).

### Successor relation — `ChallengeChunkV3Float.lean`

`checkD3F` / `RelD3F` are the D3 pipeline with `NearCfg.floats = true`; `checkD3ProtoFloat` composes
this with L1's protocol gas bound. `RelD3` and `gAlpha` are **untouched**: `make pin-check` passes
(exit 0). Proved: the boolean mirror equals the relation (`relD3F_iff_acceptsD3F`), the relation is
`Iff.rfl`-characterised by the checker (`checkD3F_characterization`) and is `Decidable`, and
`floatPv86` differs from `pv86` in exactly the `floats` field (`floatPv86_fields`).

## 3. Measured results (all numbers below were produced in this session)

Harness: `oracle/wasm-d3` against pinned nearcore `44f7ae6cd` / 2.13.4, PV86, Wasmtime 45.0.0 with
`Strategy::Winch` on x86_64 and `cranelift_nan_canonicalization(true)` (rebuilt from scratch here:
`cargo build --release --locked` → `near-wasm-d3-harness`).

| Check | Command | Result |
|---|---|---|
| Kernel vs independent Python IEEE reference | `difftest_float.py --cases 6 --seed {1,2,3,4}`, and `--cases 2 --seed 11` | 79,882 cases × 4 seeds, 70 opcodes, **0 disagreements** (79,602 for the smaller run) |
| Kernel vs **pinned nearcore**, all directed edge pairs | `float_nearcore.py --limit 0 --seed {1,2,3,4}` | **23,458** cases × 4 seeds, **0 disagreements** |
| Same, sampled through `difftest_float.py` | `--nearcore` | 400-case subsample, **0 disagreements** |
| Whole-chunk float gas (1/2/3 copies per operator, full outcome lines) | part of `float_nearcore.py` | **210** modules, **0 disagreements** (e.g. `f64.add`×2: both sides 3,055,847,162) |
| Whole-chunk lift on real corpus witnesses | `chunk_float.py` | 26 candidate cases; **20/20** cases whose D3α verdict was a *float* exclusion are `accept` under `floatPv86` |
| Preparation-only rows `L0-W-001`/`L0-W-002` | `float_prepare.py` | 6 directed cases, **0 disagreements** (import-only f32/f64 signatures, immutable/mutable/read-dropped f64 globals, wrong-arity link error) |
| Whole-chunk tamper cases | `chunk_float.py` | **80/80** mutants rejected (20 each of claim, witness, code-blob, post-state-root byte-flips) |
| Directed kernel tests (build-gated) | `lake build` | **142** theorems in `Wasm/FloatTests.lean`, all kernel-`decide`d |

### 3.1 A real chunk, end to end

`ood/00-h10031-s3` of corpus `d3c9` (contains the `d3float` contract):

```
nearcore   = "ok"                 (recorded in meta.json)
checkD3    = out_of_domain        "out of domain (e.wasm-α): float type or operator in a function body"
checkD3F   = accept
```

### 3.2 The six cases that do *not* lift, and why none is a float

Of the 26 `d3float` + `e.float` + nearcore-accept cases, 6 remain excluded under `floatPv86`. All six
carry a **second** exclusion owned by another lane; none of the six reasons mentions floats:

| Case | Remaining reason | Lane |
|---|---|---|
| `ood/00-h10060-s3` | `e.wasm-α`: ETH-implicit account with a local contract | L4 / P5 |
| `ood/00-h10152-s3` | `e.g_alpha`: chunk gas 106,774,909,479,822 > G_α 3,450,888,781,824 | L1 |
| `ood/01-h10017-s0` | `e.g_alpha`: chunk gas 136,903,177,592,374 > G_α | L1 |
| `ood/01-h10028-s0` | `e.g_alpha`: chunk gas 4,869,289,584,590 > G_α | L1 |
| `ood/03-h10054-s3` | `w.shape`: non-ED25519 transaction key | L4 |
| `ood/03-h10069-s3` | `e.wasm-α`: ETH-implicit local contract | L4 / P5 |

Two of the 26 were rejected by D3α for an *earlier* non-float reason, so they prove nothing about
floats either way; `chunk_float.py` counts them separately rather than as passes.

## 4. Corrections made to pre-existing work in this branch

The branch's earlier commits contained claims that did not hold. Each was verified, then corrected;
none was left standing.

1. **`ChallengeChunkV3Float.lean` advertised two theorems that never existed** —
   `checkD3F_eq_checkD3_of_noFloat` ("on a float-free chunk, `RelD3F` and `RelD3` agree") and
   `d3F_extends_d3_on_floatContracts` ("a concrete contract D3α rejects and `RelD3F` admits"). Both
   appeared only in the module docstring. The header now states plainly that additivity is *not*
   established and must not be cited.
2. **A broken test entry point.** `difftest_float.py --nearcore` called `float_nearcore.compare`,
   which did not exist → `AttributeError`. The nearcore anchor had therefore never run through that
   path. Added a real `compare()`; it now runs (400-case subsample, 0 disagreements).
3. **A meaningless gas check.** The original `--gas` compared a body with one copy of an operator
   against a body with two, but `build_module` re-emits the store address, both operand constants
   *and* the store for each copy. The measured delta was const/store overhead: `f32.abs` (pure) and
   `i32.trunc_f32_s` (`cvtop_partial`) both produced 15,273,269, so the check distinguished nothing
   and its "0 disagreements" was vacuous. Removed, with the reasoning recorded in the docstring. The
   replacement compares **full outcome lines** (`ok <burnt> <used>` etc.) for 1/2/3 copies, which
   *is* sensitive to the charge-point classes (210 modules, 0 disagreements).
4. **Two false passes in a gas rewrite I attempted and discarded.** A local-based constructor was
   ill-typed for some operators, the harness returned gas `0` for both sides, and `0 − 0 = 0`
   "confirmed" a pure operator. Caught it, deleted the file rather than ship it.
5. **A wrong citation.** `Float.lean` attributed `regular_op_cost = 822,756` to `82.yaml`; that file
   contains only trie/table costs. The value is `parameters.snap:110`
   (`wasm_regular_op_cost 822_756`, last changed by `49.yaml:1`). Corrected.
6. **137 tests that the build did not run.** `Wasm/FloatTests.lean` was outside the root import
   closure, so `lake build` never checked it. Now imported from `NearSpecV3.lean`; the `.olean` is
   verified present after a clean rebuild.
7. **A real coverage hole in those tests.** Every `sqrt` case was *exact* (0, ±inf, −1, and a
   perfect-square f64 operand), so a one-ulp error on an irrational root passed all 137. Demonstrated
   by sabotaging `Fmt.sqrt` to round non-square roots down: the build stayed green. Added
   `sqrt_half_f32/f64`, `sqrt_two_f32/f64` and a neighbour-inequality test; the same sabotage now
   fails the build.
8. **`Float.lean`'s stale inventory row.** The generator hard-coded `L0-instr-float` as `missing`
   with the evidence "Exec.lean returns unmodeled 'float (out of domain)'", which is no longer true.
   Updated the row (now `implemented`, pointing at `NearSpecV3.Wasm.evalFloatOp`, with an explicit
   statement of what is *not* proved) and regenerated; the drift gate
   (`lean_chunk_coverage.py --check`) passes. Counts moved `missing` 20→19, `implemented` 91→92, and
   no other row changed.

## 5. Residual premises and what is deliberately not claimed

* **Not proved:** that the Lean kernel equals the pinned engine on any input. Agreement is *measured*
  (23,458 directed cases × 4 seeds at the operator level; 210 gas modules; 20 whole chunks). This is
  testing, not a refinement theorem.
* **Not proved:** additivity (`RelD3F` = `RelD3` on float-free chunks). Removed as a claim, not
  proved; see §4.1.
* **Not covered by tests:** float imported-function-type-only modules and float-global-only modules
  (`L0-W-001`, `L0-W-002`). The guards are lifted by inspection; there is no directed case.
* **`pow`/`fma` are absent by design** — Wasm MVP has neither, and `Decode.lean` rejects them; no gap.
* **Performance:** `sqrt` uses a 64-step binary search and `div` a scaled integer division. Correct
  and kernel-reducible, not fast. `Float.lean`'s `bitLen` fuel (4096) bounds the operands formed
  here; an out-of-range operand would silently truncate the bit length rather than fail.
* **Stale-binary trap:** `lake build` in `oracle/wasm-d3/lean` did not relink `nearspec-v3-test-float`
  after a kernel change in one instance. Always build the named exe (`lake build
  nearspec-v3-test-float`) before trusting a difftest result.

## 6. UQ-003 — NaN payload/sign determinism: **resolved**

The pinned engine canonicalises NaNs on every operation that can produce one, on **both**
architectures it can run on, and the canonical value is identical in both code generators.

* nearcore sets `cranelift_nan_canonicalization(true)` (`wasmtime_runner/mod.rs:534`), and the
  comment there states the setting also takes effect on Winch. x86_64 (production) uses
  `Strategy::Winch`; non-x86_64 (aarch64 development) uses `Strategy::Cranelift`
  (`wasmtime_runner/mod.rs:517-525`).
* **Winch**: `maybe_canonicalize_nan` is emitted after each arith/round/sqrt/conversion
  (`winch-codegen-45.0.0/src/visitor.rs:602-960,1159`), writing `CANONICAL_NAN_F32 =
  0x7fc00000` / `CANONICAL_NAN_F64 = 0x7ff8000000000000` when the result is unordered
  (`isa/x64/masm.rs:716-738`, `src/masm.rs:16-17`). The aarch64 Winch backend implements the same
  rule with the same constants (`isa/aarch64/masm.rs:736-762`).
* **Cranelift**: `do_nan_canonicalization` rewrites `fadd/fsub/fmul/fdiv/fmin/fmax/fma`, `ceil`,
  `floor`, `nearest`, `sqrt`, `trunc`, `fdemote`, `fpromote` into an `fcmp Unordered` + `select`
  against `Ieee32::NAN` / `Ieee64::NAN` (`cranelift-codegen-0.132.0/src/nan_canonicalization.rs:14-133`).
  Those constants are `EXPONENT_MASK | quiet_bit` (same file's `immediates.rs:555`), which is exactly
  `0x7fc00000` / `0x7ff8000000000000` — identical to Winch.
* Cranelift's own doc comment on `is_fp_arith` excludes `fneg`, `fabs`, `fcopysign` ("only operate on
  the sign bit"), matching Winch's lack of a canonicalisation pass on those. So the bit-preserving
  set is the same under both backends.

**Answer:** the pinned target produces `+qNaN` with a **zero payload and sign 0** for every NaN
result of a canonicalising operation, and preserves payload+sign for abs/neg/copysign/reinterpret.
This is stable across the two architectures the pinned build can select, because the two code
generators use the same constants and the same instruction set for the rewrite.

**What remains genuinely unknown:** this is a statement about *this* pinned configuration. It is not
a claim that arbitrary Wasmtime builds, other `Strategy` choices, or a future version behave the
same; and it says nothing about *signalling* NaNs being preserved as signalling (they are not —
canonicalisation turns any NaN, signaling or quiet, into the quiet canonical value). The empirical
anchor is 23,458 cases per seed against the real engine with non-canonical payloads and both NaN
signs in the edge set, plus nearcore's own regression test `nan_canonicalization`
(`wasmtime_runner/mod.rs:1243-1290`) and `test_nan_sign` (`tests/runtime_errors.rs:773-800`).

## 7. Uncommitted at the time of writing

`de8cf0aa4` is the last commit. The following are **working-tree changes only** and must be committed
by whoever continues:

```
 M docs/research/lean-chunk-coverage.json     (regenerated: L0-instr-float → implemented)
 M oracle/wasm-d3/tests/float_nearcore.py     (HARNESS default path; gas docstring)
 M spec/lean/v3/NearSpecV3.lean               (import FloatTests so the build runs it)
 M spec/lean/v3/NearSpecV3/Wasm/FloatAxioms.lean  (+5 sqrt axiom checks)
 M spec/lean/v3/NearSpecV3/Wasm/FloatTests.lean   (+5 inexact-sqrt tests)
 M tools/d3/lean_chunk_coverage.py            (L0-instr-float row text)
 D spec/lean/v3/AxiomCheckFloat.lean          (superseded by Wasm/FloatAxioms.lean)
```

## 8. Build / verification commands and results

```
cd spec/lean/v3 && lake build          # exit 0, 168 jobs; Float.olean, FloatTests.olean,
                                       # ChallengeChunkV3Float.olean all present
cd spec/lean/v3 && lake env lean NearSpecV3/Wasm/FloatAxioms.lean
                                       # 30 #print axioms; all ⊆ {propext, Classical.choice, Quot.sound}
make pin-check                         # exit 0
python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore <pinned> \
    --check docs/research/lean-chunk-coverage.json          # "matches pinned sources"
cd oracle/wasm-d3/tests && python3 difftest_float.py --cases 6 --seed 1   # 0 disagreements
cd oracle/wasm-d3/tests && python3 float_nearcore.py --limit 0 --seed 1   # 0 disagreements + 0 gas
cd oracle/wasm-d3/tests && python3 chunk_float.py                          # 20 lifted, 80/80 tamper
cd oracle/wasm-d3/tests && python3 float_prepare.py                        # 6 cases, 0 disagreements
```

No `sorry`, `admit`, `native_decide` or new `axiom` in any L2 file (grep-checked). The signed
challenge surface (`D3/FunctionCall.lean` `gAlpha`, `spec/tools/build_challenge_draft_v3_chunk.py`,
`challenges/drafts/*.json`) was **not** edited.

## 9. Next executable step

1. Commit §7.
2. *(done in this branch: `oracle/wasm-d3/tests/float_prepare.py`.)*
3. Prove additivity honestly or drop the idea: the missing `checkD3F_eq_checkD3_of_noFloat` needs a
   statement that `checkD3` never reaches a float guard on a float-free chunk — that is a real
   induction over `Prepare`, not a one-line `rfl`.
4. Extend whole-chunk coverage beyond the 26 recorded `d3float` witnesses (currently one contract in
   a handful of chunks), and re-run once L1 removes `gAlpha` so the 3 gas-capped cases can be
   exercised.

**Files safe for the next agent to edit:** `spec/lean/v3/NearSpecV3/Wasm/Float.lean`,
`FloatTests.lean`, `ChallengeChunkV3Float.lean`, `oracle/wasm-d3/tests/float_*.py`,
`chunk_float.py`, `tools/d3/lean_chunk_coverage.py`. **Do not** edit `D3/FunctionCall.lean`,
`spec/tools/build_challenge_draft_v3_chunk.py` or `challenges/drafts/*.json`.
