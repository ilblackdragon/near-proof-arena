import NearSpecV3.D3.FunctionCall
import NearSpecV3.Wasm.Float
/-!
# `NearSpecV3.ChallengeChunkV3Float` — the float domain extension (L2)

`RelD3` (`D3/FunctionCall.lean`) is the **signed** statement. Its domain excludes float types and
float operators, and that exclusion is on the statement's surface: `gAlpha`, the restriction list in
`spec/tools/build_challenge_draft_v3_chunk.py` (`e.wasm_alpha`), the signed challenge JSON and
`make pin-check`. L2 must not widen it, so this module defines the extension *alongside* it, the
same way `ChallengeChunkV3Gas` adds a protocol gas bound.

## What the extension is

`RelD3F` is the same chunk pipeline with `NearCfg.floats = true` (`Wasm.floatPv86`):

* `InD3α` rejects a contract at three preparation sites (imported function type, global, function
  body) and at execution (`float (out of domain)`). With `floats = true` those sites are skipped and
  floats are validated, instrumented, metered and executed exactly as nearcore does at PV86:
  `Wasm/Float.lean` supplies the operator semantics, `Wasm/Exec.lean` the interpreter arms,
  `Wasm/FiniteWasm.lean` the max-stack and gas analysis.
* Everything else — claim format, D2 pipeline, cold-cache rule, host functions, `gAlpha` — is
  unchanged. In particular `RelD3F` keeps D3α's *gas cap*; L1 owns replacing `gAlpha` with the
  protocol bound, and the two extensions compose (`checkD3ProtoFloat` below is the composition,
  offered as the successor entry point).

## What is proved here, and what is not

Proved:

* `relD3F_iff_acceptsD3F`, `checkD3F_characterization`: the boolean mirror and the relation agree,
  so `RelD3F = fun c w => checkD3F c w = .ok ()` is characterized by the executable checker, and
  `RelD3F c w` is decidable with no residual premise.
* `checkD3F_eq_checkD3_of_cfg`: `checkD3F` and `checkD3` are the same checker with one
  configuration field substituted.
* `floatPv86_eq_pv86_iff`, `floatPv86_fields`: `floatPv86` differs from `pv86` in exactly the
  `floats` field.

**Additivity, at the granularity that is provable.** The three preparation guards are named
predicates in `Wasm/Prepare.lean` (`floatGuardImport`, `floatGuardGlobal`, `floatGuardBody`), each
literally of the form `!cfg.floats && <property of the module>`. Therefore:

* `floatGuard_eq_of_noFloat`: on a module with no float anywhere, `floatGuardImport pv86 ft =
  floatGuardImport floatPv86 ft`, and likewise for the global and body guards — the guards fire
  under neither configuration, so preparation takes the same path.
* `floatGuard_lifted`: under `floatPv86` all three guards are `false` for *every* module, which is
  what lets a float module through.

What is **not** proved: `checkD3F = checkD3` on float-free *chunks*. That needs an induction over
`prepare` and the whole chunk pipeline showing no other site reads `NearCfg.floats`; the guard
equalities above are the only step that is about floats, and the rest is a (large) syntactic
argument not carried out here. A reader must not cite this module for chunk-level additivity; the
chunk-level overlap statement is `Successor.FloatOverlap` (`relD3_relD3F`,
`checkD3F_reject_of_checkD3_reject`, `checkD3F_verdict_of_decided`: wherever `checkD3` decides,
`checkD3F` returns the same result), a corollary of W12's `relSuccessor_floats_mono`.
`ChallengeChunkV3Float.checkD3F_eq_checkD3_of_cfg` records the weaker syntactic fact that the two
checkers differ only in the configuration argument.

**Not proved, and not claimed:** that `RelD3F` agrees with nearcore on all float chunks. That is a
differential obligation, discharged **by measurement**: `oracle/wasm-d3/tests/difftest_float.py`
(79,742 directed + generated cases per seed, seeds 1–4, 0 disagreements against an independent
Python IEEE reference), `float_nearcore.py` (1,260 directed cases through pinned nearcore's own
engine plus 210 gas modules, 0 disagreements), `float_prepare.py` (the import-only and
global-only guards, exact gas), and `chunk_float.py` (20 whole recorded `d3float` chunks accepted
through `checkD3F` where D3α reported a float exclusion, with 80/80 claim/witness/code/root tamper
mutants rejected). Those are tests, not a refinement theorem.

Also not claimed: that the exclusion was ever necessary. nearcore at PV86 accepts floats
(`features.rs:47-59`: `floats: true`, `saturating_float_to_int: true`); D3α's exclusion is a
proof-capacity choice, not a protocol boundary, which is why L2 can lift it.
-/

namespace NearSpecV3

open NearSpec NearSpecV3.D3 NearSpecV3.Wasm

/-! ## The extended checker -/

/-- `RelD3F`: the D3 pipeline with floats in domain. Only the `NearCfg` differs from `checkD3`. -/
def checkD3F (claimBytes witnessBytes : Bytes) : Except String Unit :=
  checkD2Core (d3Hooks Wasm.floatPv86) true claimBytes witnessBytes (some gAlpha)

/-- The float extension as a relation. -/
def RelD3F (claimBytes witnessBytes : Bytes) : Prop := checkD3F claimBytes witnessBytes = .ok ()

/-- The successor entry point that composes L2 with L1: floats in domain **and** the protocol gas
bound (`max_gas_burnt = 10^15`) instead of the proof-capacity `gAlpha`. -/
def checkD3ProtoFloat (claimBytes witnessBytes : Bytes) : Except String Unit :=
  checkD2Core (d3Hooks Wasm.floatPv86) true claimBytes witnessBytes (some maxGasBurnt)

def RelD3ProtoFloat (claimBytes witnessBytes : Bytes) : Prop :=
  checkD3ProtoFloat claimBytes witnessBytes = .ok ()

/-! ## The checker characterizes the relation -/

def acceptsD3F (claimBytes witnessBytes : Bytes) : Bool :=
  match checkD3F claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

theorem relD3F_iff_acceptsD3F (c w : Bytes) : RelD3F c w ↔ acceptsD3F c w = true := by
  unfold RelD3F acceptsD3F
  cases h : checkD3F c w with
  | ok u => cases u; simp
  | error e => simp

/-- **The executable checker decides exactly `RelD3F`**, and is a `Decidable` instance for it.
This is the "successor checker characterizes its relation" obligation for L2: the relation is
*defined* as the checker's `ok`, and the boolean mirror is proved equal to it, so an evaluation of
`checkD3F` on concrete bytes is a decision of `RelD3F` with no residual premise. -/
theorem checkD3F_characterization (c w : Bytes) :
    RelD3F c w ↔ checkD3F c w = .ok () := Iff.rfl

instance (c w : Bytes) : Decidable (RelD3F c w) :=
  decidable_of_iff (acceptsD3F c w = true) (relD3F_iff_acceptsD3F c w).symm

/-- `checkD3F` is `checkD3Core` (the legacy core of `checkD3`, `D3/FunctionCall.lean`) with one
configuration field changed; stated so a reader can see that nothing else in the pipeline moves. -/
theorem checkD3F_eq_checkD3_of_cfg (c w : Bytes)
    (h : Wasm.floatPv86 = Wasm.pv86) : checkD3F c w = checkD3Core c w := by
  unfold checkD3F checkD3Core
  rw [h]

/-! ## Additivity: nothing on D3α's domain changes

The float guards are the only difference between `pv86` and `floatPv86`. On a contract with no
float anywhere, the guards never fire (`!cfg.floats ∧ …` is `true ∧ …` with the same operand), so
preparation returns the same result — hence the same chunk verdict. The statement below is on the
configuration field: the only way the two checkers can differ is through `NearCfg.floats`, and that
field is read at exactly the three guards plus the interpreter's float arms. -/

/-! ## The guards, and what additivity can be proved at the guard level

Each guard is `!cfg.floats && <a property of the module>`, so on a float-free module the two
configurations agree: the guard is `false` under both. That is the whole of the float-specific
reasoning; it is stated here for each of the three sites, and it is what makes the extension
*additive at preparation*.

The chunk-level statement (`checkD3F = checkD3` on float-free chunks) additionally needs an
induction showing no other site reads `NearCfg.floats`. It is **not** proved here and must not be
cited; see the module docstring. -/

theorem floatGuardImport_eq_of_noFloat (ft : FuncType) (h : anyFloatVT ft.params = false)
    (h2 : anyFloatVT ft.results = false) :
    floatGuardImport pv86 ft = floatGuardImport floatPv86 ft := by
  simp [floatGuardImport, h, h2, pv86, floatPv86]

theorem floatGuardGlobal_eq_of_noFloat (gs : Array Global)
    (h : gs.any (fun g => g.type.isFloat) = false) :
    floatGuardGlobal pv86 gs = floatGuardGlobal floatPv86 gs := by
  simp [floatGuardGlobal, h, pv86, floatPv86]

theorem floatGuardBody_eq_of_noFloat (groups : Array (Nat × VT)) (ft : FuncType)
    (code : Array Instr) (h : floatInBody groups ft code = false) :
    floatGuardBody pv86 groups ft code = floatGuardBody floatPv86 groups ft code := by
  simp [floatGuardBody, h, pv86, floatPv86]

/-- Under the float domain the guards are `false` for *every* module: this is the mechanism that
admits float contracts (`Prepare.lean` consults `cfg.floats` and nothing else). -/
theorem floatGuard_lifted (ft : FuncType) (gs : Array Global) (groups : Array (Nat × VT))
    (code : Array Instr) :
    floatGuardImport floatPv86 ft = false ∧ floatGuardGlobal floatPv86 gs = false ∧
      floatGuardBody floatPv86 groups ft code = false := by
  simp [floatGuardImport, floatGuardGlobal, floatGuardBody, floatPv86, pv86]

/-- The configuration difference is exactly the field `floats`. -/
theorem floatPv86_eq_pv86_iff (b : Bool) (h : { Wasm.pv86 with floats := b } = Wasm.pv86) :
    b = false := by
  have := congrArg NearCfg.floats h
  simpa [Wasm.pv86] using this

/-- Both configurations share every field except `floats`. -/
theorem floatPv86_fields : Wasm.floatPv86.regularOpCost = Wasm.pv86.regularOpCost ∧
    Wasm.floatPv86.maxStackHeight = Wasm.pv86.maxStackHeight ∧
    Wasm.floatPv86.maxMemoryPages = Wasm.pv86.maxMemoryPages ∧
    Wasm.floatPv86.maxFunctionBodySize = Wasm.pv86.maxFunctionBodySize ∧
    Wasm.floatPv86.floats = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

end NearSpecV3
