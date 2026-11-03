import WasmBase.Main.HostRegWF
import WasmBase.Main.StepSide

/-!
# WasmBase.Main.HostVacuity — the HOST-row premises over all related states are unsatisfiable

**The finding (sub-lane M6, mechanised here).**  `RelW` reads a state only through its Wasm-visible
part and the gas register `gas.g` (`relW_of_vis`, `Main/HostRegWF.lean`).  Every HOST-row premise of
the segment theorems — `HoldRowS` (`RowFactsSeg` → `RowSpecSeg`), `HostRely.reg` (`HostRegRely`),
`HostRely.wf`, `HostRegCap` — quantifies over **every** related pre-state, hence over every host-side
part `σ`.  But a host call's result depends on `σ`, while the row's messages (`outS`, hence the gas
units `S + fee`, and the successor gas segment) are fixed:

* `rowSpecSeg_cont_g` — under `RowSpecSeg`, a continuing step from a related pre-state lands at
  the gas register `g = segb' − R·(S_out − S_seg')`, a function of the row's out message and the
  successor segment alone;
* **`not_rowSpecSeg_of_sigma`** — so two related pre-states with the same Wasm-visible part and the
  same `g` (any two σ-variants: `relW_of_vis`) whose steps continue with *different* `g` refute
  `RowSpecSeg` (and `not_holdRowS_of_sigma` refutes `HoldRowS`);
* **`vacuity_witness`** — such a pair exists: a one-instruction function `call 0` with import 0 =
  `block_index`, and two states that differ only in `gas.burnt` (by 1) and `ctx.blockHeight`
  (10 vs 11): both steps continue (`callHost`), the post-states' `gas.g` differ (`g := remaining`,
  999999735231889 vs 999999735231888) and so do the pushed results (10 vs 11).  Evaluated by
  `decide` (kernel reduction of the spec `step`).

So `seg_sound*`, `seg_chain*`, `wasm_base_sound_m2` are vacuous on every trace with a continuing
host call whose result depends on `σ` (for `callHost` that is *every* continuing call: the
`g := gas.remaining` reset depends on `gas.burnt`).  The σ-pinned restatement is
`Main/SegSigma.lean` / `Main/SegSoundSigma.lean`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips
open NearSpecV3.Wasm hiding P
open HostFoot
set_option linter.unusedSimpArgs false

/-- **Under `RowSpecSeg`, a continuing step's gas register is fixed by the row.**  From a related
pre-state (with the gas side condition of the induction), a continuing step lands at
`R·((gasF outS).toNat − S_seg') + g' = segb'`. -/
theorem rowSpecSeg_cont_g {X : Ctx} {inS outS : List F} {cons prod : List Msg} {sgin sgout : Nat × Nat}
    (h : RowSpecSeg X inS outS cons prod sgin sgout)
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop}
    (R : RelW X E s f tps tpl t pc S live sgin.1 sgin.2) (hin : inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid)
    (hl : ∀ x ∈ cons, live x) (ht : t + 1 < P) (hS : S + X.maxFee < P) (hg0 : X.g0 < 2 ^ 64)
    (hgas : X.R * (S + X.maxFee - sgin.1) ≤ sgin.2) {s1 : St} (hs : step X.cfg X.p s = .cont s1) :
    X.R * ((gasF outS).toNat - sgout.1) + s1.gas.g = sgout.2 := by
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ := h E s f tps tpl t pc S live R hin hl ht hS hg0
  have hg' : X.R * (S + fee - sgin.1) ≤ sgin.2 :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hgas
  obtain ⟨h0, h1, h2⟩ := hsp hg'
  have eS : (gasF outS).toNat = S + fee := by
    rw [hout]; show ((S + fee : Nat) : F).toNat = _; exact Fp.toNat_cast_of_lt (by omega)
  rw [eS]
  rcases (by omega : hb = 0 ∨ hb = 1 ∨ hb = 2) with e | e | e
  · obtain ⟨s', hs', ⟨E', f', tps', tpl', -, -, -, R'⟩⟩ := h0 e
    rw [hs] at hs'; cases hs'
    exact R'.gas
  · obtain ⟨sN, hsN, -⟩ := h1 e
    rw [hs] at hsN; cases hsN
  · obtain ⟨sN, e', hsN, -⟩ := h2 e
    rw [hs] at hsN; cases hsN

/-- **`RowSpecSeg` is refuted by two σ-variants.**  If a pre-state `s` related at the row and another
state `s'` with the same Wasm-visible part and the same gas register (hence also related,
`relW_of_vis`) both take a continuing step, to different gas registers, the row's `RowSpecSeg`
fails (for every pair of segments). -/
theorem not_rowSpecSeg_of_sigma {X : Ctx} {inS outS : List F} {cons prod : List Msg} {sgin sgout : Nat × Nat}
    {E : Env} {s s' : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop}
    (R : RelW X E s f tps tpl t pc S live sgin.1 sgin.2) (hin : inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid)
    (hl : ∀ x ∈ cons, live x) (ht : t + 1 < P) (hS : S + X.maxFee < P) (hg0 : X.g0 < 2 ^ 64)
    (hgas : X.R * (S + X.maxFee - sgin.1) ≤ sgin.2)
    (hv : vis s' = vis s) (hg : s'.gas.g = s.gas.g)
    {s1 s2 : St} (hs1 : step X.cfg X.p s = .cont s1) (hs2 : step X.cfg X.p s' = .cont s2)
    (hne : s1.gas.g ≠ s2.gas.g) :
    ¬ RowSpecSeg X inS outS cons prod sgin sgout := by
  intro h
  have e1 := rowSpecSeg_cont_g h R hin hl ht hS hg0 hgas hs1
  have e2 := rowSpecSeg_cont_g h (relW_of_vis R hv hg) hin hl ht hS hg0 hgas hs2
  exact hne (by omega)

/-- **`HoldRowS` is refuted** by an active HOST row at which two σ-variants as above exist. -/
theorem not_holdRowS_of_sigma {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {r : Nat}
    (hr : r < tr.height 22) (ha : rowAct Host.table tr pub 22 r)
    {E : Env} {s s' : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop}
    (R : RelW X E s f tps tpl t pc S live (sg (rowNat tr 22 r 1)).1 (sg (rowNat tr 22 r 1)).2)
    (hin : rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid)
    (hl : ∀ x ∈ consCHS tr pub (22, r), live x) (ht : t + 1 < P) (hS : S + X.maxFee < P) (hg0 : X.g0 < 2 ^ 64)
    (hgas : X.R * (S + X.maxFee - (sg (rowNat tr 22 r 1)).1) ≤ (sg (rowNat tr 22 r 1)).2)
    (hv : vis s' = vis s) (hg : s'.gas.g = s.gas.g)
    {s1 s2 : St} (hs1 : step X.cfg X.p s = .cont s1) (hs2 : step X.cfg X.p s' = .cont s2)
    (hne : s1.gas.g ≠ s2.gas.g) :
    ¬ HoldRowS X tr pub sg := fun H =>
  not_rowSpecSeg_of_sigma R hin hl ht hS hg0 hgas hv hg hs1 hs2 hne (H r hr ha).spec

/-! ## A concrete pair of σ-variants with different host results -/

namespace Vacuity

/-- One defined function whose body is `call 0`; import 0 is `block_index`. -/
def pf0 : PFunc := { type := ⟨#[], #[]⟩, locals := #[], code := #[.call 0], endOf := #[0], elseOf := #[0],
                     gas := #[none], stackCharge := 0, prologueGas := 0 }
def p0 : Prepared := { m := { imports := #[{ module := "env", name := "block_index", kind := 0, idx := 0 }] },
                       ctx := default, funcs := #[pf0] }
def fr0 : Frame := { fn := 0, pc := 0, locals := #[], labels := [], base := 0 }
def gA : Gas := { burnt := 0, prepaid := 1000000000000000, limit := 1000000000000000, g := 1000000000000000 }
/-- State A: nothing burnt yet, block height 10 (the `CallCtx` default). -/
def sA : St := { frames := [fr0], pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[],
                 datas := #[], stackRem := 0, gas := gA }
/-- State B: as A, but one gas unit burnt and block height 11 — a different host side `σ`. -/
def sB : St := { sA with gas := { gA with burnt := 1 }, ctx := { blockHeight := 11 } }

def gOf : Res → Option Nat
  | .cont s => some s.gas.g
  | _ => none
def topOf : Res → Option Nat
  | .cont s => s.stack.back?.map Val.bits
  | _ => none

theorem cont_of_gOf {r : Res} {n : Nat} (h : gOf r = some n) : ∃ s, r = .cont s ∧ s.gas.g = n := by
  cases r <;> simp_all [gOf]

theorem gOf_A : gOf (step {} p0 sA) = some 999999735231889 := by decide
theorem gOf_B : gOf (step {} p0 sB) = some 999999735231888 := by decide
theorem topOf_A : topOf (step {} p0 sA) = some 10 := by decide
theorem topOf_B : topOf (step {} p0 sB) = some 11 := by decide

/-- **The witness.**  `sA`, `sB` have the same Wasm-visible part and gas register; both steps
continue (a `block_index` host call), to different gas registers and different pushed values. -/
theorem vacuity_witness :
    vis sA = vis sB ∧ sA.gas.g = sB.gas.g ∧
    ∃ tA tB, step {} p0 sA = .cont tA ∧ step {} p0 sB = .cont tB ∧ tA.gas.g ≠ tB.gas.g ∧
      tA.stack.back?.map Val.bits = some 10 ∧ tB.stack.back?.map Val.bits = some 11 := by
  obtain ⟨tA, hA, gA'⟩ := cont_of_gOf gOf_A
  obtain ⟨tB, hB, gB'⟩ := cont_of_gOf gOf_B
  have h1 := topOf_A; have h2 := topOf_B
  rw [hA] at h1; rw [hB] at h2
  exact ⟨rfl, rfl, tA, tB, hA, hB, by rw [gA', gB']; decide, h1, h2⟩

end Vacuity

#print axioms rowSpecSeg_cont_g
#print axioms not_rowSpecSeg_of_sigma
#print axioms not_holdRowS_of_sigma
#print axioms Vacuity.vacuity_witness

end WasmBase
