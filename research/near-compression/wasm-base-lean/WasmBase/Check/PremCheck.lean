import WasmBase.Main.SegSoundX
/-!
# WasmBase.Check.PremCheck — sound checkers for the trace-only premises of `seg_sound` / `wasm_base_sound_m2` (E2E M4c NV)

The extra premises of lane A's soundness theorems that mention only the trace and the publics
(not the module `X`, the gas map `sg`, or a spec state) are decidable on a concrete trace.  Each
has a Boolean checker here with a soundness theorem:

| premise | checker | theorem |
|---|---|---|
| `CutoHiLimbs tr` | `checkCutoHi` | `checkCutoHi_sound` |
| `HostBLinked tr pub` | `checkHostBLinked` | `checkHostBLinked_sound` |
| `RegCLinked tr pub` | `checkRegCLinked` | `checkRegCLinked_sound` |
| `TombDead tr pub (finS tr pub)` | `checkTombDead` | `checkTombDead_sound` |
| `(initS tr pub).Nodup`, `hst0`, `hlen`, `htin` | `decide` | (`Decidable`) |

Running them on the honest dumps (`wasmbase-tool holds`) witnesses that these premises are
satisfiable together with `HoldsX`/`ChipIf` on the same trace.
-/

namespace WasmBase
namespace HoldsCheck

open ZkFormal.Algebra Chips Local Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- `CutoHiLimbs`. -/
def checkCutoHi (tr : Trace) : Bool :=
  (List.range (tr.height 31)).all fun r =>
    !(rowNat tr 31 r 0 == 1) || (List.range 7).all fun k => decide (rowNat tr 31 r (12 + k) < 2 ^ 21)

theorem checkCutoHi_sound {tr : Trace} (h : checkCutoHi tr = true) : CutoHiLimbs tr := by
  intro r hr ha k hk
  have h1 := List.all_eq_true.mp h r (List.mem_range.mpr hr)
  simp only [ha, beq_self_eq_true, Bool.not_true, Bool.false_or] at h1
  simpa using List.all_eq_true.mp h1 k (List.mem_range.mpr hk)

/-- `rowAct` as a Boolean. -/
def actB (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : Bool :=
  ((T.inters.getD 0 default).count.eval (tr.row pub t r)).toNat == 1

theorem actB_iff {T : Table} {tr : Trace} {pub : List F} {t r : Nat} :
    actB T tr pub t r = true ↔ rowAct T tr pub t r := by
  simp [actB, rowAct]

/-- `HostBLinked`. -/
def checkHostBLinked (tr : Trace) (pub : List F) : Bool :=
  ((List.range (tr.height 25)).all fun r' => !actB HostB.table tr pub 25 r' ||
    (List.range (tr.height 22)).any fun r => actB Host.table tr pub 22 r &&
      rowNat tr 25 r' HostB.ts == rowNat tr 22 r cTs && rowNat tr 25 r' HostB.hid == rowNat tr 22 r Host.hid) &&
  ((List.range (tr.height 22)).all fun r => (List.range (tr.height 22)).all fun r' =>
    !(actB Host.table tr pub 22 r && actB Host.table tr pub 22 r' &&
      rowNat tr 22 r cTs == rowNat tr 22 r' cTs && rowNat tr 22 r Host.hid == rowNat tr 22 r' Host.hid) || r == r')

theorem checkHostBLinked_sound {tr : Trace} {pub : List F} (h : checkHostBLinked tr pub = true) :
    HostBLinked tr pub := by
  simp only [checkHostBLinked, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun r' hr' ha => ?_, fun r r' hr ha hr' ha' e1 e2 => ?_⟩
  · have := List.all_eq_true.mp h1 r' (List.mem_range.mpr hr')
    rw [actB_iff.mpr ha] at this
    simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      beq_iff_eq] at this
    obtain ⟨r, hr, ⟨⟨ha2, e1⟩, e2⟩⟩ := this
    exact ⟨r, hr, actB_iff.mp ha2, e1, e2⟩
  · have := List.all_eq_true.mp (List.all_eq_true.mp h2 r (List.mem_range.mpr hr)) r' (List.mem_range.mpr hr')
    rw [actB_iff.mpr ha, actB_iff.mpr ha'] at this
    simpa [e1, e2] using this

/-- `RegCLinked`. -/
def checkRegCLinked (tr : Trace) (pub : List F) : Bool :=
  (List.range (tr.height 27)).all fun r' => !(rowNat tr 27 r' Reg.act == 1) ||
    (List.range (tr.height 22)).any fun r => actB Host.table tr pub 22 r &&
      rowNat tr 27 r' Reg.ts == rowNat tr 22 r cTs && rowNat tr 27 r' Reg.hid == rowNat tr 22 r Host.hid

theorem checkRegCLinked_sound {tr : Trace} {pub : List F} (h : checkRegCLinked tr pub = true) :
    RegCLinked tr pub := by
  refine ⟨fun r' hr' ha => ?_⟩
  have := List.all_eq_true.mp h r' (List.mem_range.mpr hr')
  simp only [ha, beq_self_eq_true, Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨r, hr, ⟨⟨ha2, e1⟩, e2⟩⟩ := this
  exact ⟨r, hr, actB_iff.mp ha2, e1, e2⟩

/-- `TombDead tr pub fin`. -/
def checkTombDead (tr : Trace) (pub : List F) (fin : List Msg) : Bool :=
  (List.range (tr.height 14)).all fun r => (Ret.tk.eval (tr.row pub 14 r)).toNat == 0 ||
    (decide (rowNat tr 14 r Ret.kCid < 2 ^ 28) && rowNat tr 14 r Ret.kCid != 0 &&
      fin.all fun x => !(x.space == 4) || x.slot != rowNat tr 14 r Ret.kCid)

theorem checkTombDead_sound {tr : Trace} {pub : List F} {fin : List Msg}
    (h : checkTombDead tr pub fin = true) : TombDead tr pub fin := by
  intro r hr hk
  have := List.all_eq_true.mp h r (List.mem_range.mpr hr)
  have hk' : ((Ret.tk.eval (tr.row pub 14 r)).toNat == 0) = false := by simpa using hk
  rw [hk', Bool.false_or] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.all_eq_true] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨h1, h2, fun x hx hs => ?_⟩
  have := h3 x hx
  simpa [hs] using this

/-- All trace-only premises of `seg_sound` as one Boolean (with their names, for reporting). -/
def segPrems (tr : Trace) (pub : List F) : List (String × Bool) :=
  [("CutoHiLimbs", checkCutoHi tr),
   ("HostBLinked", checkHostBLinked tr pub),
   ("RegCLinked", checkRegCLinked tr pub),
   ("(initS tr pub).Nodup", decide (initS tr pub).Nodup),
   ("TombDead tr pub (finS tr pub)", checkTombDead tr pub (finS tr pub)),
   ("hst0: pub[pubStatus] = 0", decide (pub.getD Boundary.pubStatus 0 = 0)),
   ("hlen: |actListM2| < 2^28", decide ((actListM2 tr pub).length < 2 ^ 28)),
   ("htin: pub[pubTIn] < 2^28", decide ((pub.getD pubTIn 0).toNat < 2 ^ 28))]

/-- The trace-only premises of `wasm_base_sound_m2` (`Holds (wasmBaseM2Air nloc ngl)`). -/
def m2Prems (nloc ngl : Nat) (tr : Trace) (pub : List F) : List (String × Bool) :=
  let init := (initRaw nloc pub).map decMsg ++
    ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg))
  [("HostBLinked", checkHostBLinked tr pub),
   ("RegCLinked", checkRegCLinked tr pub),
   ("hst12/hstStatus: pub[pubStatus] ∈ {1, 2}",
     decide (pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) ∨ pub.getD Boundary.pubStatus 0 = ((2 : Nat) : F))),
   ("hlen: |actListM2| < 2^28", decide ((actListM2 tr pub).length < 2 ^ 28)),
   ("hinitTp: every init message has tp = 0", init.all fun x => x.tp == 0),
   ("hinitNd: init messages Nodup", decide init.Nodup)]

end HoldsCheck
end WasmBase

#print axioms WasmBase.HoldsCheck.checkCutoHi_sound
#print axioms WasmBase.HoldsCheck.checkHostBLinked_sound
#print axioms WasmBase.HoldsCheck.checkRegCLinked_sound
#print axioms WasmBase.HoldsCheck.checkTombDead_sound
