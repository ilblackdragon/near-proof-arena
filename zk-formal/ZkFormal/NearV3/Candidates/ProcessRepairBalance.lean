import ZkFormal.NearV3.Candidates.ProcessRepairInterface
namespace ZkFormal.NearV3.Candidates.ProcessRepairBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2

/-- An inventory reference only; validity of these original constraints is NOT claimed. -/
def reference (AP : AirP) : AirP := {AP with toAir:={AP.toAir with tables:=ProcPriorComparatorRoutedFamily.tables}}

theorem inventory {AP : AirP} {pub : List Fp} {tr : Trace Fp} (v:ProcessRepairInterface.View AP pub tr) :
    AP.tables.map Air.Table.interactions=ProcPriorComparatorRoutedFamily.tables.map Air.Table.interactions := by
  apply List.ext_getElem (by simpa using v.length)
  intro i hi hi'
  have h0:i<AP.tables.length:=by simpa using hi
  have h1:i<ProcPriorComparatorRoutedFamily.tables.length:=by simpa using hi'
  simp only [List.getElem_map]
  simpa only [getElem!_pos AP.tables i h0,getElem!_pos ProcPriorComparatorRoutedFamily.tables i h1] using v.wires i

theorem go (xs ys : List Air.Table) (h:xs.map Air.Table.interactions=ys.map Air.Table.interactions)
    (tr : Trace Fp) (pub : List Fp) (bus : Nat) (dir : Bool) (msg : List Fp) (off : Nat) :
    busCount.go tr pub bus dir msg xs off=busCount.go tr pub bus dir msg ys off := by
  induction xs generalizing ys off with
  | nil=>cases ys <;> simp_all [busCount.go]
  | cons x xs ih=>
    cases ys with
    | nil=>simp at h
    | cons y ys=>
      obtain ⟨hh,ht⟩:=List.cons.inj h
      change tableBusCount x.interactions tr off pub bus dir msg+_=tableBusCount y.interactions tr off pub bus dir msg+_
      rw [hh,ih ys ht]

theorem count {AP : AirP} {pub : List Fp} {tr : Trace Fp} (v:ProcessRepairInterface.View AP pub tr)
    (bus : Nat) (dir : Bool) (msg : List Fp) :
    busCount AP.toAir tr pub bus dir msg=busCount (reference AP).toAir tr pub bus dir msg :=
  go AP.tables _ (inventory v) tr pub bus dir msg 0

/-- Preserve global natural multiplicities/public packets without importing
any of the obsolete process equations. -/
theorem balance {AP : AirP} {pub : List Fp} {tr : Trace Fp} (v:ProcessRepairInterface.View AP pub tr)
    (bus : Nat) (msg : List Fp) :
    busCount (reference AP).toAir tr pub bus true msg+pubCount (reference AP) pub bus true msg=
    busCount (reference AP).toAir tr pub bus false msg+pubCount (reference AP) pub bus false msg := by
  have h:=v.valid.balance bus msg
  rw [count v bus true,count v bus false] at h
  exact h
end ZkFormal.NearV3.Candidates.ProcessRepairBalance
