import ZkFormal.NearV3.Candidates.ProcPriorValueLengthLift
import ZkFormal.Near.Extract.Segments
namespace ZkFormal.NearV3.Candidates.ProcPriorValueLength
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Rcpt.Candidates.SizeCount

theorem lift_mult (tr : Trace Fp) (tt r : Nat) (selected : Nat→Bool) (pub : List Fp) (es : List Expr)
    (hb:∀ e∈es,e.colBound≤gate) (k : Nat) :
    Interaction.multNat.go (liftTrace tr tt selected) tt r pub es k=Interaction.multNat.go tr tt r pub es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [Interaction.multNat.go]
    rw [lift_eval tr tt r selected pub e (hb e (by simp)),ih (fun x hx=>hb x (by simp [hx]))]

theorem lift_interaction (tr : Trace Fp) (tt r : Nat) (selected : Nat→Bool) (pub : List Fp)
    (i : Interaction) (hi:i∈valTable.interactions) :
    i.multNat (liftTrace tr tt selected) tt r pub=i.multNat tr tt r pub ∧
    i.msgVal (liftTrace tr tt selected) tt r pub=i.msgVal tr tt r pub := by
  constructor
  · apply lift_mult
    intro e he
    exact old_bounds e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  · unfold Interaction.msgVal
    apply List.map_congr_left
    intro e he
    exact lift_eval tr tt r selected pub e (old_bounds e
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_right _ he⟩)))


theorem old_row_traffic (tr : Trace Fp) (tt r : Nat) (selected : Nat→Bool) (pub : List Fp)
    (bus : Nat) (sd : Bool) :
    rowTraffic valTable.interactions (liftTrace tr tt selected) tt r pub bus sd=
      rowTraffic valTable.interactions tr tt r pub bus sd := by
  unfold rowTraffic
  apply flatMap_congr'
  intro i hi
  obtain ⟨hm,hv⟩:=lift_interaction tr tt r selected pub i hi
  rw [hm,hv]

theorem announcement (lb : Nat) (tr : Trace Fp) (tt r : Nat) (selected : Nat→Bool) (pub : List Fp)
    (bus : Nat) (sd : Bool) :
    rowTraffic [interaction lb] (liftTrace tr tt selected) tt r pub bus sd=
      if lb=bus ∧ sd=true ∧ selected r=true then
        [[(c ValV3.vid).eval tr tt r pub,(c ValV3.len).eval tr tt r pub]] else [] := by
  have hz:(0:Fp)≠1:=by decide +kernel
  simp only [rowTraffic,List.flatMap_cons,List.flatMap_nil,List.append_nil,interaction,
    Interaction.multNat,Interaction.multNat.go,lift_gate,Interaction.msgVal,
    List.map_cons,List.map_nil,Nat.pow_zero,Nat.add_zero]
  rw [lift_eval tr tt r selected pub (c ValV3.vid) (by decide +kernel),
    lift_eval tr tt r selected pub (c ValV3.len) (by decide +kernel)]
  by_cases hb:lb=bus <;> cases sd <;> cases hs:selected r <;> simp [hb,hz]

/-- Exact new traffic plus unchanged old traffic. No hidden provider or
consumer multiplicity assumption is folded into this equation. -/
theorem row_traffic (lb : Nat) (tr : Trace Fp) (tt r : Nat) (selected : Nat→Bool) (pub : List Fp)
    (bus : Nat) (sd : Bool) :
    rowTraffic (table lb).interactions (liftTrace tr tt selected) tt r pub bus sd=
      rowTraffic valTable.interactions tr tt r pub bus sd ++
      (if lb=bus ∧ sd=true ∧ selected r=true then
        [[(c ValV3.vid).eval tr tt r pub,(c ValV3.len).eval tr tt r pub]] else []) := by
  change rowTraffic (valTable.interactions++[interaction lb]) _ _ _ _ _ _=_
  simp only [rowTraffic,List.flatMap_append]
  change rowTraffic valTable.interactions _ _ _ _ _ _++rowTraffic [interaction lb] _ _ _ _ _ _=_
  rw [old_row_traffic,announcement]
  rfl

end ZkFormal.NearV3.Candidates.ProcPriorValueLength
