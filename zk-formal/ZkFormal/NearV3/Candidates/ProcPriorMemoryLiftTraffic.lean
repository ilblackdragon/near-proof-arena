import ZkFormal.NearV3.Candidates.ProcPriorMemoryLiftLocal
import ZkFormal.Near.Extract.Segments
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E ZkFormal.Near

theorem lift_mult (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (es : List Expr)
    (hb:∀ e∈es,e.colBound≤11) (k : Nat) :
    Interaction.multNat.go (liftTrace tr tt pub) tt r pub es k=Interaction.multNat.go tr tt r pub es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [Interaction.multNat.go]
    rw [lift_eval tr tt r pub e (hb e (by simp)),ih (fun x hx=>hb x (by simp [hx]))]

theorem lift_interaction (wb rb cb : Nat) (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (i : Interaction) (hi:i∈(ProcPriorMemoryTable.table wb rb cb).interactions) :
    i.multNat (liftTrace tr tt pub) tt r pub=i.multNat tr tt r pub ∧
    i.msgVal (liftTrace tr tt pub) tt r pub=i.msgVal tr tt r pub := by
  constructor
  · apply lift_mult
    intro e he
    exact old_bounds wb rb cb e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  · unfold Interaction.msgVal
    apply List.map_congr_left
    intro e he
    exact lift_eval tr tt r pub e (old_bounds wb rb cb e
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_right _ he⟩)))

/-- Exact all-bus traffic of the executable gate extension, at every row. -/
theorem lift_row_traffic (wb rb cb : Nat) (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) :
    rowTraffic (table wb rb cb).interactions (liftTrace tr tt pub) tt r pub bus sd=
      rowTraffic (ProcPriorMemoryTable.table wb rb cb).interactions tr tt r pub bus sd := by
  change rowTraffic (interactions wb rb cb) (liftTrace tr tt pub) tt r pub bus sd=
    rowTraffic (ProcPriorMemoryTable.interactions wb rb cb) tr tt r pub bus sd
  rw [row_traffic wb rb cb (liftTrace tr tt pub) tt r pub (lift_gate_eq tr tt r pub) bus sd]
  unfold rowTraffic
  apply flatMap_congr'
  intro i hi
  obtain ⟨hm,hv⟩:=lift_interaction wb rb cb tr tt r pub i hi
  rw [hm,hv]

/-- Whole physical table counts retain exact multiplicity and direction. -/
theorem lift_table_traffic (wb rb cb : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount (table wb rb cb).interactions (liftTrace tr tt pub) tt pub bus sd msg=
      tableBusCount (ProcPriorMemoryTable.table wb rb cb).interactions tr tt pub bus sd msg := by
  simp only [tableBusCount_eq,lift_row_traffic]
  rfl

end ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
