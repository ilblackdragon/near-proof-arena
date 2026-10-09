import ZkFormal.NearV3.Candidates.ProcPriorProcessProjection
namespace ZkFormal.NearV3.Candidates.ProcessRepairInterface
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
set_option maxRecDepth 32768

/-- Soundness-facing contract: real validity belongs to the supplied AIR.
Only interaction inventory and unchanged components refer to the old family. -/
structure View (AP : AirP) (pub : List Fp) (tr : Trace Fp) : Prop where
  valid : HoldsP AP pub tr
  length : AP.tables.length=ProcPriorComparatorRoutedFamily.tables.length
  wires : ∀(t:Nat),(AP.tables[t]!).interactions=(ProcPriorComparatorRoutedFamily.tables[t]!).interactions
  component : ∀i,i<ProcPriorComparatorRoutedFamily.selected.length→i≠10→
    TableLocal (ProcPriorComparatorRoutedFamily.selected[i]!)
      (HorizontalTrace.project (ProcPriorProcessProjection.offset i) tr) 0 pub
  rest : ∀t,t<AP.tables.length→t≠0→TableLocal (ProcPriorComparatorRoutedFamily.tables[t]!) tr t pub

theorem physical_local {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (h:HoldsP AP pub tr) (t : Nat) (ht:t<AP.tables.length) : TableLocal (AP.tables[t]!) tr t pub := by
  rw [getElem!_pos AP.tables t ht]
  exact ⟨(h.logBound t ht).1,(h.logBound t ht).2,h.constr t ht,h.bits t ht⟩

theorem repaired {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (h:HoldsP AP pub tr) (ht:AP.tables=ProcPriorProcessRepairedFamily.tables) : View AP pub tr := by
  have hlen:AP.tables.length=ProcPriorComparatorRoutedFamily.tables.length := by rw [ht];rfl
  have hrest:∀t,t≠0→AP.tables[t]! =ProcPriorComparatorRoutedFamily.tables[t]! := by
    intro t hn
    cases t with
    | zero=>exact False.elim (hn rfl)
    | succ t=>rw [ht];rfl
  have hzero:AP.tables[0]! =ProcPriorProcessRepairedFamily.fused := by rw [ht];rfl
  have hz:0<AP.tables.length := by rw [ht];decide +kernel
  refine ⟨h,hlen,?_,?_,?_⟩
  · intro t
    cases t with
    | zero=>rw [hzero];exact ProcPriorProcessTransport.fused_interactions
    | succ t=>rw [hrest _ (by omega)]
  · intro i hi hn
    have hlocal:=physical_local h 0 hz
    rw [hzero] at hlocal
    exact ProcPriorProcessProjection.nonprocess_local tr 0 pub hlocal i
      (by rw [ProcPriorProcessRepairedFamily.length];exact hi) hn
  · intro t hi hn
    rw [←hrest t hn]
    exact physical_local h t hi

/-- Any concrete old bus ownership fact transfers through the interaction
contract, while matching still uses actual HoldsP and actual public segments. -/
theorem ownership {AP : AirP} {pub : List Fp} {tr : Trace Fp} (v:View AP pub tr)
    (Q : Nat→Interaction→Prop)
    (h:∀t,t<ProcPriorComparatorRoutedFamily.tables.length→
      ∀i∈(ProcPriorComparatorRoutedFamily.tables[t]!).interactions,Q t i) :
    ∀t,t<AP.tables.length→∀i∈(AP.tables[t]!).interactions,Q t i := by
  intro t ht i hi
  rw [v.wires] at hi
  exact h t (by rw [←v.length];exact ht) i hi
end ZkFormal.NearV3.Candidates.ProcessRepairInterface
