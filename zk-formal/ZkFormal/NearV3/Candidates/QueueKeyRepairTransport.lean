import ZkFormal.NearV3.Candidates.QueueKeyRepair

namespace ZkFormal.NearV3.Candidates.QueueKeyRepair
open ZkFormal.Near Qv Qv.Candidates ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

theorem nonkey_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bus : Nat)
    (hb : bus≠B_KEYNIB) (sd : Bool) :
    rowTraffic interactions tr t r pub bus sd=
      rowTraffic CombinedTable.interactions tr t r pub bus sd := by
  simp [interactions,CombinedTable.interactions,rowTraffic,send,recv,hb,Ne.symm hb]

theorem nonkey_count (tr : Trace Fp) (t : Nat) (pub : List Fp) (bus : Nat)
    (hb : bus≠B_KEYNIB) (sd : Bool) (msg : List Fp) :
    tableBusCount interactions tr t pub bus sd msg=
      tableBusCount CombinedTable.interactions tr t pub bus sd msg := by
  rw [ZkFormal.Near.tableBusCount_eq,ZkFormal.Near.tableBusCount_eq]
  simp only [nonkey_row tr t _ pub bus hb sd]

theorem mult_covered : ∀i∈interactions,∃j∈CombinedTable.interactions,i.mult=j.mult := by
  simp [interactions,CombinedTable.interactions,send,recv]

theorem local_transport (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal CombinedTable.table tr t pub) : TableLocal table tr t pub := by
  refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
  intro r hr i hi b hb
  obtain ⟨j,hj,he⟩:=mult_covered i hi
  exact h.bits r hr j hj b (he ▸ hb)

end ZkFormal.NearV3.Candidates.QueueKeyRepair
