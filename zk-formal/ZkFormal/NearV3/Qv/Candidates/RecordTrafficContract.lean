import ZkFormal.NearV3.Qv.Candidates.RecordShardTraffic

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

def canonicalTraffic (vs : List Record) : Traffic where
  sends := fun bus =>
    if bus=B_VBYTES then vs.flatMap (fun v => numberedBytes v.vid 0 v.bytes)
    else if bus=ValueTable.B_QVC then vs.map (fun v => [v.vid,v.tau,v.mode,0])
    else if bus=B_QSH then vs.flatMap Record.shardBytes++vs.flatMap Record.shardCount
    else []
  recvs := fun bus =>
    if bus=ValueTable.B_QVC then vs.map (fun v => [v.vid,v.tau,v.mode,v.users]) else []

theorem natRowTraffic_silent (row : List Nat) (bus : Nat) (sd : Bool)
    (hb : bus≠B_VBYTES) (hq : bus≠ValueTable.B_QVC) (hs : bus≠B_QSH) :
    natRowTraffic ValueTable.interactions row bus sd=[] := by
  simp [natRowTraffic,ValueTable.interactions,send,recv,Ne.symm hb,Ne.symm hq,Ne.symm hs]

theorem natRowTraffic_recv_other (row : List Nat) (bus : Nat) (hq : bus≠ValueTable.B_QVC) :
    natRowTraffic ValueTable.interactions row bus false=[] := by
  simp [natRowTraffic,ValueTable.interactions,send,recv,Ne.symm hq]

theorem recordsTraffic_canonical (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) (bus : Nat) :
    ((recordsTraffic vs).sends bus).Perm ((canonicalTraffic vs).sends bus) ∧
    ((recordsTraffic vs).recvs bus).Perm ((canonicalTraffic vs).recvs bus) := by
  constructor
  · by_cases hb : bus=B_VBYTES
    · subst bus
      simp only [canonicalTraffic,ite_true,recordsTraffic_bytes vs hv]
      exact List.Perm.refl _
    · by_cases hq : bus=ValueTable.B_QVC
      · subst bus
        simp only [canonicalTraffic,hb,ite_false,ite_true,(recordsTraffic_providers vs hv).1]
        exact List.Perm.refl _
      · by_cases hs : bus=B_QSH
        · subst bus
          simpa only [canonicalTraffic,hb,hq,ite_false,ite_true] using recordsTraffic_shards vs hv
        · simp [recordsTraffic,canonicalTraffic,hb,hq,hs,natRowTraffic_silent _ _ _ hb hq hs]
  · by_cases hq : bus=ValueTable.B_QVC
    · subst bus
      simp only [canonicalTraffic,ite_true,(recordsTraffic_providers vs hv).2]
      exact List.Perm.refl _
    · simp [recordsTraffic,canonicalTraffic,hq,natRowTraffic_recv_other _ _ hq]

/-- Complete field-valued parser traffic in canonical payload terms: byte records,
provider endpoints, buffered shard bytes, and buffered entry counts. -/
theorem records_canonical_traffic (vs : List Record) (hv : ∀ v ∈ vs, v.Valid)
    (log : Nat) (pub : List Fp) (hb : recordsSize vs≤2^log) :
    TableTraffic ValueTable.interactions (recordsTrace vs log) 0 pub (canonicalTraffic vs) := by
  have h := records_field_traffic vs log pub (by rw [recordsRows_length vs hv]; exact hb)
  intro bus msg
  have ht := h bus msg
  have hp := recordsTraffic_canonical vs hv bus
  exact ⟨ht.1.trans ((hp.1.map Msg.toFp).count_eq msg),
    ht.2.trans ((hp.2.map Msg.toFp).count_eq msg)⟩

end ZkFormal.NearV3.Qv.Candidates.ValueGen
