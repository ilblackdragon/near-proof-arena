import ZkFormal.NearV3.Qv.Candidates.CombinedWordAggregate

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen

def Walk.wordMessages (w : Walk) (bus : Nat) (sd : Bool) : List Msg :=
  if bus=ValueTable.B_QVC then w.counterWordMessages sd
  else if sd then if bus=B_KEYNIB then w.keyWordMessages else []
  else if bus=B_FINAL then w.finalWordMessages
  else if bus=B_QSH then w.shardWordMessages else []

theorem Walk.send_other_silent (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((w.row pos b).getD c 0))
    (bus : Nat) (hk : bus≠B_KEYNIB) (hq : bus≠ValueTable.B_QVC) :
    rowTraffic CombinedTable.interactions tr t r pub bus true=[] := by
  rw [w.parser_silent pos b tr t r pub hc]
  simp [rowTraffic,walkInteractions,CombinedTable.interactions,Dsl.send,Dsl.recv,Ne.symm hk,Ne.symm hq]

theorem Walk.recv_other_silent (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat ((w.row pos b).getD c 0))
    (bus : Nat) (hf : bus≠B_FINAL) (hq : bus≠ValueTable.B_QVC) (hs : bus≠B_QSH) :
    rowTraffic CombinedTable.interactions tr t r pub bus false=[] := by
  rw [w.parser_silent pos b tr t r pub hc]
  simp [rowTraffic,walkInteractions,CombinedTable.interactions,Dsl.send,Dsl.recv,Ne.symm hf,Ne.symm hq,Ne.symm hs]

theorem Walk.all_word_field (w : Walk) (tr : Trace Fp) (t start : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool)
    (hc : ∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
      tr.cell t (start+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0))
    (hs : w.kind.code=3 → 3≤w.slot) :
    w.kind.bytes.zipIdx.flatMap (fun bi =>
      rowTraffic CombinedTable.interactions tr t (start+bi.2) pub bus sd)=
      (w.wordMessages bus sd).map Msg.toFp := by
  by_cases hq : bus=ValueTable.B_QVC
  · subst bus
    simpa only [Walk.wordMessages,Walk.counterWordMessages,Walk.finalWordMessages,ite_true] using w.counter_word_field tr t start pub sd hc
  · cases sd
    · by_cases hf : bus=B_FINAL
      · subst bus
        simpa only [Walk.wordMessages,Walk.counterWordMessages,Walk.finalWordMessages,hq,ite_false,ite_true,Bool.false_eq_true] using w.final_word_field tr t start pub hc
      · by_cases hh : bus=B_QSH
        · subst bus
          simpa only [Walk.wordMessages,Walk.counterWordMessages,Walk.finalWordMessages,hq,hf,ite_false,ite_true,Bool.false_eq_true] using w.shard_word_field tr t start pub hc hs
        · simp only [Walk.wordMessages,Walk.counterWordMessages,Walk.finalWordMessages,hq,hf,hh,ite_false,Bool.false_eq_true,List.map_nil]
          apply List.flatMap_eq_nil_iff.mpr
          intro bi hbi
          exact w.recv_other_silent bi.2 bi.1 tr t _ pub (hc bi hbi) bus hf hq hh
    · by_cases hk : bus=B_KEYNIB
      · subst bus
        simpa only [Walk.wordMessages,Walk.counterWordMessages,Walk.finalWordMessages,hq,ite_false,ite_true] using w.key_word_field tr t start pub hc
      · simp only [Walk.wordMessages,Walk.counterWordMessages,Walk.finalWordMessages,hq,hk,ite_false,ite_true,List.map_nil]
        apply List.flatMap_eq_nil_iff.mpr
        intro bi hbi
        exact w.send_other_silent bi.2 bi.1 tr t _ pub (hc bi hbi) bus hk hq

def mixedTraffic (ws : List Walk) (vs : List Record) : Traffic where
  sends := fun bus => ws.flatMap (fun w => w.wordMessages bus true) ++ (canonicalTraffic vs).sends bus
  recvs := fun bus => ws.flatMap (fun w => w.wordMessages bus false) ++ (canonicalTraffic vs).recvs bus

theorem mixedTrace_all_messages (ws : List Walk) (vs : List Record)
    (hv : ∀ v ∈ vs,v.Valid) (hs : ∀ w ∈ ws,w.kind.code=3 → 3≤w.slot)
    (log : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (hfit : (ws.flatMap Walk.rows).length+recordsSize vs≤2^log) :
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub bus sd)).Perm
      ((if sd then (mixedTraffic ws vs).sends bus else (mixedTraffic ws vs).recvs bus).map Msg.toFp) := by
  have hp := mixedTrace_prefix_word_messages ws vs log pub bus sd (fun w => w.wordMessages bus sd)
    (fun w hw off hc => w.all_word_field _ 0 off pub bus sd hc (hs w hw))
  have h := mixedTrace_traffic_split ws vs hv log pub bus sd hfit
  rw [hp] at h
  cases sd <;> simpa only [mixedTraffic,ite_true,ite_false,Bool.false_eq_true,List.map_append] using h

theorem mixedTrace_table_traffic (ws : List Walk) (vs : List Record)
    (hv : ∀ v ∈ vs,v.Valid) (hs : ∀ w ∈ ws,w.kind.code=3 → 3≤w.slot)
    (log : Nat) (pub : List Fp)
    (hfit : (ws.flatMap Walk.rows).length+recordsSize vs≤2^log) :
    TableTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 pub (mixedTraffic ws vs) := by
  intro bus msg
  rw [tableBusCount_eq,tableBusCount_eq]
  exact ⟨(mixedTrace_all_messages ws vs hv hs log pub bus true hfit).count_eq msg,
    (mixedTrace_all_messages ws vs hv hs log pub bus false hfit).count_eq msg⟩

theorem plan_table_traffic (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie)
    (resolve : Resolve) (vs : List Record) (hv : ∀ v ∈ vs,v.Valid) (log : Nat) (pub : List Fp)
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length+recordsSize vs≤2^log) :
    TableTraffic CombinedTable.interactions (mixedTrace (plan pre v pres resolve) vs log) 0 pub
      (mixedTraffic (plan pre v pres resolve) vs) :=
  mixedTrace_table_traffic _ vs hv (plan_group_slot pre v pres resolve) log pub hfit

/-- Honest queue renderer with complete local and traffic interfaces. Balance
with other tables and extraction of arbitrary accepted traces remain separate. -/
theorem plan_local_and_traffic (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie)
    (resolve : Resolve) (hv : v.Valid) (d : Walk) (vs : List Record)
    (hvs : ∀ v ∈ vs,v.Valid) (log : Nat) (pub : List Fp)
    (hlog : 1≤log ∧ log≤CombinedTable.table.maxLog)
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length+recordsSize vs≤2^log)
    (hpub : ∀ r, CombinedTable.kPublic.eval (mixedTrace (F:=Fp) (plan pre v pres resolve) vs log) 0 r pub =
      @Nat.cast Fp Lean.Grind.Semiring.natCast pres.length) :
    TableLocal CombinedTable.table (mixedTrace (plan pre v pres resolve) vs log) 0 pub ∧
    TableTraffic CombinedTable.interactions (mixedTrace (plan pre v pres resolve) vs log) 0 pub
      (mixedTraffic (plan pre v pres resolve) vs) :=
  ⟨mixedTrace_table_local pre v pres resolve hv d vs hvs log pub hlog hfit hpub,
    plan_table_traffic pre v pres resolve vs hvs log pub hfit⟩

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
