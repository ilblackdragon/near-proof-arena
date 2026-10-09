import ZkFormal.NearV3.Assembly.CompactSelectedChildTargets

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- LSa keeps the old branch value and consumes its newly inserted leaf job. -/
theorem split_lsa_targets (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k)) (hw : WindowOk I (part I k))
    (hk : (part I k).kind=10) (hc : I.ci=4) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k 39 k 50] := by
  have ht : (part I k).ty=3 := (hp.tySpb hk).mpr (by simp [hc])
  have hn:=hw.splitCount hk
  simp only [hc,show ¬((4:Nat)=6∨4=9∨4=10) by decide,ite_false] at hn
  rw [value_branch_digest_inventory I k hf ht,value_field_target,hn]
  simp [VcpB,hk,hc,List.range_succ,child_field_target,WfrB,WnB,WyB,FwB,Spy1B,Spy2B,XcpB]

/-- LSb/ESl0 write the fresh value and authenticate the moved child, each once. -/
theorem split_value_moved_targets (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k)) (hw : WindowOk I (part I k))
    (hk : (part I k).kind=10) (hc : I.ci=5∨I.ci=7) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k 5 0 (L I),digestWindow I k 39 1 (part I k).clen] := by
  have ht : (part I k).ty=3 := (hp.tySpb hk).mpr (by omega)
  have hn : nWin (part I k).shape=1 := by rw [hw.splitCount hk];split <;> omega
  have hj:=hp.jmS hk (by omega)
  rw [value_branch_digest_inventory I k hf ht,value_field_target,hn]
  rcases hc with hc|hc <;>
    simp [VcpB,hk,hc,hj,List.range_succ,child_field_target,WfrB,WnB,WyB,FwB,Spy1B,Spy2B,XcpB]

/-- ESl1 writes the value while copying its already existing child digest. -/
theorem split_value_copied_targets (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k)) (hw : WindowOk I (part I k))
    (hk : (part I k).kind=10) (hc : I.ci=8) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k 5 0 (L I)] := by
  have ht : (part I k).ty=3 := (hp.tySpb hk).mpr (by simp [hc])
  have hn : nWin (part I k).shape=1 := by rw [hw.splitCount hk];simp [hc]
  rw [value_branch_digest_inventory I k hf ht,value_field_target,hn]
  simp [VcpB,hk,hc,List.range_succ,child_field_target,WfrB,WnB,WyB,FwB,Spy1B,Spy2B,XcpB]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
