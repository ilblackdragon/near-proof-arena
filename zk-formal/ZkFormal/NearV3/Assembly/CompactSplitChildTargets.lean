import ZkFormal.NearV3.Assembly.CompactSplitValueTargets

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- LSc/ESn0 authenticate both moved and fresh children. The physical order
changes with the selected nibble and both occurrences are retained. -/
theorem split_two_child_targets (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k)) (hw : WindowOk I (part I k))
    (hk : (part I k).kind=10) (hc : I.ci=6∨I.ci=9) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      if I.ts=1 then
        [digestWindow I k 3 k 50,digestWindow I k 35 1 (part I k).clen]
      else [digestWindow I k 3 1 (part I k).clen,digestWindow I k 35 k 50] := by
  have ht : (part I k).ty=2 := by
    have hbr:=hp.tyBr (by omega)
    have hb:=hf.ty
    have hsp:=hp.tySpb hk
    omega
  have hn : nWin (part I k).shape=2 := by rw [hw.splitCount hk];split <;> omega
  have hj:=hp.jmS hk (by omega)
  rw [branch_digest_inventory I k hf ht,hn]
  by_cases hs:I.ts=1
  · rcases hc with hc|hc <;>
      simp [hk,hc,hs,hj,List.range_succ,child_field_target,WfrB,WnB,WyB,FwB,Spy1B,Spy2B,XcpB]
  · rcases hc with hc|hc <;>
      simp [hk,hc,hs,hj,List.range_succ,child_field_target,WfrB,WnB,WyB,FwB,Spy1B,Spy2B,XcpB]

/-- ESn1 copies the old child and authenticates only the newly allocated leaf. -/
theorem split_copied_child_target (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k)) (hw : WindowOk I (part I k))
    (hk : (part I k).kind=10) (hc : I.ci=10) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k (if I.ts=1 then 3 else 35) k 50] := by
  have ht : (part I k).ty=2 := by
    have hbr:=hp.tyBr (by omega)
    have hb:=hf.ty
    have hsp:=hp.tySpb hk
    omega
  have hn : nWin (part I k).shape=2 := by rw [hw.splitCount hk];simp [hc]
  rw [branch_digest_inventory I k hf ht,hn]
  by_cases hs:I.ts=1 <;>
    simp [hk,hc,hs,List.range_succ,child_field_target,WfrB,WnB,WyB,FwB,Spy1B,Spy2B,XcpB]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
