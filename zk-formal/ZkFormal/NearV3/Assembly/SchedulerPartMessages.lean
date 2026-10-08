import ZkFormal.NearV3.Assembly.SchedulerParentMessages
import ZkFormal.NearV3.Assembly.SchedulerSplitMessages
import ZkFormal.NearV3.Assembly.CompactUnaryDigestTargets

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Near

/-- Complete physical payload conservation for every actual upsert part.
No digest identity or demand multiplicity is supplied as a premise. -/
theorem nativeInstance_part_messages (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p)
    (hi : InstOk (nativeInstance recordId baseI root run v Qs))
    (hparts : NativePartFamily (nativeInstance recordId baseI root run v Qs)) :
    let I:=nativeInstance recordId baseI root run v Qs
    (((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp).Perm
      ((partDigestUses run.terminal k p.kind).map (fun j=>(nativeJobMessage run v I.tau j).toFp)) := by
  let I:=nativeInstance recordId baseI root run v Qs
  change (((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp).Perm _
  have hframe:=nativeInstance_digest_frame recordId baseI hr (nativeSourceBase recordId run base) he
  have hkb:k<nQ I:=by rw [hframe.2.2.1];exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨_,hf,hplan,_,_⟩:=hparts k hkb
  have hkind:=hframe.2.2.2 k p hp
  cases hk:p.kind with
  | RDB | RDE | RBI | WEX | PT =>
    have hm:=nativeInstance_parent_messages recordId baseI hr hw base he hp (by simp [hk]) hi hparts
    rw [hm]
    simp only [hk,partDigestUses,List.map_cons,List.map_nil]
    exact List.Perm.refl _
  | RLP | RBR | RBV | NLF =>
    have hm:=nativeInstance_fresh_only_digest recordId baseI hr hw (nativeSourceBase recordId run base) he hp
      (by simp [hk]) hparts
    rw [hm]
    simp [hk,partDigestUses,nativeJobMessage_zero,I]
  | MVL =>
    rw [CompactPhysicalDigests.moved_leaf_no_digest I k hf hplan (by rw [hkind,hk];rfl)]
    simp [hk,partDigestUses]
  | MVE =>
    rw [CompactPhysicalDigests.moved_extension_no_digest I k hf hplan (by rw [hkind,hk];rfl)]
    simp [hk,partDigestUses]
  | SPB =>simpa only [hk] using nativeInstance_split_messages recordId baseI hr hw base he hp hk hi hparts

end ZkFormal.NearV3.Assembly
