import ZkFormal.NearV3.Assembly.SchedulerSignedSplitMoved
import ZkFormal.NearV3.Assembly.SchedulerSignedSplitPair
import ZkFormal.NearV3.Assembly.SchedulerSignedSplitNew
import ZkFormal.NearV3.Assembly.SchedulerSignedFreshOnly
import ZkFormal.NearV3.Assembly.SchedulerJobMessages
import ZkFormal.NearV3.Assembly.SchedulerDigestPlanFacts

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Near

/-- Split-window payloads are exactly the indexed native jobs, preserving both
children and their physical order before the final permutation. -/
theorem nativeInstance_split_messages (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p) (hk : p.kind=.SPB)
    (hi : InstOk (nativeInstance recordId baseI root run v Qs))
    (hparts : NativePartFamily (nativeInstance recordId baseI root run v Qs)) :
    let I:=nativeInstance recordId baseI root run v Qs
    (((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp).Perm
      ((partDigestUses run.terminal k p.kind).map (fun j=>(nativeJobMessage run v I.tau j).toFp)) := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hframe:=nativeInstance_digest_frame recordId baseI hr (nativeSourceBase recordId run base) he
  have hkb:k<nQ I:=by rw [hframe.2.2.1];exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨_,hf,hplan,hwin,_⟩:=hparts k hkb
  have hkind:(part I k).kind=10:=by rw [hframe.2.2.2 k p hp,hk];rfl
  have hci:4≤run.terminal.ix:=split_part_case_bound I k hi hplan hkind
  have hq:=nativeInstance_bytes_at recordId baseI hr hw (nativeSourceBase recordId run base) he hp
  change (((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp).Perm
    ((partDigestUses run.terminal k p.kind).map (fun j=>(nativeJobMessage run v I.tau j).toFp))
  cases hc:run.terminal with
  | LP | BR | BV | BI => simp [hc,UpsRows.UCase.ix] at hci
  | LSa | ESn1 =>
    obtain ⟨a,ha,hk1,hm⟩:=nativeInstance_split_new_digest recordId baseI hr hw
      (nativeSourceBase recordId run base) he hp hk (by simp [hc]) hparts
    rw [hm]
    simp only [hk,hc,partDigestUses,List.map_cons,List.map_nil,hk1]
    rw [nativeJobMessage_part v I.tau ha]
  | LSb | ESl0 =>
    obtain ⟨a,ha,hm⟩:=nativeInstance_split_moved_digests recordId baseI hr hw base he hp hk
      (by simp [hc]) hq hf hplan hwin
    rw [hm]
    simp only [hk,hc,partDigestUses,List.map_cons,List.map_nil,nativeJobMessage_zero]
    rw [nativeJobMessage_part v I.tau ha]
  | LSc | ESn0 =>
    obtain ⟨a,b,ha,hb,hk2,hm⟩:=nativeInstance_split_pair_digests recordId baseI hr hw base he hp hk
      (by simp [hc]) hparts
    rw [hm]
    simp only [hk,hc,partDigestUses,List.map_cons,List.map_nil,hk2]
    rw [nativeJobMessage_part v I.tau ha,nativeJobMessage_part v I.tau hb]
    split <;> simp only [List.map_cons,List.map_nil]
    · exact List.Perm.swap _ _ []
    · exact List.Perm.refl _
  | ESl1 =>
    have hm:=nativeInstance_fresh_only_digest recordId baseI hr hw (nativeSourceBase recordId run base) he hp
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨hk,hc⟩)))) hparts
    rw [hm]
    simp [hk,hc,partDigestUses,nativeJobMessage_zero,I]

end ZkFormal.NearV3.Assembly
