import ZkFormal.NearV3.Assembly.SchedulerSignedExtensionDigest
import ZkFormal.NearV3.Assembly.SchedulerSignedRdbDigest
import ZkFormal.NearV3.Assembly.SchedulerSignedRbiDigest
import ZkFormal.NearV3.Assembly.SchedulerNativeBytesAt
import ZkFormal.NearV3.Assembly.SchedulerJobMessages
import ZkFormal.NearV3.Assembly.SchedulerDigestPlanFacts

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Near

/-- Every non-split parent demand equals the same indexed native job, including
insertions, wrapping extensions and all rebuilt trie ancestors. -/
theorem nativeInstance_parent_messages (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p)
    (hk : p.kind=.RDB∨p.kind=.RDE∨p.kind=.RBI∨p.kind=.WEX∨p.kind=.PT)
    (hi : InstOk (nativeInstance recordId baseI root run v Qs))
    (hparts : NativePartFamily (nativeInstance recordId baseI root run v Qs)) :
    let I:=nativeInstance recordId baseI root run v Qs
    ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=
      [(nativeJobMessage run v I.tau k).toFp] := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hf:=nativeInstance_digest_frame recordId baseI hr (nativeSourceBase recordId run base) he
  have hkb:k<nQ I:=by rw [hf.2.2.1];exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨_,hfields,hplan,hwin,_⟩:=hparts k hkb
  have hkind:(part I k).kind=p.kind.ix:=hf.2.2.2 k p hp
  have hpos:0<k:=parent_part_positive I k hi hplan (by
    rw [hkind];rcases hk with h|h|h|h|h <;> simp [h,UpsRows.UKind.ix])
  cases k with
  | zero=>omega
  | succ k=>
    have hkp:k<run.parts.length:=Nat.lt_trans (Nat.lt_succ_self k) (List.getElem?_eq_some_iff.mp hp).1
    let a:=run.parts[k]'hkp
    have ha:run.parts[k]?=some a:=List.getElem?_eq_getElem hkp
    have hq:=nativeInstance_bytes_at recordId baseI hr hw (nativeSourceBase recordId run base) he hp
    change ((List.range (part I (k+1)).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I (k+1))).map Msg.toFp=_
    rw [nativeJobMessage_part v I.tau ha]
    rcases hk with hk|hk|hk|hk|hk
    · exact nativeInstance_rdb_digest recordId baseI hr hw base he ha hp hk hq hfields hplan
    · exact nativeInstance_extension_digest recordId baseI hr base he ha hp (Or.inl hk) hq hfields hplan
    · obtain ⟨_,hf0,hp0,_⟩:=hparts 0 hi.nQ1
      exact nativeInstance_rbi_digest recordId baseI hr hw base he ha hp hk
        (nativeInstance_bytes_at recordId baseI hr hw (nativeSourceBase recordId run base) he ha)
        hf0 hp0 hq hfields hplan
    · exact nativeInstance_extension_digest recordId baseI hr base he ha hp (Or.inr (Or.inl hk)) hq hfields hplan
    · exact nativeInstance_extension_digest recordId baseI hr base he ha hp (Or.inr (Or.inr hk)) hq hfields hplan

end ZkFormal.NearV3.Assembly
