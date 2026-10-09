import ZkFormal.NearV3.Assembly.SchedulerSplitNewSlice
import ZkFormal.NearV3.Assembly.SchedulerSplitChildLength
import ZkFormal.NearV3.Assembly.SchedulerNativeBytesAt
import ZkFormal.NearV3.Assembly.CompactSplitChildTargets
import ZkFormal.NearV3.Assembly.CompactSplitValueTargets
import ZkFormal.NearV3.Assembly.CompactDigestSlice

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Entire LSa/ESn1 physical part consumes precisely native output job1.
The copied ESn1 child has no extra SHA lookup. -/
theorem nativeInstance_split_new_digest (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p) (hkind : p.kind=.SPB)
    (hc : run.terminal=.LSa ∨ run.terminal=.ESn1)
    (hparts : NativePartFamily (nativeInstance recordId baseI root run v Qs)) :
    let I:=nativeInstance recordId baseI root run v Qs
    ∃a,run.parts[0]?=some a ∧ k=1 ∧
      ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=
      [(digMsg (upsertJobId I.tau 1) (nodeEnc a.output).length ((sha256 (nodeEnc a.output)).map UInt8.toNat)).toFp] := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hk:k<Qs.length:=by rw [encodeNativeParts_length recordId hr base he];exact (List.getElem?_eq_some_iff.mp hp).1
  have hkI:k<nQ I:=by rw [nativeInstance_nQ];exact hk
  obtain ⟨_,hf,hplan,hwin,_⟩:=hparts k hkI
  obtain ⟨p',Q,hp',_,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  rw [hp] at hp';cases hp'
  have hpk:(part I k).kind=10:=by rw [hpart];change Q.kind=10;rw [encodeTreePart_kind henc,hkind];rfl
  have hci:I.ci=4∨I.ci=10:=by
    change run.terminal.ix=4∨run.terminal.ix=10
    rcases hc with h|h <;> rw [h] <;> simp [UpsRows.UCase.ix]
  obtain ⟨_,hfp,hpp,_⟩:=hparts (k-1) (show k-1<nQ I by omega)
  have hlenparts:=spb_previous_length (I:=I) (by omega) hpk hplan hfp hpp
  have hk1:k=1:=hlenparts.2.2.1 hci
  have hfQ:FieldsOk Q:=by rw [hpart] at hf;exact ⟨hf.ty,hf.prefixLength,hf.leaf,hf.extension,hf.shape,hf.bytes,hf.nochild⟩
  have hq:=nativeInstance_bytes_at recordId baseI hr hw base he hp
  have hqQ:Q.q=(nodeEnc p.output).map UInt8.toNat:=by rw [hpart] at hq;exact hq
  obtain ⟨a,ha,hslice⟩:=traceUpsert_split_new_slice hr hw (List.mem_of_getElem? hp) hkind hc henc hfQ hqQ
  have hqa:=nativeInstance_bytes_at recordId baseI hr hw base he ha
  have halen:(nodeEnc a.output).length=50:=by
    have hh:=hlenparts.2.1
    rw [hk1] at hh
    change (part I 0).q.length=50 at hh
    rw [hqa,List.length_map] at hh
    exact hh
  have hmsgs: (List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)=
      [CompactPhysicalDigests.digestWindow I k (if run.terminal=.LSa then 39 else if I.ts=1 then 3 else 35) k 50] := by
    rcases hc with h|h
    · have hi:I.ci=4:=by change run.terminal.ix=4;rw [h];rfl
      simpa only [h,ite_true] using CompactPhysicalDigests.split_lsa_targets I k hf hplan hwin hpk hi
    · have hi:I.ci=10:=by change run.terminal.ix=10;rw [h];rfl
      simpa only [h,show ¬(UpsRows.UCase.ESn1=UpsRows.UCase.LSa) by decide,ite_false] using
        CompactPhysicalDigests.split_copied_child_target I k hf hplan hwin hpk hi
  refine ⟨a,ha,hk1,?_⟩
  change ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=_
  rw [hmsgs,List.map_cons,List.map_nil,←halen]
  congr 1
  rw [hk1] at hq ⊢
  apply CompactPhysicalDigests.digest_window_slice
  · rw [hq,←List.map_drop,←List.map_take]
    exact congrArg (List.map UInt8.toNat) hslice
  · simp

end ZkFormal.NearV3.Assembly
