import ZkFormal.NearV3.Assembly.SchedulerSplitMovedSlices
import ZkFormal.NearV3.Assembly.CompactSplitValueTargets
import ZkFormal.NearV3.Assembly.CompactDigestSlice
import ZkFormal.NearV3.Render.Ups.NativeChildLengths

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Entire physical LSb/ESl0 part: exact fresh-value and moved-output native
SHA consumers, including the allocator's concrete child length. -/
theorem nativeInstance_split_moved_digests (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p) (hkind : p.kind=.SPB)
    (hc : run.terminal=.LSb ∨ run.terminal=.ESl0)
    (hq : (part (nativeInstance recordId baseI root run v Qs) k).q=(nodeEnc p.output).map UInt8.toNat)
    (hf : FieldsOk (part (nativeInstance recordId baseI root run v Qs) k))
    (hplan : PartOk (nativeInstance recordId baseI root run v Qs) k (part (nativeInstance recordId baseI root run v Qs) k))
    (hwin : WindowOk (nativeInstance recordId baseI root run v Qs) (part (nativeInstance recordId baseI root run v Qs) k)) :
    let I:=nativeInstance recordId baseI root run v Qs
    ∃a,run.parts[0]?=some a ∧
      ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=
      [digMsg (upsertJobId I.tau 0) v.length ((sha256 v).map UInt8.toNat),
        digMsg (upsertJobId I.tau 1) (nodeEnc a.output).length ((sha256 (nodeEnc a.output)).map UInt8.toNat)].map Msg.toFp := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hk:k<Qs.length:=by
    rw [encodeNativeParts_length recordId hr (nativeSourceBase recordId run base) he]
    exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨p',Q,hp',hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr (nativeSourceBase recordId run base) he k hk
  rw [hp] at hp';cases hp'
  have hfQ:FieldsOk Q:=by
    rw [hpart] at hf
    exact ⟨hf.ty,hf.prefixLength,hf.leaf,hf.extension,hf.shape,hf.bytes,hf.nochild⟩
  have hqQ:Q.q=(nodeEnc p.output).map UInt8.toNat:=by rw [hpart] at hq;exact hq
  obtain ⟨a,ha,h5,h39⟩:=traceUpsert_split_moved_slices hr hw (List.mem_of_getElem? hp) hkind hc henc hfQ hqQ
  have hpk:(part I k).kind=10:=by
    change (part (nativeInstance recordId baseI root run v Qs) k).kind=10
    rw [hpart];change Q.kind=10;rw [encodeTreePart_kind henc,hkind];rfl
  have hci:I.ci=5∨I.ci=7:=by
    change run.terminal.ix=5∨run.terminal.ix=7
    rcases hc with h|h <;> rw [h] <;> simp [UpsRows.UCase.ix]
  have hj:(part I k).jm=1:=hplan.jmS hpk (by rcases hci with h|h;exact Or.inl h;exact Or.inr (Or.inr (Or.inl h)))
  obtain ⟨a',ha',hlen⟩:=nativeInstance_nativeChildLength recordId baseI hr base he k hk
  change run.parts[(part I k).jm-1]?=some a' at ha'
  rw [hj,Nat.sub_self,ha] at ha';cases ha'
  change (part I k).clen=(nodeEnc a.output).length at hlen
  refine ⟨a,ha,?_⟩
  change ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=_
  rw [CompactPhysicalDigests.split_value_moved_targets I k hf hplan hwin hpk hci]
  have hL:L I=v.length:=by simp [I,nativeInstance,signedInstance,positionedInstance,traceInstance,L]
  rw [hL,hlen]
  simp only [List.map_cons,List.map_nil]
  congr 1
  · apply CompactPhysicalDigests.digest_window_slice
    · rw [hq,←List.map_drop,←List.map_take,h5]
    · simp
  · congr 1
    apply CompactPhysicalDigests.digest_window_slice
    · rw [hq,←List.map_drop,←List.map_take,h39]
    · simp

end ZkFormal.NearV3.Assembly
