import ZkFormal.NearV3.Assembly.SchedulerRbiFieldSlice
import ZkFormal.NearV3.Assembly.CompactDigestSlice
import ZkFormal.NearV3.Assembly.CompactSelectedChildTargets
import ZkFormal.NearV3.Render.Ups.NativeChildLengths
import ZkFormal.NearV3.Assembly.SchedulerBranchWindows
import ZkFormal.NearV3.Assembly.SchedulerRbiChildLength

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- An entire physical RBI part consumes exactly the preceding native SHA
job. Actual runtime child identity, header offset, and allocated clen are derived. -/
theorem nativeInstance_rbi_digest (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {a b : TreePart} (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hu : b.kind=.RBI)
    (hqa : (part (nativeInstance recordId baseI root run v Qs) k).q=(nodeEnc a.output).map UInt8.toNat)
    (hf0 : FieldsOk (part (nativeInstance recordId baseI root run v Qs) 0))
    (hp0 : PartOk (nativeInstance recordId baseI root run v Qs) 0 (part (nativeInstance recordId baseI root run v Qs) 0))
    (hq : (part (nativeInstance recordId baseI root run v Qs) (k+1)).q=
      (nodeEnc b.output).map UInt8.toNat)
    (hf : FieldsOk (part (nativeInstance recordId baseI root run v Qs) (k+1)))
    (hp : PartOk (nativeInstance recordId baseI root run v Qs) (k+1)
      (part (nativeInstance recordId baseI root run v Qs) (k+1))) :
    let I:=nativeInstance recordId baseI root run v Qs
    ((List.range (part I (k+1)).q.length).flatMap
      (CompactPhysicalDigests.nodeDigestMsgs I (k+1))).map Msg.toFp=
      [(digMsg (upsertJobId I.tau (k+1)) (nodeEnc a.output).length
        ((sha256 (nodeEnc a.output)).map UInt8.toNat)).toFp] := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hk : k+1<Qs.length := by
    rw [encodeNativeParts_length recordId hr (nativeSourceBase recordId run base) he]
    exact (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨b',Q,hb',hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr
    (nativeSourceBase recordId run base) he (k+1) hk
  rw [hb] at hb'
  cases hb'
  have hkind : (part I (k+1)).kind=5 := by
    change (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=5
    rw [hpart]
    change Q.kind=5
    rw [encodeTreePart_kind henc,hu]
    rfl
  have hcase:I.ci=3 := by
    have hh:=(traceUpsert_rbi_info root [0,15] v run hr b (List.mem_of_getElem? hb) hu).2.1
    change run.terminal.ix=3
    rw [hh]
    rfl
  have hlenQ:=(rbi_previous_length hcase hkind hp hf0 hp0).2
  have hlen : (nodeEnc a.output).length=50 := by
    rw [hqa,List.length_map] at hlenQ
    exact hlenQ
  change ((List.range (part I (k+1)).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I (k+1))).map Msg.toFp=_
  have hn : 0<nWin (part I (k+1)).shape :=
    nativeInstance_branch_windows recordId baseI hr (nativeSourceBase recordId run base) he (k+1)
      (by rw [nativeInstance_nQ];exact hk) (Or.inr hkind)
  rw [CompactPhysicalDigests.selected_branch_inventory I (k+1) hf hp (Or.inr hkind) hn,
    List.map_cons,List.map_nil]
  simp only [hkind,ite_true]
  congr 1
  rw [←hlen]
  apply CompactPhysicalDigests.digest_window_slice
  · rw [hq,←List.map_drop,←List.map_take,hpart]
    unfold CompactPhysicalDigests.targetWindow
    change _ = _
    rw [hpart]
    change (((nodeEnc b.output).drop ((if Q.ty=2 then 3 else 39)+
      32*(if S15B I Q then nWin Q.shape-1 else 0))).take 32).map UInt8.toNat=_
    rw [traceUpsert_rbi_field_slice hr hw ha hb hu henc I rfl]
  · simp

end ZkFormal.NearV3.Assembly
