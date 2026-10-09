import ZkFormal.NearV3.Assembly.SchedulerRdbFieldSlice
import ZkFormal.NearV3.Assembly.CompactDigestSlice
import ZkFormal.NearV3.Assembly.CompactSelectedChildTargets
import ZkFormal.NearV3.Render.Ups.NativeChildLengths
import ZkFormal.NearV3.Assembly.SchedulerBranchWindows

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- An entire physical RDB part consumes exactly the preceding native SHA
job. Actual runtime child identity, header offset, and allocated clen are derived. -/
theorem nativeInstance_rdb_digest (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {a b : TreePart} (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hu : b.kind=.RDB)
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
  have hkind : (part I (k+1)).kind=0 := by
    change (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=0
    rw [hpart]
    change Q.kind=0
    rw [encodeTreePart_kind henc,hu]
    rfl
  have hj : (part I (k+1)).jm=k+1 := hp.jmD (Or.inl hkind)
  obtain ⟨c,hc,hlen⟩:=nativeInstance_nativeChildLength recordId baseI hr base he (k+1) hk
  change run.parts[(part I (k+1)).jm-1]?=some c at hc
  rw [hj,Nat.add_sub_cancel,ha] at hc
  cases hc
  change (part I (k+1)).clen=(nodeEnc a.output).length at hlen
  change ((List.range (part I (k+1)).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I (k+1))).map Msg.toFp=_
  have hn : 0<nWin (part I (k+1)).shape :=
    nativeInstance_branch_windows recordId baseI hr (nativeSourceBase recordId run base) he (k+1)
      (by rw [nativeInstance_nQ];exact hk) (Or.inl hkind)
  rw [CompactPhysicalDigests.selected_branch_inventory I (k+1) hf hp (Or.inl hkind) hn,
    List.map_cons,List.map_nil]
  simp only [hkind,show ¬(0=5) by decide,ite_false]
  congr 1
  rw [hlen]
  apply CompactPhysicalDigests.digest_window_slice
  · rw [hq,←List.map_drop,←List.map_take,hpart]
    unfold CompactPhysicalDigests.targetWindow
    change _ = _
    rw [hpart]
    change (((nodeEnc b.output).drop ((if Q.ty=2 then 3 else 39)+
      32*(if S15B I Q then nWin Q.shape-1 else 0))).take 32).map UInt8.toNat=_
    rw [traceUpsert_rdb_field_slice recordId hr hw ha hb hu
      ((nativeSourceBase recordId run base) (k+1)) henc I]
  · simp

end ZkFormal.NearV3.Assembly
