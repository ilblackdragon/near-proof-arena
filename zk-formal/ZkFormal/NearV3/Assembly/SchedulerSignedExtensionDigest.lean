import ZkFormal.NearV3.Assembly.SchedulerExtensionFieldSlice
import ZkFormal.NearV3.Assembly.CompactDigestSlice
import ZkFormal.NearV3.Assembly.CompactUnaryDigestTargets
import ZkFormal.NearV3.Render.Ups.NativeChildLengths

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- An entire physical RDE/WEX/PT part consumes exactly the preceding native SHA
job. Actual runtime child identity, header offset, and allocated clen are derived. -/
theorem nativeInstance_extension_digest (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {a b : TreePart} (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b)
    (hu : b.kind=.RDE ∨ b.kind=.WEX ∨ b.kind=.PT)
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
  have hkind : (part I (k+1)).kind=1 ∨ (part I (k+1)).kind=9 ∨ (part I (k+1)).kind=11 := by
    change (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=1 ∨ _
    rw [hpart]
    change Q.kind=1 ∨ Q.kind=9 ∨ Q.kind=11
    rw [encodeTreePart_kind henc]
    rcases hu with h|h|h <;> rw [h] <;> simp [UpsRows.UKind.ix]
  have hj : (part I (k+1)).jm=k+1 := hp.jmD (by rcases hkind with h|h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h)))
  obtain ⟨c,hc,hlen⟩:=nativeInstance_nativeChildLength recordId baseI hr base he (k+1) hk
  change run.parts[(part I (k+1)).jm-1]?=some c at hc
  rw [hj,Nat.add_sub_cancel,ha] at hc
  cases hc
  change (part I (k+1)).clen=(nodeEnc a.output).length at hlen
  change ((List.range (part I (k+1)).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I (k+1))).map Msg.toFp=_
  rw [CompactPhysicalDigests.extension_child_target I (k+1) hf hp (by omega),List.map_cons,List.map_nil]
  congr 1
  rw [hlen]
  apply CompactPhysicalDigests.digest_window_slice
  · rw [hq,←List.map_drop,←List.map_take,hpart]
    change (((nodeEnc b.output).drop (5+Q.qhk)).take 32).map UInt8.toNat=_
    rw [traceUpsert_extension_field_slice hr ha hb hu henc]
  · simp

end ZkFormal.NearV3.Assembly
