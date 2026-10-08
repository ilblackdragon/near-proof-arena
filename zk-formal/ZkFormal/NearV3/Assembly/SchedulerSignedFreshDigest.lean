import ZkFormal.NearV3.Assembly.SchedulerFreshPhysicalDigest
import ZkFormal.NearV3.Render.Ups.NativeEncodingFacts

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Fresh payload binding on the actual signed instance. The encoder supplies
its metadata; the same native SHA byte-family supplies the serialization. -/
theorem nativeInstance_fresh_digest (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p)
    (hf : freshDigestKind run.terminal p.kind=true)
    (hq : (part (nativeInstance recordId baseI root run v Qs) k).q=
      (nodeEnc p.output).map UInt8.toNat) :
    let I:=nativeInstance recordId baseI root run v Qs
    (CompactPhysicalDigests.digestWindow I k
      (if (part I k).ty=0 then 9+(part I k).qhk else 5) 0 v.length).toFp=
      (digMsg (upsertJobId I.tau 0) v.length ((sha256 v).map UInt8.toNat)).toFp := by
  have hk : k<Qs.length := by
    rw [encodeNativeParts_length recordId hr base he]
    exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨p',Q,hp',hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  rw [hp] at hp'
  cases hp'
  apply CompactPhysicalDigests.digest_window_slice
  · rw [hq,←List.map_drop,←List.map_take,hpart]
    change (((nodeEnc p.output).drop (if Q.ty=0 then 9+Q.qhk else 5)).take 32).map UInt8.toNat=_
    rw [traceUpsert_fresh_field_slice hr (List.mem_of_getElem? hp) hf henc]
  · simp

end ZkFormal.NearV3.Assembly
