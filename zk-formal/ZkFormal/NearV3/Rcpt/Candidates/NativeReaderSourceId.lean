import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderPayload

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Source identity and copied bytes refer to the same indexed native part,
not to independently chosen equal-byte occurrences. -/
theorem native_reader_source_id (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] value=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k<Qs.length) :
    ∃p,run.parts[k]?=some p ∧ p.source∈occs root ∧
      (part (nativeInstance recordId baseI root run value Qs) k).sN=recordId p.source ∧
      (part (nativeInstance recordId baseI root run value Qs) k).pb=(nodeEnc p.source).map UInt8.toNat := by
  obtain ⟨p,hp,hm,hb,_⟩:=native_reader_payload recordId baseI hr hw base he k hk
  obtain ⟨p',Q,hp',hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  have hpp : p'=p := Option.some.inj (hp'.symm.trans hp)
  subst p'
  refine ⟨p,hp,hm,?_,hb⟩
  rw [hpart]
  change Q.sN=recordId p.source
  exact (encodeTreePart_positions henc).2.2.2.1

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
