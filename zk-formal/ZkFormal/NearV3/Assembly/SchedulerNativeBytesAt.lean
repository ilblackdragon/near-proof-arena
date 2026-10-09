import ZkFormal.NearV3.Assembly.UpsertShaEncoding

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen

/-- Index-preserving exact native serialization for the actual signed instance,
including rebuilt ancestors and branch slots. Source wf is sufficient. -/
theorem nativeInstance_bytes_at (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p) :
    (part (nativeInstance recordId baseI root run v Qs) k).q=(nodeEnc p.output).map UInt8.toNat := by
  have hk:k<Qs.length:=by rw [encodeNativeParts_length recordId hr base he];exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨p',Q,hp',_,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  rw [hp] at hp';cases hp'
  rw [hpart]
  change Q.q=_
  exact encodeTreePart_nat_output henc (traceUpsert_branchWidth root [0,15] v run hr hw p (List.mem_of_getElem? hp))

end ZkFormal.NearV3.Assembly
