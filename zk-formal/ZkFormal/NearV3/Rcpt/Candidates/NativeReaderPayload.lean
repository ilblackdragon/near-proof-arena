import ZkFormal.NearV3.Render.Ups.NativePrefixBounds
import ZkFormal.NearV3.Render.Ups.NativeSourceOccurrences

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- A constructed UPS reader copies the exact serialization of an actual
revealed occurrence in its input tree. This retains the native part index,
including repeated source occurrences introduced by split plans. -/
theorem native_reader_payload (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] value=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k<Qs.length) :
    ∃p,run.parts[k]?=some p ∧ p.source∈occs root ∧
      (part (nativeInstance recordId baseI root run value Qs) k).pb=(nodeEnc p.source).map UInt8.toNat ∧
      ((part (nativeInstance recordId baseI root run value Qs) k).q).map UInt8.ofNat=nodeEnc p.output := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  refine ⟨p,hp,traceUpsert_source_occurrence hr (List.mem_of_getElem? hp),?_,?_⟩ <;> rw [hpart]
  · change Q.pb=_
    have hs := (traceUpsert_sources root [0,15] value run hw hr).2 p (List.mem_of_getElem? hp)
    unfold encodeTreePart at henc
    cases hsrc : treeNode p.source <;> cases hdst : treeNode p.output <;> simp [hsrc,hdst] at henc
    subst Q
    exact treeNode_ser hs hsrc true
  · exact (encodeTreePart_native_bytes henc).2

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
