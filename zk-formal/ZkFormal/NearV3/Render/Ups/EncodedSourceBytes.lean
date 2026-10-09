import ZkFormal.NearV3.Render.Ups.TreeEncodedBounds
import ZkFormal.NearV3.Render.Ups.TreePartBytesBounds

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

/-- Encoding real source nodes supplies byte bounds for the entire surrounding part table. -/
theorem encodeTreeParts_sourceBytes (base : Nat→UpsPartI) :
    ∀ (parts : List TreePart) (offset : Nat) (Qs : List UpsPartI),
    encodeTreeParts base offset parts=some Qs →
    (∀ part∈parts,part.source.wf=true) → ∀ Q∈Qs,SourceBytes Q
  | [], _, Qs, he, _ => by simp [encodeTreeParts] at he; subst Qs; simp
  | part::parts, offset, Qs, he, hw => by
    cases hQ : encodeTreePart (base offset) part with
    | none => simp [encodeTreeParts,hQ] at he
    | some Q =>
      cases hQs : encodeTreeParts base (offset+1) parts with
      | none => simp [encodeTreeParts,hQ,hQs] at he
      | some tail =>
        simp [encodeTreeParts,hQ,hQs] at he
        subst Qs
        intro P hP
        simp only [List.mem_cons] at hP
        rcases hP with rfl|hP
        · exact encoded_source_byte_bounds hQ (hw part (by simp))
        · exact encodeTreeParts_sourceBytes base parts (offset+1) tail hQs
            (fun p hp => hw p (by simp [hp])) P hP

theorem table_child_sourceBytes (I : UpsInst) (Q : UpsPartI)
    (hw : ∀ P∈I.parts,SourceBytes P) : SourceBytes (child I Q) := by
  unfold child part
  cases he : I.parts[Q.jm-1]? with
  | none =>
    simp only [List.getD_eq_getElem?_getD,he,Option.getD_none]
    change ∀ b∈([] : List Nat),b<256
    simp
  | some P =>
    simp only [List.getD_eq_getElem?_getD,he,Option.getD_some]
    exact hw P (List.mem_of_getElem? he)

/-- No child-byte hypothesis is needed once the actual native part table is encoded. -/
theorem trace_encoded_child_sourceBytes {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) (hw : t.wf=true) (base : Nat→UpsPartI)
    {Qs : List UpsPartI} (he : encodeTreeParts base 0 run.parts=some Qs)
    (I : UpsInst) (hi : I.parts=Qs) (Q : UpsPartI) : SourceBytes (child I Q) := by
  apply table_child_sourceBytes I Q
  rw [hi]
  exact encodeTreeParts_sourceBytes base run.parts 0 Qs he (traceUpsert_sources t key v run hw hr).2
end ZkFormal.NearV3.Render.UpsGen
