import ZkFormal.NearV3.Render.Ups.CopyFields
import ZkFormal.NearV3.Render.Ups.ValueFieldPosition

namespace ZkFormal.NearV3.Render.UpsGen

/-- A field absent from the suffix is wholly contained in the headBytes. -/
theorem field_headBytes_bound (front back pre post : List (Nat × Nat)) (field : Nat × Nat)
    (he : front++back=pre++field::post) (hn : field ∉ back) :
    fieldsLen pre+field.2≤fieldsLen front := by
  induction front generalizing pre with
  | nil =>
    have hm : field ∈ back := by rw [List.nil_append] at he; rw [he]; simp
    exact False.elim (hn hm)
  | cons f front ih =>
    cases pre with
    | nil =>
      have hh : f=field := (List.cons.inj he).1
      subst field
      simp [fieldsLen] <;> omega
    | cons g pre =>
      obtain ⟨hfg,ht⟩ := List.cons.inj he
      subst g
      have hb := ih pre ht
      simp only [fieldsLen,List.map_cons,List.sum_cons] at hb ⊢
      omega

theorem slice_common_headBytes (headBytes left right : List Nat) (start width : Nat)
    (h : start+width≤headBytes.length) :
    ((headBytes++left).drop start).take width=((headBytes++right).drop start).take width := by
  rw [List.drop_append_of_le_length (by omega),List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp; omega),List.take_append_of_le_length (by simp; omega)]

end ZkFormal.NearV3.Render.UpsGen
