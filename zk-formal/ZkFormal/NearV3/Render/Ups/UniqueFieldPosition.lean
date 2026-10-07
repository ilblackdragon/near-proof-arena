import ZkFormal.NearV3.Render.Ups.PrefixPosition

namespace ZkFormal.NearV3.Render.UpsGen

/-- A uniquely tagged field determines the byte cursor from its serialized prefix. -/
theorem unique_field_position (pre post : List (Nat × Nat)) (st len p : Nat)
    (hs9 : 9≠st) (hpre : ∀ f ∈ pre, f.1≠st) (hpost : ∀ f ∈ post, f.1≠st)
    (hs : (fieldAt (pre++(st,len)::post) p).1=st) :
    p=fieldsLen pre + (fieldAt (pre++(st,len)::post) p).2.1 := by
  by_cases hp : p<fieldsLen pre
  · rw [fieldAt_append_before pre ((st,len)::post) p hp] at hs
    exact False.elim (fieldAt_avoid st hs9 pre hpre p hs)
  · have hn : fieldsLen pre ≤ p := by omega
    have he := fieldAt_append_after pre ((st,len)::post) p hn
    rw [he] at hs ⊢
    by_cases hl : p-fieldsLen pre<len
    · simp [fieldAt,hl]; omega
    · have hz := fieldAt_avoid st hs9 post hpost (p-fieldsLen pre-len)
      simp only [fieldAt,hl,ite_false] at hs
      exact False.elim (hz hs)

end ZkFormal.NearV3.Render.UpsGen
