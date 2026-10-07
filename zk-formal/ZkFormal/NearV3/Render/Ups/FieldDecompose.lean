import ZkFormal.NearV3.Render.Ups.FieldFacts
import ZkFormal.NearV3.Render.Ups.MemPosition

namespace ZkFormal.NearV3.Render.UpsGen

/-- Every live cursor belongs to one whole serialized field and its preceding fields. -/
theorem fieldAt_decompose (sh : List (Nat × Nat)) (p : Nat) (hp : p<fieldsLen sh) :
    ∃ pre post, sh=pre++((fieldAt sh p).1,(fieldAt sh p).2.2.1)::post ∧
      p=fieldsLen pre+(fieldAt sh p).2.1 ∧ (fieldAt sh p).2.2.2=nWin pre ∧
      (fieldAt sh p).2.1<(fieldAt sh p).2.2.1 := by
  induction sh generalizing p with
  | nil => simp at hp
  | cons f fs ih =>
    obtain ⟨st,len⟩ := f
    by_cases hl : p<len
    · refine ⟨[],fs,?_,?_,?_,?_⟩ <;> simp [fieldAt,hl,nWin,fieldsLen]
    · have hp' : p-len<fieldsLen fs := by simp only [fieldsLen_cons] at hp; omega
      obtain ⟨pre,post,hsh,hpos,hwin,hwidth⟩ := ih (p-len) hp'
      refine ⟨(st,len)::pre,post,?_,?_,?_,?_⟩
      · simpa [fieldAt,hl] using congrArg (fun l => (st,len)::l) hsh
      · simp only [fieldAt,hl,ite_false,fieldsLen_cons]
        omega
      · simp only [fieldAt,hl,ite_false]
        rw [hwin]
        by_cases hs : st=7 <;> simp [nWin,hs] <;> omega
      · simpa [fieldAt,hl] using hwidth

theorem field_slice_get (bytes : List Nat) (start width ix : Nat) (hi : ix<width) :
    ((bytes.drop start).take width).getD ix 0=bytes.getD (start+ix) 0 := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_take,hi]

end ZkFormal.NearV3.Render.UpsGen
