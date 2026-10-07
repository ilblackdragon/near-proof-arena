import ZkFormal.NearV3.Render.Ups.SourceHeader

namespace ZkFormal.NearV3.Render.UpsGen

 theorem header_tag_position {I : UpsInst} {Q : UpsPartI} (p ix wi : Nat)
    (hk : Q.kind=6 ∨ Q.kind=7 ∨ XcpB I Q=true) : rbV I Q 0 ix wi p=(Q.pb.getD 5 0 : Int) := by
  rcases hk with h | h | h
  · simp [rbV,sposV,h]
  · simp [rbV,sposV,h]
  · have hk : Q.kind=10 := by have hh := h; simp only [XcpB,Bool.and_eq_true,beq_iff_eq] at hh; exact hh.1
    simp [rbV,sposV,hk]

theorem SourceHeader.moved_hpl {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (p ix wi : Nat) (hk : Q.kind=6 ∨ Q.kind=7) :
    rbV I Q 1 ix wi p=(Q.phk : Int) := by
  have hp := h.hpl (by rcases hk with hk | hk; exact Or.inl hk; exact Or.inr (Or.inl hk))
  simp only [List.getD_eq_getElem?_getD] at hp
  rcases hk with hk | hk <;> simp [rbV,sposV,hk,hp]

theorem SourceHeader.split_hpl {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (p ix wi : Nat) (hk : XcpB I Q=true) :
    rbV I Q 6 ix wi p=(Q.phk : Int) := by
  have hp := h.hpl (Or.inr (Or.inr hk))
  have hk' : Q.kind=10 := by have hh := hk; simp only [XcpB,Bool.and_eq_true,beq_iff_eq] at hh; exact hh.1
  simp only [List.getD_eq_getElem?_getD] at hp
  simp [rbV,sposV,hk',hp]

theorem fieldAt_avoid_zero (sh : List (Nat × Nat)) (h : ∀ f ∈ sh, f.1 ≠ 0) (p : Nat) :
    (fieldAt sh p).1 ≠ 0 := by
  induction sh generalizing p with
  | nil => simp [fieldAt]
  | cons f fs ih =>
    by_cases hp : p < f.2
    · simp [fieldAt,hp,h f (by simp)]
    · simpa [fieldAt,hp] using ih (fun f hf => h f (by simp [hf])) (p-f.2)

theorem FieldsOk.tag_position {Q : UpsPartI} (f : FieldsOk Q) {p : Nat}
    (hs : (fieldAt Q.shape p).1=0) : p=0 := by
  by_cases hp : p=0
  · exact hp
  · have htail : ∀ x ∈ (nodeFields Q.ty Q.qhk (nWin Q.shape)).tail, x.1 ≠ 0 := by
      by_cases h1 : Q.ty ≤ 1 <;> by_cases h2 : 1 < Q.qhk <;>
        by_cases h3 : Q.ty=0 ∨ Q.ty=3 <;> by_cases h4 : 2 ≤ Q.ty <;>
        simp [nodeFields,h1,h2,h3,h4] <;> intro a b h <;> omega
    have hz := fieldAt_avoid_zero _ htail (p-1)
    rw [f.shape] at hs
    have he : fieldAt (nodeFields Q.ty Q.qhk (nWin Q.shape)) p =
        fieldAt (nodeFields Q.ty Q.qhk (nWin Q.shape)).tail (p-1) := by
      simp only [nodeFields,List.cons_append,List.nil_append,List.tail_cons,fieldAt,
        if_neg (show ¬ p<1 by omega),Nat.reduceEqDiff,ite_false,Nat.add_zero]
    rw [he] at hs
    exact False.elim (hz hs)

theorem SourceHeader.value_tag {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) {p : Nat} (ix wi : Nat) (f : FieldsOk Q)
    (hs : (fieldAt Q.shape p).1=0) (hk : Q.kind=4) :
    rbV I Q 0 ix wi p=1 := by
  have ht := h.insert_tag hk
  simp only [List.getD_eq_getElem?_getD] at ht
  have hz := f.tag_position hs
  simp [rbV,sposV,hk,aftV,AftB,ind,hz,ht]

end ZkFormal.NearV3.Render.UpsGen
