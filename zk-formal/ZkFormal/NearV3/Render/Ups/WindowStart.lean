import ZkFormal.NearV3.Render.Ups.WindowCursor

namespace ZkFormal.NearV3.Render.UpsGen

/-- CH index zero locates the byte offset by its window ordinal. -/
theorem FieldsOk.window_start {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hs : (fieldAt Q.shape p).1=7) (hi : (fieldAt Q.shape p).2.1=0) :
    p=fieldsLen (nodeHeader Q.ty Q.qhk)+32*(fieldAt Q.shape p).2.2.2 := by
  obtain ⟨hge,hlt,he⟩ := ok.window hs
  rw [he] at hi ⊢
  simp only [Prod.fst,Prod.snd] at hi ⊢
  omega

/-- Target selection at a CH start chooses the first or last serialized child. -/
theorem FieldsOk.target_start {Q : UpsPartI} (ok : FieldsOk Q) (I : UpsInst) {p : Nat}
    (hs : (fieldAt Q.shape p).1=7) (hi : (fieldAt Q.shape p).2.1=0)
    (ht : TgtB I Q 7 (fieldAt Q.shape p).2.2.2=true) :
    p=fieldsLen (nodeHeader Q.ty Q.qhk)+
      32*(if S15B I Q then nWin Q.shape-1 else 0) := by
  have hpos := ok.window_start hs hi
  have hsel : (fieldAt Q.shape p).2.2.2=
      if S15B I Q then nWin Q.shape-1 else 0 := by
    cases h15 : S15B I Q <;> simp [TgtB,FwB,LastwB,h15] at ht ⊢ <;> omega
  rw [hsel] at hpos
  exact hpos
end ZkFormal.NearV3.Render.UpsGen
