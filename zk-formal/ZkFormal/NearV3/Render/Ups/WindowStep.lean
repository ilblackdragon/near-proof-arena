import ZkFormal.NearV3.Render.Ups.WindowCursor

/-! Window boundaries of canonical node serializations. -/
namespace ZkFormal.NearV3.Render.UpsGen

/-- A live child window has an in-range zero-based index. -/
theorem FieldsOk.window_index {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hs : (fieldAt Q.shape p).1 = 7) :
    (fieldAt Q.shape p).2.2.2 < nWin Q.shape := by
  obtain ⟨_,hp,he⟩ := ok.window hs
  rw [he]; simp only; omega

/-- At the end of a child digest the next row starts the next child or the memory tail. -/
theorem FieldsOk.window_next {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hs : (fieldAt Q.shape p).1 = 7)
    (hend : (fieldAt Q.shape p).2.1 + 1 = (fieldAt Q.shape p).2.2.1) :
    fieldAt Q.shape (p+1) =
      if (fieldAt Q.shape p).2.2.2 + 1 = nWin Q.shape then (8,0,8,nWin Q.shape)
      else (7,0,32,(fieldAt Q.shape p).2.2.2+1) := by
  obtain ⟨hp,hw,hcur⟩ := ok.window hs
  have he : Q.shape = nodeHeader Q.ty Q.qhk ++ (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) := by
    rw [← nodeFields_eq_header]; exact ok.shape
  have hc := fieldAt_append_after (nodeHeader Q.ty Q.qhk)
    (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) (p+1) (by omega)
  rw [← he,nodeHeader_nWin] at hc
  rw [hcur] at hend ⊢
  simp only at hend ⊢
  by_cases hl : (p - fieldsLen (nodeHeader Q.ty Q.qhk)) / 32 + 1 = nWin Q.shape
  · rw [if_pos hl,hc]
    have heq : p+1 - fieldsLen (nodeHeader Q.ty Q.qhk) = 32 * nWin Q.shape := by omega
    rw [heq,fieldAt_after_windows _ _ (by omega) (by omega)]
    simp
  · rw [if_neg hl,hc]
    have hb : p+1-fieldsLen (nodeHeader Q.ty Q.qhk) < 32*nWin Q.shape := by omega
    rw [fieldAt_windows _ _ hb]
    have hm : (p+1-fieldsLen (nodeHeader Q.ty Q.qhk)) % 32 = 0 := by omega
    have hd : (p+1-fieldsLen (nodeHeader Q.ty Q.qhk)) / 32 =
        (p-fieldsLen (nodeHeader Q.ty Q.qhk)) / 32 + 1 := by omega
    simp [hm,hd]

/-- Entering the child section from another field starts its first window. -/
theorem FieldsOk.window_enter {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hprev : (fieldAt Q.shape p).1 ≠ 7) (hnext : (fieldAt Q.shape (p+1)).1 = 7) :
    (fieldAt Q.shape (p+1)).2.2.2 = 0 := by
  obtain ⟨hp,hw,hcur⟩ := ok.window hnext
  have he : Q.shape = nodeHeader Q.ty Q.qhk ++ (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) := by
    rw [← nodeFields_eq_header]; exact ok.shape
  have hbefore : p < fieldsLen (nodeHeader Q.ty Q.qhk) := by
    apply Classical.byContradiction; intro hn
    have hc := fieldAt_append_after (nodeHeader Q.ty Q.qhk)
      (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) p (by omega)
    rw [← he,nodeHeader_nWin,fieldAt_windows _ _ (by omega)] at hc
    exact hprev (by rw [hc])
  rw [hcur]; simp only
  have hz : p+1-fieldsLen (nodeHeader Q.ty Q.qhk) = 0 := by omega
  rw [hz]

end ZkFormal.NearV3.Render.UpsGen
