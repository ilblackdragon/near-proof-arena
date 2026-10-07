import ZkFormal.NearV3.Render.Ups.WindowCursor

/-! Byte offsets in the final memory field of a canonical node. -/
namespace ZkFormal.NearV3.Render.UpsGen

theorem fieldsLen_append (a b : List (Nat × Nat)) : fieldsLen (a++b) = fieldsLen a + fieldsLen b := by
  simp [fieldsLen,List.sum_append]

/-- MEM is the final eight-byte field, so its offset is measured from the record's end. -/
theorem FieldsOk.mem_position {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hp : p < Q.q.length) (hs : (fieldAt Q.shape p).1 = 8) :
    p+8 = Q.q.length + (fieldAt Q.shape p).2.1 := by
  have he : Q.shape = nodeHeader Q.ty Q.qhk ++ (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) := by
    rw [← nodeFields_eq_header]; exact ok.shape
  have hl : Q.q.length = fieldsLen (nodeHeader Q.ty Q.qhk) + (32*nWin Q.shape+8) := by
    calc Q.q.length = fieldsLen Q.shape := ok.bytes
      _ = fieldsLen (nodeHeader Q.ty Q.qhk ++ (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)])) := congrArg fieldsLen he
      _ = _ := by rw [fieldsLen_append,fieldsLen_windows]
  have hstart : fieldsLen (nodeHeader Q.ty Q.qhk) ≤ p := by
    apply Classical.byContradiction; intro hn
    have hlt : p < fieldsLen (nodeHeader Q.ty Q.qhk) := by omega
    have hc := fieldAt_append_before (nodeHeader Q.ty Q.qhk)
      (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) p hlt
    rw [← he] at hc
    rw [hc] at hs
    have hm := (fieldAt_bounds (nodeHeader Q.ty Q.qhk) p hlt).2
    have hr := nodeHeader_states hm
    omega
  have hc := fieldAt_append_after (nodeHeader Q.ty Q.qhk)
    (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) p hstart
  rw [← he,nodeHeader_nWin] at hc
  have hw : 32*nWin Q.shape ≤ p-fieldsLen (nodeHeader Q.ty Q.qhk) := by
    apply Classical.byContradiction; intro hn
    rw [fieldAt_windows _ _ (by omega)] at hc
    rw [hc] at hs
    simp at hs
  rw [fieldAt_after_windows _ _ hw (by omega)] at hc
  rw [hc]; simp only; omega

end ZkFormal.NearV3.Render.UpsGen
