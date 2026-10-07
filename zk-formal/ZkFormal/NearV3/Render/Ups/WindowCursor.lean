import ZkFormal.NearV3.Render.Ups.FieldSucc

/-! Exact positions of child windows within canonical node serializations. -/
namespace ZkFormal.NearV3.Render.UpsGen

def nodeHeader (ty hk : Nat) : List (Nat × Nat) :=
  [(0,1)] ++
  (if ty ≤ 1 then [(1,4),(2,1)] ++ (if 1 < hk then [(3,hk-1)] else []) else []) ++
  (if ty = 0 ∨ ty = 3 then [(4,4),(5,32)] else []) ++
  (if 2 ≤ ty then [(6,2)] else [])

theorem nodeFields_eq_header (ty hk n : Nat) :
    nodeFields ty hk n = nodeHeader ty hk ++ (List.replicate n (7,32) ++ [(8,8)]) := by
  simp [nodeFields,nodeHeader,List.append_assoc]

theorem fieldsLen_windows (n : Nat) :
    fieldsLen (List.replicate n (7,32) ++ [(8,8)]) = 32*n+8 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,fieldsLen_cons,ih]; omega

theorem nodeHeader_states {ty hk s l : Nat} (h : (s,l) ∈ nodeHeader ty hk) : s < 7 := by
  simp only [nodeHeader,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with ((h | h) | h) | h
  · cases h; omega
  · split at h
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with (h | h) | h
      · cases h; omega
      · cases h; omega
      · split at h
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at h; cases h; omega
        · cases h
    · cases h
  · split at h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h | h <;> cases h <;> omega
    · cases h
  · split at h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h; cases h; omega
    · cases h

theorem nodeHeader_nWin (ty hk : Nat) : nWin (nodeHeader ty hk) = 0 := by
  unfold nWin
  apply List.length_eq_zero_iff.2
  apply List.eq_nil_iff_forall_not_mem.2
  intro f hf
  simp only [List.mem_filter] at hf
  have hs := nodeHeader_states hf.1
  simp only [decide_eq_true_eq] at hf
  omega

theorem fieldAt_windows_iff (n p : Nat) :
    (fieldAt (List.replicate n (7,32) ++ [(8,8)]) p).1 = 7 ↔ p < 32*n := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    have hge : 32*n ≤ p := by omega
    by_cases hl : p < 32*n+8
    · rw [fieldAt_after_windows n p hge hl] at h; simp at h
    · rw [fieldAt_past _ p (by rw [fieldsLen_windows]; omega)] at h; simp at h
  · intro h; rw [fieldAt_windows n p h]

/-- A cursor in state CH has the exact quotient/remainder window coordinates. -/
theorem FieldsOk.window {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hs : (fieldAt Q.shape p).1 = 7) :
    fieldsLen (nodeHeader Q.ty Q.qhk) ≤ p ∧
    p - fieldsLen (nodeHeader Q.ty Q.qhk) < 32 * nWin Q.shape ∧
    fieldAt Q.shape p =
      (7,(p - fieldsLen (nodeHeader Q.ty Q.qhk)) % 32,32,
        (p - fieldsLen (nodeHeader Q.ty Q.qhk)) / 32) := by
  have he : Q.shape = nodeHeader Q.ty Q.qhk ++ (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) := by
    rw [← nodeFields_eq_header]; exact ok.shape
  have hp : fieldsLen (nodeHeader Q.ty Q.qhk) ≤ p := by
    apply Classical.byContradiction; intro hn
    have hl : p < fieldsLen (nodeHeader Q.ty Q.qhk) := by omega
    have hc := fieldAt_append_before (nodeHeader Q.ty Q.qhk)
      (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) p hl
    rw [← he] at hc
    rw [hc] at hs
    have hm := (fieldAt_bounds (nodeHeader Q.ty Q.qhk) p hl).2
    have ht := nodeHeader_states hm
    omega
  have hc := fieldAt_append_after (nodeHeader Q.ty Q.qhk)
    (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) p hp
  rw [← he,nodeHeader_nWin] at hc
  have ht : p - fieldsLen (nodeHeader Q.ty Q.qhk) < 32 * nWin Q.shape := by
    apply (fieldAt_windows_iff _ _).1
    rw [hc] at hs
    exact hs
  refine ⟨hp,ht,?_⟩
  rw [hc,fieldAt_windows _ _ ht]
  simp

end ZkFormal.NearV3.Render.UpsGen
