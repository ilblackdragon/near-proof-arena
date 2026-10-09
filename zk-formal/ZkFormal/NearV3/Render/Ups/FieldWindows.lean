import ZkFormal.NearV3.Render.Ups.FieldFacts

/-! Cursor formulas for the consecutive child-digest windows and final memory field. -/
namespace ZkFormal.NearV3.Render.UpsGen

/-- A child's 32 digest bytes form one complete window. -/
theorem fieldAt_windows (n p : Nat) (hp : p < 32 * n) :
    fieldAt (List.replicate n (7,32) ++ [(8,8)]) p = (7,p % 32,32,p / 32) := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, fieldAt]
    by_cases h : p < 32
    · simp only [h, ite_true]
      have hm : p % 32 = p := Nat.mod_eq_of_lt h
      have hd : p / 32 = 0 := Nat.div_eq_of_lt h
      rw [hm,hd]
    · simp only [h, ite_false]
      have hn : p - 32 < 32 * n := by omega
      rw [ih (p - 32) hn]
      simp only
      have hm : (p - 32) % 32 = p % 32 := by omega
      have hd : (p - 32) / 32 + 1 = p / 32 := by omega
      simp [hm,hd]

/-- The final eight bytes are the memory field, after all child windows. -/
theorem fieldAt_after_windows (n p : Nat) (hp : 32 * n ≤ p) (hl : p < 32 * n + 8) :
    fieldAt (List.replicate n (7,32) ++ [(8,8)]) p = (8,p - 32 * n,8,n) := by
  induction n generalizing p with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.sub_zero] at hp hl ⊢
            simp [fieldAt,hl]
  | succ n ih =>
    have hn : ¬ p < 32 := by omega
    simp only [List.replicate_succ, List.cons_append, fieldAt, hn, ite_false]
    rw [ih (p - 32) (by omega) (by omega)]
    have he : p - 32 - 32 * n = p - 32 * (n + 1) := by omega
    simp [he]

end ZkFormal.NearV3.Render.UpsGen
