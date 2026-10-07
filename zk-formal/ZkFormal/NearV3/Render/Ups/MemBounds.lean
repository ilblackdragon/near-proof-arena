import ZkFormal.NearV3.Render.Ups.MemArith

/-! Carry ranges derived from bounds on the semantic integer operands. -/
namespace ZkFormal.NearV3.Render.UpsGen

theorem tV_bounds (I : UpsInst) (Q : UpsPartI) (i : Nat) :
    0 ≤ tV I Q i ∧ tV I Q i < 256 := by unfold tV; omega

/-- Before the last limb, three units of negative bias suffice for the
signed sum of source, child and length operands. -/
theorem coV_bounds (I : UpsInst) (Q : UpsPartI)
    (hx : ∀ i, i < 7 → -765 ≤ sigV Q * X1V I Q i ∧ sigV Q * X1V I Q i ≤ 1020) :
    ∀ i, i < 7 → -3 ≤ coV I Q i ∧ coV I Q i ≤ 4 := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hc := inside_carry I Q (i := 0) (by omega)
    have hb := tV_bounds I Q 0
    have hx := hx 0 hi
    simp only [ite_true] at hc
    omega
  | succ i ih =>
    intro hi
    have hc := inside_carry I Q (i := i + 1) (by omega)
    have hb := tV_bounds I Q (i + 1)
    have hx := hx (i + 1) hi
    have hp := ih (by omega)
    simp only [Nat.add_sub_cancel, show i + 1 ≠ 0 by omega, ite_false] at hc
    omega

/-- The outside carry remains an unsigned three-bit number. -/
theorem co2V_bounds (I : UpsInst) (Q : UpsPartI) (hn : Q.neg ≤ 1)
    (he : ∀ i, i < 8 → 0 ≤ EinV I Q i ∧ EinV I Q i ≤ 1785) :
    ∀ i, i < 8 → 0 ≤ co2V I Q i ∧ co2V I Q i < 8 := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hc := outside_carry I Q hn (i := 0) (by omega)
    have hb := tV_bounds I Q 0
    have he := he 0 hi
    rcases (show Q.neg = 0 ∨ Q.neg = 1 by omega) with h | h <;>
      simp only [h, Int.natCast_zero, Int.natCast_one, Int.sub_zero, Int.sub_self,
        Int.one_mul, Int.zero_mul, ite_true] at hc <;> omega
  | succ i ih =>
    intro hi
    have hc := outside_carry I Q hn (i := i + 1) (by omega)
    have hb := tV_bounds I Q (i + 1)
    have he := he (i + 1) hi
    have hp := ih (by omega)
    rcases (show Q.neg = 0 ∨ Q.neg = 1 by omega) with h | h <;>
      simp only [h, Int.natCast_zero, Int.natCast_one, Int.sub_zero, Int.sub_self,
        Int.one_mul, Int.zero_mul, Nat.add_sub_cancel, show i + 1 ≠ 0 by omega,
        ite_false] at hc <;> omega

/-- A nonnegative bounded total handles the unbiased final inside limb. -/
theorem cbV_bounds (I : UpsInst) (Q : UpsPartI)
    (hx : ∀ i, i < 7 → -765 ≤ sigV Q * X1V I Q i ∧ sigV Q * X1V I Q i ≤ 1020)
    (ht : 0 ≤ TV I Q ∧ TV I Q < 8 * 256 ^ 8) :
    ∀ i, i < 8 → 0 ≤ cbV I Q i ∧ cbV I Q i < 8 := by
  intro i hi
  by_cases h : i < 7
  · have hc := coV_bounds I Q hx i h
    simp only [cbV,h,ite_true]
    omega
  · have hi7 : i = 7 := by omega
    subst i
    simp only [cbV, Nat.lt_irrefl, ite_false, Int.add_zero, inside_last_high]
    simp only [Int.reducePow, Int.reduceMul] at ht ⊢
    omega

end ZkFormal.NearV3.Render.UpsGen
