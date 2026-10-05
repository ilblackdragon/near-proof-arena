import ZkFormal.Bcs.TransStatements

/-!
# ZkFormal.Bcs.PosCount — `PosCountStmt`

Positions read as `bits`-bit digits of a uniform 256-bit RO answer, each reduced mod `2^n0`,
all land in a set of size `≤ a` for at most `a^p · 2^(256 - p·n0)` answers.  Proof: peel one
`bits`-bit digit at a time (`v ↦ (v % 2^bits, v / 2^bits)` is a bijection
`[0, 2^bits·N) ≅ [0, 2^bits) × [0, N)`); within a digit, `d ↦ d % 2^n0` is `2^(bits-n0)`-to-one.
-/

namespace ZkFormal.Bcs.Transport

open ArenaCore ArenaCore.Security

private theorem count_congr_mem' {α : Type} (l : List α) {E F : α → Prop}
    (h : ∀ x ∈ l, E x ↔ F x) : count l E = count l F :=
  Nat.le_antisymm (count_mono_mem l fun x hx => (h x hx).1)
    (count_mono_mem l fun x hx => (h x hx).2)

/-- Counting over `[0, K·m)` through the digits `(v % K, v / K)`. -/
theorem count_range_mul_digits (K : Nat) (P Q : Nat → Prop) :
    ∀ m, count (List.range (K * m)) (fun v => P (v % K) ∧ Q (v / K)) =
      count (List.range K) P * count (List.range m) Q
  | 0 => by simp [count]
  | m + 1 => by
    classical
    rw [Nat.mul_succ, List.range_add, count_append, count_map, count_range_mul_digits K P Q m,
      List.range_succ, count_append (List.range m)]
    have hblk : count (List.range K) (fun r => P ((K * m + r) % K) ∧ Q ((K * m + r) / K)) =
        count (List.range K) (fun r => Q m ∧ P r) := by
      apply count_congr_mem'
      intro r hr
      have hrK := List.mem_range.mp hr
      have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) hrK
      have h1 : (K * m + r) % K = r := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrK]
      have h2 : (K * m + r) / K = m := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hrK, Nat.zero_add]
      rw [h1, h2]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hblk]
    have hs : count [m] Q = if Q m then 1 else 0 := by
      rw [count_cons]; simp [count]
    rw [hs]
    by_cases hq : Q m
    · have : count (List.range K) (fun r => Q m ∧ P r) = count (List.range K) P :=
        count_congr_mem' _ fun r _ => ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
      rw [this, ite_eq_left hq, Nat.mul_add, Nat.mul_one]
    · have : count (List.range K) (fun r => Q m ∧ P r) = 0 := by
        have h := count_mono (List.range K) (E := fun r => Q m ∧ P r) (F := fun _ => False)
          fun _ h => hq h.1
        rw [count_const, ite_eq_right (fun h => h)] at h
        omega
      rw [this, ite_eq_right hq, Nat.add_zero, Nat.add_zero]

/-- `d ↦ d % K` on `[0, K·m)` is `m`-to-one. -/
theorem count_range_mul_mod (K m : Nat) (A : Nat → Prop) :
    count (List.range (K * m)) (fun d => A (d % K)) = count (List.range K) A * m := by
  have h := count_range_mul_digits K A (fun _ => True) m
  rw [count_const, ite_eq_left trivial, List.length_range] at h
  rw [← h]
  exact count_congr_mem' _ fun _ _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

/-- The digit-peeling induction, over `[0, 2^(bits·p)·M)`. -/
theorem count_digits_le (bits n0 : Nat) (A : Nat → Prop) (a : Nat) (hn : n0 ≤ bits)
    (hA : count (List.range (2 ^ n0)) A ≤ a) :
    ∀ p M, count (List.range (2 ^ (bits * p) * M))
        (fun v => ∀ i, i < p → A ((v >>> (bits * i)) % 2 ^ n0)) ≤
      a ^ p * 2 ^ ((bits - n0) * p) * M
  | 0, M => by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
    exact Nat.le_trans (count_le_length _ _) (by simp)
  | p + 1, M => by
    have ih := count_digits_le bits n0 A a hn hA p M
    have hsplit : 2 ^ (bits * (p + 1)) * M = 2 ^ bits * (2 ^ (bits * p) * M) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (bits * p)), Nat.mul_assoc]
    have hdvd : 2 ^ n0 ∣ 2 ^ bits := Nat.pow_dvd_pow 2 hn
    have hcongr : count (List.range (2 ^ bits * (2 ^ (bits * p) * M)))
        (fun v => ∀ i, i < p + 1 → A ((v >>> (bits * i)) % 2 ^ n0)) =
        count (List.range (2 ^ bits * (2 ^ (bits * p) * M)))
          (fun v => A (v % 2 ^ bits % 2 ^ n0) ∧
            (fun w => ∀ i, i < p → A ((w >>> (bits * i)) % 2 ^ n0)) (v / 2 ^ bits)) := by
      apply count_congr_mem'
      intro v _
      have hsh : ∀ i, v >>> (bits * (i + 1)) = (v / 2 ^ bits) >>> (bits * i) := by
        intro i
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          ← Nat.pow_add, Nat.mul_succ, Nat.add_comm (bits * i)]
      rw [Nat.mod_mod_of_dvd _ hdvd]
      constructor
      · intro h
        refine ⟨?_, fun i hi => ?_⟩
        · have := h 0 (Nat.succ_pos _)
          simpa using this
        · have := h (i + 1) (Nat.succ_lt_succ hi)
          rwa [hsh] at this
      · rintro ⟨h0, h⟩ i hi
        cases i with
        | zero => simpa using h0
        | succ i => rw [hsh]; exact h i (Nat.lt_of_succ_lt_succ hi)
    rw [hsplit, hcongr]
    refine Nat.le_trans (Nat.le_of_eq (count_range_mul_digits (2 ^ bits) (fun d => A (d % 2 ^ n0))
      (fun w => ∀ i, i < p → A ((w >>> (bits * i)) % 2 ^ n0)) _)) ?_
    have hb : 2 ^ bits = 2 ^ n0 * 2 ^ (bits - n0) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hn]
    have hd : count (List.range (2 ^ bits)) (fun d => A (d % 2 ^ n0)) ≤ a * 2 ^ (bits - n0) := by
      rw [hb, count_range_mul_mod]
      exact Nat.mul_le_mul_right _ hA
    calc count (List.range (2 ^ bits)) (fun d => A (d % 2 ^ n0)) *
            count (List.range (2 ^ (bits * p) * M))
              (fun w => ∀ i, i < p → A ((w >>> (bits * i)) % 2 ^ n0))
        ≤ (a * 2 ^ (bits - n0)) * (a ^ p * 2 ^ ((bits - n0) * p) * M) := Nat.mul_le_mul hd ih
      _ = a ^ (p + 1) * 2 ^ ((bits - n0) * (p + 1)) * M := by
        rw [Nat.pow_succ, Nat.mul_succ, Nat.pow_add]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem posCount : PosCountStmt := by
  intro p bits n0 A a hpb hn hA
  have hro : roRange = 2 ^ (bits * p) * 2 ^ (256 - p * bits) := by
    rw [← Nat.pow_add, Nat.mul_comm bits p, Nat.add_sub_cancel' hpb]; rfl
  have h256 : (256 : Nat) ^ 32 = roRange := by
    rw [roRange_eq]
  have hcongr : count (List.range roRange) (fun v =>
      ∀ x ∈ (List.range p).map (fun i => (Bytes.beToNat (LazyRO.answer v) >>> (bits * i)) % 2 ^ n0),
        A x) =
      count (List.range (2 ^ (bits * p) * 2 ^ (256 - p * bits)))
        (fun v => ∀ i, i < p → A ((v >>> (bits * i)) % 2 ^ n0)) := by
    rw [← hro]
    apply count_congr_mem'
    intro v hv
    have hv' : v < 256 ^ 32 := h256 ▸ List.mem_range.mp hv
    have hdec : Bytes.beToNat (LazyRO.answer v) = v := by
      rw [LazyRO.answer, Bytes.beToNat_beN, Nat.mod_eq_of_lt hv']
    rw [hdec]
    simp only [List.mem_map, List.mem_range]
    constructor
    · intro h i hi; exact h _ ⟨i, hi, rfl⟩
    · rintro h x ⟨i, hi, rfl⟩; exact h i hi
  rw [hcongr]
  refine Nat.le_trans (count_digits_le bits n0 A a hn hA p _) (Nat.le_of_eq ?_)
  have hpn : p * n0 ≤ p * bits := Nat.mul_le_mul_left p hn
  have hsub : (bits - n0) * p = p * bits - p * n0 := by
    rw [Nat.mul_comm, Nat.mul_sub]
  rw [Nat.mul_assoc, ← Nat.pow_add, hsub]
  generalize p * bits = x at hpb hpn
  generalize p * n0 = y at hpn
  rw [show x - y + (256 - x) = 256 - y by omega]

end ZkFormal.Bcs.Transport
