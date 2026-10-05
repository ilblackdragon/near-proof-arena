import ZkFormal.Near.Render.Proof.RcptChars4

/-!
# ZkFormal.Near.Render.Proof.RcptNat — byte-serial arithmetic of the `rcpt` generator

Pure `Nat` facts about the generator's carries and borrows:

* `V x n = Σ_{j<n} x j · 256^j`; `chain x n = V x n / 256^n` (`chain_V`), so the
  digits `(x i + chain x i) % 256` are the bytes of `V x n` (`chain_digit`);
* `bchain`/`bdig`: `V a n + 256^n·borrow = V b n + b0 + V bdig n` (`bchain_eq`),
  the final borrow is `[V a n < V b n + b0]`;
* `conv`: `V (conv g v) n = Σ_j g_j 256^j V v (n − j)` (`V_conv`);
* bytes of `leBytes` (`leBytes_getD`), `V` of the bytes of `X` (`V_bytes`).
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

namespace RcptP

open RcptGen

/-- `Σ_{j<n} x j · 256^j` -/
def V (x : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => V x n + x n * 256 ^ n

theorem pow_pos' (n : Nat) : 0 < 256 ^ n := Nat.pow_pos (by decide)

theorem chain_V (x : Nat → Nat) : ∀ n, chain x n = V x n / 256 ^ n
  | 0 => by simp [chain, V]
  | n + 1 => by
    rw [chain, chain_V x n, V, Nat.pow_succ, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (pow_pos' n), Nat.add_comm]

theorem V_succ_div (x : Nat → Nat) (i : Nat) : V x (i + 1) / 256 ^ i = x i + chain x i := by
  rw [V, Nat.add_mul_div_right _ _ (pow_pos' i), chain_V, Nat.add_comm]

theorem V_div_mod (x : Nat → Nat) (i : Nat) : ∀ n, i < n → V x n / 256 ^ i % 256 = (x i + chain x i) % 256
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rcases (show i = n ∨ i < n by omega) with rfl | h'
    · rw [V_succ_div]
    · rw [← V_div_mod x i n h', V]
      have hp : 256 ^ n = 256 ^ (n - i - 1) * 256 * 256 ^ i := by
        rw [← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega
      have : x n * 256 ^ n = (x n * 256 ^ (n - i - 1) * 256) * 256 ^ i := by
        rw [hp, ← Nat.mul_assoc, ← Nat.mul_assoc]
      rw [this, Nat.add_mul_div_right _ _ (pow_pos' i), Nat.add_mul_mod_self_right]

/-- **Digits of a carry chain.** -/
theorem chain_digit (x : Nat → Nat) {i n : Nat} (h : i < n) :
    (x i + chain x i) % 256 = V x n / 256 ^ i % 256 := (V_div_mod x i n h).symm

theorem chain_zero_of (x : Nat → Nat) {n : Nat} (h : V x n < 256 ^ n) : chain x n = 0 := by
  rw [chain_V, Nat.div_eq_of_lt h]

/-- `x + chain = digit + 256 · next chain`. -/
theorem chain_step (x : Nat → Nat) (i : Nat) :
    x i + chain x i = (x i + chain x i) % 256 + 256 * chain x (i + 1) := by
  rw [chain]; omega

/-- `Σ_{j<m} f j` -/
def sumR (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumR f m + f m

theorem sum_range_map (f : Nat → Nat) : ∀ m, ((List.range m).map f).sum = sumR f m
  | 0 => rfl
  | m + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_map f m]; simp [sumR]

theorem sumR_add (f g : Nat → Nat) : ∀ m, sumR (fun j => f j + g j) m = sumR f m + sumR g m
  | 0 => rfl
  | m + 1 => by simp only [sumR, sumR_add f g m]; omega

theorem sumR_mul (f : Nat → Nat) (k : Nat) : ∀ m, sumR (fun j => f j * k) m = sumR f m * k
  | 0 => by simp [sumR]
  | m + 1 => by simp only [sumR, sumR_mul f k m, Nat.add_mul]

theorem sumR_congr {f g : Nat → Nat} : ∀ m, (∀ j, j < m → f j = g j) → sumR f m = sumR g m
  | 0, _ => rfl
  | m + 1, h => by rw [sumR, sumR, sumR_congr m (fun j hj => h j (by omega)), h m (by omega)]

theorem chain_le (x : Nat → Nat) {M : Nat} (hx : ∀ j, x j + M < 256 * M + 256) : ∀ i, chain x i ≤ M
  | 0 => Nat.zero_le _
  | i + 1 => by
    rw [chain]
    have := hx i; have := chain_le x hx i
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))

theorem V_add (x y : Nat → Nat) : ∀ n, V (fun i => x i + y i) n = V x n + V y n
  | 0 => rfl
  | n + 1 => by rw [V, V, V, V_add x y n, Nat.add_mul]; omega

theorem sumR_le {f g : Nat → Nat} : ∀ m, (∀ j, j < m → f j ≤ g j) → sumR f m ≤ sumR g m
  | 0, _ => Nat.le_refl _
  | m + 1, h => Nat.add_le_add (sumR_le m (fun j hj => h j (by omega))) (h m (by omega))

theorem V_lt (v : Nat → Nat) (hv : ∀ i, v i < 256) : ∀ n, V v n < 256 ^ n
  | 0 => by simp [V]
  | n + 1 => by
    rw [V, Nat.pow_succ]
    have := V_lt v hv n; have := hv n
    have : v n * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

theorem V_congr {x y : Nat → Nat} : ∀ n, (∀ i, i < n → x i = y i) → V x n = V y n
  | 0, _ => rfl
  | n + 1, h => by rw [V, V, V_congr n (fun i hi => h i (by omega)), h n (by omega)]

/-- The digits of a byte-valued function are its values. -/
theorem V_digit (v : Nat → Nat) (hv : ∀ i, v i < 256) {i n : Nat} (h : i < n) : V v n / 256 ^ i % 256 = v i := by
  rw [V_div_mod v i n h, chain_V, Nat.div_eq_of_lt (V_lt v hv i), Nat.add_zero, Nat.mod_eq_of_lt (hv i)]

/-! ## Bytes of a number -/

theorem toNats_leN_getD : ∀ (w X i : Nat), (toNats (leN w X)).getD i 0 = if i < w then X / 256 ^ i % 256 else 0
  | 0, _, _ => by simp [toNats, leN]
  | w + 1, X, 0 => by simp [toNats, leN]
  | w + 1, X, i + 1 => by
    have := toNats_leN_getD w (X / 256) i
    simp only [toNats, leN, List.map_cons, List.getD_cons_succ] at this ⊢
    rw [this]
    simp only [Nat.add_lt_add_iff_right, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 256]

theorem leBytes_getD (w X i : Nat) : (leBytes w X).getD i 0 = if i < w then X / 256 ^ i % 256 else 0 :=
  toNats_leN_getD w X i

theorem leBytes_getD_lt (w X i : Nat) : (leBytes w X).getD i 0 < 256 := by
  rw [leBytes_getD]; split <;> omega

theorem V_bytes_mod (X : Nat) : ∀ k, V (fun i => X / 256 ^ i % 256) k = X % 256 ^ k
  | 0 => by simp [V, Nat.mod_one]
  | k + 1 => by
    rw [V, V_bytes_mod X k, Nat.pow_succ, Nat.mod_mul]; simp only [Nat.mul_comm]

/-- `V` of the first `w` bytes of `X` (zero beyond). -/
theorem V_leBytes (w X : Nat) : ∀ k, V (fun i => (leBytes w X).getD i 0) k = X % 256 ^ (min k w) := by
  intro k
  rcases Nat.le_total k w with h | h
  · rw [Nat.min_eq_left h, ← V_bytes_mod X k]
    exact V_congr k (fun i hi => by rw [leBytes_getD, if_pos (by omega)])
  · rw [Nat.min_eq_right h]
    induction k with
    | zero => rw [show w = 0 by omega, ← V_bytes_mod X 0]; rfl
    | succ k ih =>
      rcases (show w = k + 1 ∨ w ≤ k by omega) with rfl | h'
      · rw [← V_bytes_mod X (k + 1)]
        exact V_congr _ (fun i hi => by rw [leBytes_getD, if_pos (by omega)])
      · rw [V, ih h', leBytes_getD, if_neg (by omega)]; simp

theorem V_leBytes_of {w X k : Nat} (hk : w ≤ k) (hX : X < 256 ^ w) : V (fun i => (leBytes w X).getD i 0) k = X := by
  rw [V_leBytes, Nat.min_eq_right hk, Nat.mod_eq_of_lt hX]

/-- Byte `i` of `X` from a chain whose value is `X`. -/
theorem chain_byte (x : Nat → Nat) {w X i : Nat} (hi : i < w) (hV : V x w = X) :
    (x i + chain x i) % 256 = (leBytes w X).getD i 0 := by
  rw [chain_digit x hi, hV, leBytes_getD, if_pos hi]

/-! ## Borrow chains -/

section
variable (a b : Nat → Nat) (b0 : Nat)

theorem bchain_le : ∀ i, b0 ≤ 1 → bchain a b b0 i ≤ 1
  | 0, h => h
  | i + 1, _ => by simp only [bchain]; split <;> omega

theorem bdig_step (ha : ∀ i, a i < 256) (hb : ∀ i, b i < 256) (h0 : b0 ≤ 1) (i : Nat) :
    a i + 256 * bchain a b b0 (i + 1) = b i + bchain a b b0 i + bdig a b b0 i ∧ bdig a b b0 i < 256 := by
  have := ha i; have := hb i; have := bchain_le a b b0 i h0
  simp only [bdig, bchain]
  split <;> omega

theorem bchain_eq (ha : ∀ i, a i < 256) (hb : ∀ i, b i < 256) (h0 : b0 ≤ 1) :
    ∀ n, V a n + 256 ^ n * bchain a b b0 n = V b n + b0 + V (bdig a b b0) n
  | 0 => by simp [V, bchain]
  | n + 1 => by
    have ih := bchain_eq ha hb h0 n
    have st := (bdig_step a b b0 ha hb h0 n).1
    simp only [V, Nat.pow_succ]
    have e1 : 256 ^ n * 256 * bchain a b b0 (n + 1) = 256 ^ n * (256 * bchain a b b0 (n + 1)) := by
      rw [Nat.mul_assoc]
    rw [e1]
    have e2 : 256 ^ n * (256 * bchain a b b0 (n + 1)) = 256 ^ n * (b n + bchain a b b0 n + bdig a b b0 n) -
        a n * 256 ^ n := by rw [← st]; rw [Nat.mul_add]; rw [Nat.mul_comm (a n)]; omega
    have e3 : 256 ^ n * (b n + bchain a b b0 n + bdig a b b0 n) =
        b n * 256 ^ n + 256 ^ n * bchain a b b0 n + bdig a b b0 n * 256 ^ n := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm (256 ^ n) (b n), Nat.mul_comm (256 ^ n) (bdig a b b0 n)]
    have e4 : a n * 256 ^ n ≤ 256 ^ n * (b n + bchain a b b0 n + bdig a b b0 n) := by
      rw [← st, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega

theorem bdig_lt (ha : ∀ i, a i < 256) (hb : ∀ i, b i < 256) (h0 : b0 ≤ 1) (i : Nat) : bdig a b b0 i < 256 :=
  (bdig_step a b b0 ha hb h0 i).2

theorem bchain_final (ha : ∀ i, a i < 256) (hb : ∀ i, b i < 256) (h0 : b0 ≤ 1) (n : Nat) :
    bchain a b b0 n = if V a n < V b n + b0 then 1 else 0 := by
  have e := bchain_eq a b b0 ha hb h0 n
  have hl := V_lt _ (bdig_lt a b b0 ha hb h0) n
  have := bchain_le a b b0 n h0
  have hp := pow_pos' n
  split
  · rcases (show bchain a b b0 n = 0 ∨ bchain a b b0 n = 1 by omega) with h | h
    · rw [h] at e; omega
    · exact h
  · rcases (show bchain a b b0 n = 0 ∨ bchain a b b0 n = 1 by omega) with h | h
    · exact h
    · rw [h] at e; omega

theorem V_bdig (ha : ∀ i, a i < 256) (hb : ∀ i, b i < 256) (h0 : b0 ≤ 1) {n : Nat} (h : V b n + b0 ≤ V a n) :
    V (bdig a b b0) n = V a n - V b n - b0 := by
  have e := bchain_eq a b b0 ha hb h0 n
  rw [bchain_final a b b0 ha hb h0 n, if_neg (by omega)] at e
  omega

end

/-! ## Convolutions -/

theorem conv_eq (g : List Nat) (v : Nat → Nat) (i : Nat) :
    conv g v i = sumR (fun j => if j ≤ i then g.getD j 0 * v (i - j) else 0) g.length := by
  rw [conv, sum_range_map]

theorem conv_le (g : List Nat) (v : Nat → Nat) (hv : ∀ i, v i ≤ 255) (i : Nat) :
    conv g v i ≤ sumR (fun j => g.getD j 0 * 255) g.length := by
  rw [conv_eq]
  apply sumR_le
  intro j _
  split
  · exact Nat.mul_le_mul_left _ (hv _)
  · exact Nat.zero_le _

theorem V_conv (g : List Nat) (v : Nat → Nat) :
    ∀ n, V (conv g v) n = sumR (fun j => g.getD j 0 * 256 ^ j * V v (n - j)) g.length
  | 0 => by
    rw [V]; symm
    exact (sumR_congr (g := fun _ => 0) _ (fun j _ => by simp [V])).trans
      (by induction g.length with | zero => rfl | succ m ih => simp [sumR, ih])
  | n + 1 => by
    rw [V, V_conv g v n, conv_eq, ← sumR_mul, ← sumR_add]
    apply sumR_congr
    intro j _
    split
    · rename_i hj
      rw [show n + 1 - j = (n - j) + 1 by omega, V, Nat.mul_add]
      have : g.getD j 0 * 256 ^ j * (v (n - j) * 256 ^ (n - j)) = g.getD j 0 * v (n - j) * 256 ^ n := by
        rw [show n = j + (n - j) by omega, Nat.pow_add]
        simp only [show j + (n - j) - j = n - j by omega]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [this]
    · rw [show n + 1 - j = 0 by omega, show n - j = 0 by omega]; simp

/-- `V` of a scaled function. -/
theorem V_smul (a : Nat) (x : Nat → Nat) : ∀ n, V (fun i => a * x i) n = a * V x n
  | 0 => rfl
  | n + 1 => by rw [V, V, V_smul a x n, Nat.mul_add, Nat.mul_assoc]

theorem runSum_eq0 (x : Nat → Nat) : ∀ i, runSum x i = 0 → ∀ j, j ≤ i → x j = 0
  | 0, h, j, hj => by rw [runSum_zero] at h; rw [show j = 0 by omega]; exact h
  | i + 1, h, j, hj => by
    rw [runSum_succ] at h
    rcases (show j = i + 1 ∨ j ≤ i by omega) with rfl | hj'
    · omega
    · exact runSum_eq0 x i (by omega) j hj'

theorem V_zero (x : Nat → Nat) : ∀ n, (∀ i, i < n → x i = 0) → V x n = 0
  | 0, _ => rfl
  | n + 1, h => by rw [V, V_zero x n (fun i hi => h i (by omega)), h n (by omega)]; simp

end RcptP

end ZkFormal.Near.Render
