import WasmBase.KeccakAir
import WasmBase.ChiVectors
/-!
# WasmBase.KeccakSteps — the per-step lemmas for the Keccak-f round

`WasmBase.KeccakAir` defines the round row.  This file proves the facts a round lemma needs, one step
at a time, each about a **field row** (`Expr.eval`) and its `toNat` image:

* `bits_*` — the field/evaluation plumbing: `boolE e = 0` gives `e ∈ {0,1}`, `xor2`/`xorEq` evaluated
  on bits, `sel` evaluated through `rcSel`.
* `theta_parity` — the 4 equations of `thetaConstr` imply
  `C[x][k] = A[x][k] ^ A[x+5][k] ^ A[x+10][k] ^ A[x+15][k] ^ A[x+20][k]` (5-way XOR through the
  three `CA` auxiliaries).
* `iota_const` — the one-hot `sel` selects exactly `rc[r]`: with `Σ sel_r = 1` and every `sel_r` a
  bit, `rcSel k = rcBit r k` for the unique `r` with `sel_r = 1`.
* `rho_pi_index` — the static index facts: `piSrc` is a bijection of `0..24` inverse to the spec's
  `piTgt`, so `bBit` reads each `T` bit exactly once per round.

Everything is stated on natural numbers (`Row.cur i` is an `Fp`; `toNat` of a bit is the bit), which
is what `KeccakRound.lean` composes.
-/
set_option linter.unusedSimpArgs false

namespace WasmBase
namespace Chips
namespace Keccak

open ZkFormal.Algebra

/-! ## Evaluation of the expression builders -/

theorem e2_eval (rw : Row) : e2.eval rw = 2 := by
  show ((Expr.c 2).eval rw) = (2 : F)
  rw [Expr.eval_c]
  decide

theorem e1_eval (rw : Row) : e1.eval rw = 1 := by
  show ((Expr.c 1).eval rw) = (1 : F)
  rw [Expr.eval_c]
  decide

theorem e0_eval (rw : Row) : e0.eval rw = 0 := by
  show ((Expr.c 0).eval rw) = (0 : F)
  rw [Expr.eval_c]
  decide

theorem eval_boolE (rw : Row) (e : Expr) :
    (boolE e).eval rw = e.eval rw * (e.eval rw - 1) := by
  simp only [boolE, Expr.eval_sub', Expr.eval_mul', e1_eval]

theorem eval_xor2 (rw : Row) (a b : Expr) :
    (xor2 a b).eval rw = a.eval rw + b.eval rw - 2 * (a.eval rw * b.eval rw) := by
  simp only [xor2, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', e2_eval]

theorem eval_xorEq (rw : Row) (a b r : Expr) :
    (xorEq a b r).eval rw = a.eval rw + b.eval rw - 2 * (a.eval rw * b.eval rw) - r.eval rw := by
  simp only [xorEq, xor2, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', e2_eval]

/-! ## Bits: `Fp` values in `{0,1}` and their `toNat` -/

/-- A booleanity constraint `e·(e−1) = 0` puts `e` in `{0,1}`. -/
theorem bit_cases {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := WasmBase.bool_cases h

theorem bit_toNat {x : F} (h : x = 0 ∨ x = 1) : x.toNat = 0 ∨ x.toNat = 1 := by
  rcases h with h | h
  · exact Or.inl (WasmBase.toNat_of_eq_zero h)
  · exact Or.inr (WasmBase.toNat_of_eq_one h)

theorem bit_of_toNat {x : F} (h : x.toNat = 0 ∨ x.toNat = 1) : x = 0 ∨ x = 1 := by
  rcases h with h | h
  · exact Or.inl (WasmBase.eq_of_toNat h)
  · exact Or.inr (WasmBase.eq_of_toNat h)

/-- `toNat` of a bit is the bit. -/
theorem bit_toNat_val {x : F} (h : x = 0 ∨ x = 1) : x.toNat < 2 := by
  rcases bit_toNat h with h | h <;> omega

theorem nat_xor_cases {a b : Nat} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ^^^ b = 0 ∨ a ^^^ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- **XOR of bits, on `toNat`**: the degree-2 expression `a + b − 2ab` is `a ^^^ b`. -/
theorem toNat_xor2 {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a + b - 2 * (a * b)).toNat = a.toNat ^^^ b.toNat := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- `(1 − a)` on a bit is the complement. -/
theorem toNat_one_sub {a : F} (ha : a = 0 ∨ a = 1) : ((1 : F) - a).toNat = 1 - a.toNat := by
  rcases ha with rfl | rfl <;> decide

/-- `a · b` on bits, on `toNat`. -/
theorem toNat_mul {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a * b).toNat = a.toNat &&& b.toNat := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-! ## `theta`: the 5-way parity

The four equations of `thetaConstr x k` are

```
ca0 = A[x] ^ A[x+5]
ca1 = ca0  ^ A[x+10]
ca2 = ca1  ^ A[x+15]
C[x] = ca2  ^ A[x+20]
```

so `C[x]` is the 5-way XOR by transitivity of `^^^`.  Stated over `F` (`Expr.eval`) with the bits'
`toNat`s, since that is how the round lemma consumes it. -/

/-- In `F_p`, `x − y = 0` implies `x = y`.  `sub` on `Nat.toNat` is `(x + (P − y)) % P`, and that
is zero only at `x = y` because both are `< P`. -/
theorem nat_sub_zero {a b : Nat} (ha : a < P) (hb : b < P) (h : (a + (P - b)) % P = 0) : a = b := by
  have hP : 0 < P := by have := ZkFormal.Algebra.P_lt; omega
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt ha] at h
    omega
  · rcases Nat.lt_or_ge (a + (P - b)) P with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h; omega
    · rcases Nat.lt_or_ge (a + (P - b)) (2 * P) with h'' | h''
      · rw [Nat.mod_eq_sub_mod h'] at h
        rw [Nat.mod_eq_of_lt (by omega : a + (P - b) - P < P)] at h
        omega
      · omega

theorem sub_eq_zero {a b : F} (h : a - b = 0) : a = b := by
  have hsub : Fp.sub a b = 0 := h
  have h1 : (a.toNat + (P - b.toNat)) % P = 0 := by
    have := congrArg Fp.toNat hsub
    rw [Fp.toNat_sub, Fp.toNat_zero] at this
    simpa using this
  exact Fp.ext (nat_sub_zero (Fp.toNat_lt a) (Fp.toNat_lt b) h1)

/-- One chain step: `xorEq a b r = 0` on bits says `r.toNat = a.toNat ^^^ b.toNat`. -/
theorem xorEq_nat {a b r : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (_hr : r = 0 ∨ r = 1)
    (h : a + b - 2 * (a * b) - r = 0) : r.toNat = a.toNat ^^^ b.toNat := by
  have hx : (a + b - 2 * (a * b)).toNat = a.toNat ^^^ b.toNat := toNat_xor2 ha hb
  have heq : a + b - 2 * (a * b) = r := sub_eq_zero h
  rw [← heq, hx]

/-- **`theta`'s parity**: the four chain equations give the 5-way XOR. -/
theorem theta_parity (rw : Row) (x k : Nat)
    (h0b : rw.cur (aBit x k) = 0 ∨ rw.cur (aBit x k) = 1)
    (h1b : rw.cur (aBit (x + 5) k) = 0 ∨ rw.cur (aBit (x + 5) k) = 1)
    (h2b : rw.cur (aBit (x + 10) k) = 0 ∨ rw.cur (aBit (x + 10) k) = 1)
    (h3b : rw.cur (aBit (x + 15) k) = 0 ∨ rw.cur (aBit (x + 15) k) = 1)
    (h4b : rw.cur (aBit (x + 20) k) = 0 ∨ rw.cur (aBit (x + 20) k) = 1)
    (hc0 : rw.cur (caBit x k 0) = 0 ∨ rw.cur (caBit x k 0) = 1)
    (hc1 : rw.cur (caBit x k 1) = 0 ∨ rw.cur (caBit x k 1) = 1)
    (hc2 : rw.cur (caBit x k 2) = 0 ∨ rw.cur (caBit x k 2) = 1)
    (hC : rw.cur (cBit x k) = 0 ∨ rw.cur (cBit x k) = 1)
    (eq0 : rw.cur (aBit x k) + rw.cur (aBit (x + 5) k) -
        2 * (rw.cur (aBit x k) * rw.cur (aBit (x + 5) k)) - rw.cur (caBit x k 0) = 0)
    (eq1 : rw.cur (caBit x k 0) + rw.cur (aBit (x + 10) k) -
        2 * (rw.cur (caBit x k 0) * rw.cur (aBit (x + 10) k)) - rw.cur (caBit x k 1) = 0)
    (eq2 : rw.cur (caBit x k 1) + rw.cur (aBit (x + 15) k) -
        2 * (rw.cur (caBit x k 1) * rw.cur (aBit (x + 15) k)) - rw.cur (caBit x k 2) = 0)
    (eq3 : rw.cur (caBit x k 2) + rw.cur (aBit (x + 20) k) -
        2 * (rw.cur (caBit x k 2) * rw.cur (aBit (x + 20) k)) - rw.cur (cBit x k) = 0) :
    (rw.cur (cBit x k)).toNat =
      (rw.cur (aBit x k)).toNat ^^^ (rw.cur (aBit (x + 5) k)).toNat ^^^
      (rw.cur (aBit (x + 10) k)).toNat ^^^ (rw.cur (aBit (x + 15) k)).toNat ^^^
      (rw.cur (aBit (x + 20) k)).toNat := by
  have h0 := xorEq_nat h0b h1b hc0 eq0
  have h1 := xorEq_nat hc0 h2b hc1 eq1
  have h2 := xorEq_nat hc1 h3b hc2 eq2
  have h3 := xorEq_nat hc2 h4b hC eq3
  rw [h3, h2, h1, h0, Nat.xor_assoc, Nat.xor_assoc, Nat.xor_assoc]

variable (rw : Row)

/-! ## `iota`: the one-hot `sel` selects exactly one round constant

`selConstraints` says every `sel_r` is a bit and `Σ_r sel_r = 1`; `bits_onehot` turns that into
"exactly one `r` has `sel_r = 1`", and `rcSelAux_at` then collapses the constant selector. -/

theorem zero_add_f (a : F) : (0 : F) + a = a := by grind
theorem add_zero_f (a : F) : a + (0 : F) = a := by grind
theorem one_mul_f (a : F) : (1 : F) * a = a := by grind
theorem zero_mul_f (a : F) : (0 : F) * a = 0 := by grind

def selSumF : Nat → F
  | 0 => 0
  | n + 1 => selSumF n + rw.cur (selE n)

def selSumN : Nat → Nat
  | 0 => 0
  | n + 1 => selSumN n + (rw.cur (selE n)).toNat

theorem onehotAux_eq_selSumF (N : Nat) : (onehotAux N).eval rw = selSumF rw N := by
  induction N with
  | zero => show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    show (Expr.eval rw (onehotAux n) + Expr.eval rw (v (selE n))) = _
    rw [ih, show (v (selE n)).eval rw = rw.cur (selE n) from rfl]
    rfl

theorem selSumN_le (N : Nat) (hb : ∀ i, i < N → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1) :
    selSumN rw N ≤ N := by
  induction N with
  | zero => simp [selSumN]
  | succ n ih =>
    have := ih (fun i hi => hb i (by omega))
    have hn := bit_toNat (hb n (by omega))
    simp only [selSumN]
    omega

/-- `toNat` of the `Fp` sum is the `Nat` sum: every partial sum is a small `Nat` (`≤ 24`), so the
modular addition never wraps. -/
theorem selSumF_toNat : ∀ N, N < P → (∀ i, i < N → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1) →
    (selSumF rw N).toNat = selSumN rw N := by
  intro N
  induction N with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hN hb
    have hb' : ∀ i, i < n → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1 := fun i hi => hb i (by omega)
    have hn := bit_toNat (hb n (by omega))
    have hle := selSumN_le rw n hb'
    have hih := ih (by have := ZkFormal.Algebra.P_lt; omega) hb'
    show (selSumF rw n + rw.cur (selE n)).toNat = selSumN rw n + (rw.cur (selE n)).toNat
    have hadd := ZkFormal.Algebra.Fp.toNat_add (selSumF rw n) (rw.cur (selE n))
    rw [show selSumF rw n + rw.cur (selE n) =
        Fp.add (selSumF rw n) (rw.cur (selE n)) from rfl, hadd]
    simp only [hih]
    exact Nat.mod_eq_of_lt (by omega)


/-- A list of bits summing to zero is all zeros. -/
theorem sum_eq_zero_bits : ∀ (l : List Nat), (∀ x ∈ l, x = 0 ∨ x = 1) → l.sum = 0 →
    ∀ x ∈ l, x = 0 := by
  intro l
  induction l with
  | nil => intro _ _ x hx; exact absurd hx (by simp)
  | cons a as ih =>
    intro h hs x hx
    rw [List.sum_cons] at hs
    have ha : a = 0 := by rcases h a (List.mem_cons_self ..) with h' | h' <;> omega
    rcases List.mem_cons.1 hx with hxa | hx'
    · omega
    · exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by omega) x hx'

/-- A list of bits summing to one has exactly one `1`. -/
theorem sum_eq_one_bits : ∀ (N : Nat) (b : Nat → Nat),
    (∀ i ∈ List.range N, b i = 0 ∨ b i = 1) → ((List.range N).map b).sum = 1 →
    ∃ r, r < N ∧ b r = 1 ∧ ∀ j, j < N → j ≠ r → b j = 0 := by
  intro N
  induction N with
  | zero => intro b _ hs; simp at hs
  | succ n ih =>
    intro b hb hs
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton] at hs
    have hbn : b n = 0 ∨ b n = 1 := hb n (by simp)
    have hb' : ∀ i ∈ List.range n, b i = 0 ∨ b i = 1 := by
      intro i hi; exact hb i (by simp only [List.mem_range] at hi ⊢; omega)
    rcases hbn with h0 | h1
    · have hs' : ((List.range n).map b).sum = 1 := by omega
      obtain ⟨r, hr, hbr, hzero⟩ := ih b hb' hs'
      refine ⟨r, by omega, hbr, ?_⟩
      intro j hj hne
      rcases Nat.lt_or_ge j n with h' | h'
      · exact hzero j h' hne
      · have : j = n := by omega
        subst this; exact h0
    · have hs' : ((List.range n).map b).sum = 0 := by omega
      refine ⟨n, by omega, h1, ?_⟩
      intro j hj _
      exact sum_eq_zero_bits _ (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        exact hb' i hi) hs' (b j)
        (List.mem_map.2 ⟨j, by simp only [List.mem_range]; omega, rfl⟩)

theorem selSumN_eq_map_sum : ∀ N, selSumN rw N =
    ((List.range N).map (fun i => (rw.cur (selE i)).toNat)).sum := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show selSumN rw n + (rw.cur (selE n)).toNat = _
    rw [ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]

/-- **The one-hot sum is exactly 1.**  If every `sel_r` (`r < N`) is a bit and their `Fp` sum is 1,
then their `Nat` sum is 1 too — so exactly one `sel_r` is 1 (`onehot_at` below). -/
theorem onehot_sum_eq_one (N : Nat) (hN : N < P)
    (hb : ∀ i, i < N → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1)
    (h1 : (onehotAux N).eval rw = 1) : selSumN rw N = 1 := by
  rw [onehotAux_eq_selSumF] at h1
  have h := selSumF_toNat rw N hN hb
  rw [h1] at h
  rw [show ZkFormal.Algebra.Fp.toNat (1 : F) = 1 from rfl] at h
  exact h.symm

theorem eq_zero_of_sum_zero : ∀ N, selSumN rw N = 0 →
    ∀ i, i < N → (rw.cur (selE i)).toNat = 0 := by
  intro N
  induction N with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    have hn : selSumN rw (n + 1) = selSumN rw n + (rw.cur (selE n)).toNat := rfl
    rw [hn] at h
    rcases Nat.lt_or_eq_of_le (show i ≤ n from by omega) with h' | h'
    · exact ih (by omega) i h'
    · rw [h']; omega

/-- **Exactly one selector bit is 1** (and it is at the index the sum picks out). -/
theorem onehot_at (N : Nat) (hN : N < P)
    (hb : ∀ i, i < N → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1)
    (h1 : (onehotAux N).eval rw = 1) :
    ∃ r, r < N ∧ rw.cur (selE r) = 1 ∧ ∀ i, i < N → i ≠ r → rw.cur (selE i) = 0 := by
  have hsum := onehot_sum_eq_one rw N hN hb h1
  have habs : ∀ i, i < N → (rw.cur (selE i)).toNat = 0 ∨ (rw.cur (selE i)).toNat = 1 :=
    fun i hi => bit_toNat (hb i hi)
  have habs' : ∀ i ∈ List.range N, (rw.cur (selE i)).toNat = 0 ∨ (rw.cur (selE i)).toNat = 1 := by
    intro i hi; exact habs i (by simpa using hi)
  have hmap : ((List.range N).map (fun i => (rw.cur (selE i)).toNat)).sum = 1 := by
    rw [← selSumN_eq_map_sum]; exact hsum
  obtain ⟨r, hr, hbr, hzero⟩ := sum_eq_one_bits N (fun i => (rw.cur (selE i)).toNat) habs' hmap
  refine ⟨r, hr, ?_, ?_⟩
  · exact WasmBase.eq_of_toNat hbr
  · intro i hi hne
    have h0 : (rw.cur (selE i)).toNat = 0 := hzero i hi hne
    exact WasmBase.eq_of_toNat h0

theorem rcSelAux_zero (k : Nat) :
    ∀ N, (∀ i, i < N → rw.cur (selE i) = 0) → (rcSelAux k N).eval rw = 0 := by
  intro N
  induction N with
  | zero => intro _; show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    intro h
    show (Expr.eval rw (rcSelAux k n) + Expr.eval rw (v (selE n) * Expr.c (rcBit n k))) = 0
    rw [ih (fun i hi => h i (by omega))]
    rw [show Expr.eval rw (v (selE n) * Expr.c (rcBit n k)) =
        rw.cur (selE n) * ((rcBit n k : Nat) : F) from by
      show Expr.eval rw (v (selE n)) * Expr.eval rw (Expr.c (rcBit n k)) = _
      rw [show (v (selE n)).eval rw = rw.cur (selE n) from rfl,
        show (Expr.c (rcBit n k)).eval rw = ((rcBit n k : Nat) : F) from rfl]]
    rw [h n (by omega), zero_mul_f, add_zero_f]

theorem rcSelAux_at (k : Nat) :
    ∀ N r, r < N → rw.cur (selE r) = 1 →
      (∀ i, i < N → i ≠ r → rw.cur (selE i) = 0) →
      (rcSelAux k N).eval rw = ((rcBit r k : Nat) : F) := by
  intro N
  induction N with
  | zero => intro r hr _ _; omega
  | succ n ih =>
    intro r hr h1 h0
    show (Expr.eval rw (rcSelAux k n) + Expr.eval rw (v (selE n) * Expr.c (rcBit n k))) = _
    rw [show Expr.eval rw (v (selE n) * Expr.c (rcBit n k)) =
        rw.cur (selE n) * ((rcBit n k : Nat) : F) from by
      show Expr.eval rw (v (selE n)) * Expr.eval rw (Expr.c (rcBit n k)) = _
      rw [show (v (selE n)).eval rw = rw.cur (selE n) from rfl,
        show (Expr.c (rcBit n k)).eval rw = ((rcBit n k : Nat) : F) from rfl]]
    rcases Nat.lt_or_eq_of_le (show r ≤ n from by omega) with h' | h'
    · rw [h0 n (by omega) (by omega), zero_mul_f, add_zero_f]
      exact ih r h' h1 (fun i hi hne => h0 i (by omega) hne)
    · have hrn : r = n := h'
      rw [show rw.cur (selE n) = 1 from by rw [← hrn]; exact h1]
      rw [show (Expr.eval rw (rcSelAux k n)) = 0 from
        rcSelAux_zero rw k n (fun i hi => h0 i (by omega) (by omega))]
      rw [show ((rcBit n k : Nat) : F) = ((rcBit r k : Nat) : F) from by rw [hrn]]
      rw [one_mul_f, zero_add_f]

/-- **`iota`'s constant selection.**  If the one-hot `sel` picks index `r`, then the round's `rcSel`
expression evaluates to the spec's `rc[r]` bit `k` — as an exact numeral identity, since `rcBit r k`
is `0` or `1`. -/
theorem iota_const (k : Nat)
    (hb : ∀ i, i < ROUNDS → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1)
    (h1 : (onehotAux ROUNDS).eval rw = 1) :
    ∃ r, r < ROUNDS ∧ (rcSel k).eval rw = ((rcBit r k : Nat) : F) := by
  obtain ⟨r, hr, hsel, hzero⟩ := onehot_at rw ROUNDS (by decide) hb h1
  refine ⟨r, hr, ?_⟩
  show (rcSelAux k ROUNDS).eval rw = _
  exact rcSelAux_at rw k ROUNDS r hr hsel hzero

/-! ## `rho`/`pi`: the static index facts -/

/-- `piTgt` is injective on `0..24` (so `piSrc` is well defined and `bBit` reads each `T` bit once). -/
theorem piTgt_inj : ∀ a ∈ List.range L, ∀ b ∈ List.range L, piTgt a = piTgt b → a = b := by
  decide

/-- `piSrc` inverts the spec's `piTgt` on the 25 lanes. -/
theorem piTgt_piSrc : ∀ m ∈ List.range L, piTgt (piSrc m) = m := by
  decide

/-- `piSrc` maps the 25 lanes onto the 25 lanes (a permutation). -/
theorem piSrc_mem : ∀ m ∈ List.range L, piSrc m ∈ List.range L := by
  decide

/-- The rho offsets are all `< 64`, so `bBit`'s index arithmetic stays in range. -/
theorem rotc_lt : ∀ s ∈ List.range L, rotcVal s < W := by
  decide

/-- `chi`'s input lanes are in the same slice: `chi1 m` and `chi2 m` have `m`'s lane `m / 5`. -/
theorem chi1_div (m : Nat) (hm : m ∈ List.range L) : chi1 m / 5 = m / 5 := by
  simp only [chi1, List.mem_range, L] at hm ⊢
  omega

theorem chi2_div (m : Nat) (hm : m ∈ List.range L) : chi2 m / 5 = m / 5 := by
  simp only [chi2, List.mem_range, L] at hm ⊢
  omega

/-- The `chi` input lanes are distinct lanes `0..24`. -/
theorem chi1_mem (m : Nat) (hm : m ∈ List.range L) : chi1 m ∈ List.range L := by
  simp only [chi1, List.mem_range, L] at hm ⊢
  omega

theorem chi2_mem (m : Nat) (hm : m ∈ List.range L) : chi2 m ∈ List.range L := by
  simp only [chi2, List.mem_range, L] at hm ⊢
  omega

/-- Every `bBit m j` is a `tBit` column: the rho/pi wiring never invents a column. -/
theorem bBit_is_tBit (m j : Nat) : ∃ l k, bBit m j = tBit l k :=
  ⟨piSrc m, _, rfl⟩

/-- The rotation index `(j + W − r) mod W` written out: it is `j − r` when `j ≥ r`, and `j + W − r`
(a plain `Nat`) when `j < r`.  So it is injective in `j`. -/
theorem rot_form (r j : Nat) (hr : r < W) (hj : j < W) :
    (j + W - r) % W = if j < r then j + W - r else j - r := by
  by_cases h : j < r
  · rw [if_pos h]
    have hlt : j + W - r < W := by omega
    exact Nat.mod_eq_of_lt hlt
  · rw [if_neg h]
    have e : j + W - r = W + (j - r) := by omega
    rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- **The rotation index is injective.**  Both branches of `rot_form` are strictly increasing in `j`
on `[0, W)`: the "wrap" branch lands in `[1, r)` and the other in `[0, W − r)`, and they do not
overlap. -/
theorem rot_index (r j j' : Nat) (hr : r < W) (hj : j < W) (hj' : j' < W)
    (h : (j + W - r) % W = (j' + W - r) % W) : j = j' := by
  rw [rot_form r j hr hj, rot_form r j' hr hj'] at h
  by_cases h1 : j < r <;> by_cases h2 : j' < r
  · rw [if_pos h1, if_pos h2] at h; omega
  · rw [if_pos h1, if_neg h2] at h; omega
  · rw [if_neg h1, if_pos h2] at h; omega
  · rw [if_neg h1, if_neg h2] at h; omega

/-- Splitting a lane-bit index `W·l + k` (`k < W`) is unique. -/
theorem lane_bit_split (l1 k1 l2 k2 : Nat) (hk1 : k1 < W) (hk2 : k2 < W)
    (h : W * l1 + k1 = W * l2 + k2) : l1 = l2 ∧ k1 = k2 := by
  have h1 : (W * l1 + k1) / W = l1 := by
    rw [Nat.mul_add_div (by decide : 0 < W), Nat.div_eq_of_lt hk1, Nat.add_zero]
  have h2 : (W * l2 + k2) / W = l2 := by
    rw [Nat.mul_add_div (by decide : 0 < W), Nat.div_eq_of_lt hk2, Nat.add_zero]
  have hl : l1 = l2 := by rw [← h1, ← h2, h]
  subst hl
  omega

/-- **`rho`/`pi` is a bijection on columns**: distinct `(m, j)` pairs read distinct `T` bits, so the
round's 1,600 `T` columns are consumed exactly once. -/
theorem bBit_inj {m j m' j' : Nat} (hm : m < L) (hj : j < W) (hm' : m' < L) (hj' : j' < W)
    (h : bBit m j = bBit m' j') : m = m' ∧ j = j' := by
  have hk1 : (j + W - rotcVal (piSrc m)) % W < W := Nat.mod_lt _ (by decide)
  have hk2 : (j' + W - rotcVal (piSrc m')) % W < W := Nat.mod_lt _ (by decide)
  simp only [bBit, tBit] at h
  have h' : W * piSrc m + (j + W - rotcVal (piSrc m)) % W =
      W * piSrc m' + (j' + W - rotcVal (piSrc m')) % W := by omega
  have hsplit := lane_bit_split (piSrc m) ((j + W - rotcVal (piSrc m)) % W)
    (piSrc m') ((j' + W - rotcVal (piSrc m')) % W) hk1 hk2 h'
  have hs : piSrc m = piSrc m' := hsplit.1
  have hmm : m = m' := by
    have hm1 : piTgt (piSrc m) = m := piTgt_piSrc m (List.mem_range.2 hm)
    have hm2 : piTgt (piSrc m') = m' := piTgt_piSrc m' (List.mem_range.2 hm')
    rw [← hm1, ← hm2, hs]
  refine ⟨hmm, ?_⟩
  rw [hs] at hsplit
  exact rot_index (rotcVal (piSrc m')) j j'
    (rotc_lt (piSrc m') (piSrc_mem m' (List.mem_range.2 hm'))) hj hj' hsplit.2

end Keccak
end Chips
end WasmBase
