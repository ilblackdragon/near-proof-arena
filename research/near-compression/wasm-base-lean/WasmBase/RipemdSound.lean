import WasmBase.RipemdAir
import WasmBase.RipemdVectors
import WasmBase.Prelude
/-!
# WasmBase.RipemdSound — the round-agreement lemma for the RIPEMD-160 row

`WasmBase.RipemdAir` defines the row; `WasmBase.RipemdVectors` checks on concrete inputs that a
generated row satisfies every constraint and that the chained digest equals the spec's.  Neither
proves the general statement the soundness argument needs:

> a row that satisfies the table's constraints **is** one step of `NearSpecV3.Wasm.Crypto.ripemd160`.

That is the `M3` analogue the README names as a gap.  This file proves it in stages, each stage a
lemma about `Expr.eval` on a `Row` and its `toNat` image:

1. **`bits_*`** — the field plumbing: booleanity gives `{0,1}`, and the degree-2/3/4 builders
   (`xor2`, `xor3`, `majE`, `chE`, `orE`, `notE`) evaluated on bits equal their integer formulas.
2. **`sel_*`** — the selector collapses.  `selConstraints` says `Σ_j sel_j = 1` and every `sel_j` is
   a bit; `sel_unique` turns that into "exactly one `j₀` has `sel_j₀ = 1`", and the group sums
   `gselAux g 16` then vanish except on `j₀`'s group.  Everything row-dependent (`f`, `xL`, `xR`,
   `rot`, `kL`, `kR`) is a `sel`-gated sum, so each collapses to its value at `j₀`.
3. **`adder_*`** — the ripple-carry adder.  `addSum`/`addCarry` at each bit are exactly the full
   adder's sum and carry; `ofBits_add32_top` composes the 32 bits into
   `ofBits t = (ofBits x + ofBits y) % 2³²`.
4. **`round_agrees`** — the assembly: the ten next-row words are the spec's step at `j₀`.

Everything is stated on naturals (`Row.cur i` is an `Fp`; `toNat` of a bit is the bit) — the same
style as `KeccakSteps`, so the composition reads as the spec's own arithmetic.
-/
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace WasmBase
namespace Chips
namespace Ripemd

open ZkFormal.Algebra

/-! ## 1. Evaluation plumbing -/

theorem e0_eval (rw : Row) : e0.eval rw = 0 := by
  show ((Expr.c 0).eval rw) = (0 : F); rw [Expr.eval_c]; decide
theorem e1_eval (rw : Row) : e1.eval rw = 1 := by
  show ((Expr.c 1).eval rw) = (1 : F); rw [Expr.eval_c]; decide
theorem e2_eval (rw : Row) : e2.eval rw = 2 := by
  show ((Expr.c 2).eval rw) = (2 : F); rw [Expr.eval_c]; decide
theorem e4_eval (rw : Row) : e4.eval rw = 4 := by
  show ((Expr.c 4).eval rw) = (4 : F); rw [Expr.eval_c]; decide

theorem eval_boolE (rw : Row) (e : Expr) :
    (boolE e).eval rw = e.eval rw * (e.eval rw - 1) := by
  simp only [boolE, Expr.eval_mul', Expr.eval_sub', e1_eval]

theorem eval_xor2 (rw : Row) (a b : Expr) :
    (xor2 a b).eval rw = a.eval rw + b.eval rw - 2 * (a.eval rw * b.eval rw) := by
  simp only [xor2, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', e2_eval]

theorem eval_xor3 (rw : Row) (a b c : Expr) :
    (xor3 a b c).eval rw = a.eval rw + b.eval rw + c.eval rw
      - 2 * (a.eval rw * b.eval rw + a.eval rw * c.eval rw + b.eval rw * c.eval rw)
      + 4 * (a.eval rw * b.eval rw * c.eval rw) := by
  simp only [xor3, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', e2_eval, e4_eval]

theorem eval_majE (rw : Row) (a b c : Expr) :
    (majE a b c).eval rw = a.eval rw * b.eval rw + a.eval rw * c.eval rw + b.eval rw * c.eval rw
      - 2 * (a.eval rw * b.eval rw * c.eval rw) := by
  simp only [majE, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', e2_eval]

theorem eval_orE (rw : Row) (a b : Expr) :
    (orE a b).eval rw = a.eval rw + b.eval rw - a.eval rw * b.eval rw := by
  simp only [orE, Expr.eval_sub', Expr.eval_add', Expr.eval_mul']

theorem eval_notE (rw : Row) (a : Expr) : (notE a).eval rw = 1 - a.eval rw := by
  simp only [notE, Expr.eval_sub', e1_eval]

theorem eval_chE (rw : Row) (a b c : Expr) :
    (chE a b c).eval rw = a.eval rw * b.eval rw + (1 - a.eval rw) * c.eval rw := by
  simp only [chE, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', e1_eval]

theorem eval_andE (rw : Row) (a b : Expr) : (andE a b).eval rw = a.eval rw * b.eval rw := by
  simp only [andE, Expr.eval_mul']

/-- A booleanity constraint `e·(e−1) = 0` puts `e` in `{0,1}`. -/
theorem bit_cases {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := WasmBase.bool_cases h

theorem bit_toNat {x : F} (h : x = 0 ∨ x = 1) : x.toNat = 0 ∨ x.toNat = 1 := by
  rcases h with h | h
  · exact Or.inl (WasmBase.toNat_of_eq_zero h)
  · exact Or.inr (WasmBase.toNat_of_eq_one h)

/-- `toNat` of a bit is below 2. -/
theorem bit_toNat_val {x : F} (h : x = 0 ∨ x = 1) : x.toNat < 2 := by
  rcases bit_toNat h with h | h <;> omega

/-- **Three-way XOR on `toNat`**: the degree-4 builder on bits is `(a+b+c) % 2`. -/
theorem xor3_toNat {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    (a + b + c - 2 * (a * b + a * c + b * c) + 4 * (a * b * c)).toNat
      = (a.toNat + b.toNat + c.toNat) % 2 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> rcases hc with h'' | h'' <;>
    rw [h, h', h''] <;> decide

/-- **Majority on `toNat`**: the degree-3 builder on bits is the adder's carry. -/
theorem majE_toNat {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    (a * b + a * c + b * c - 2 * (a * b * c)).toNat = (a.toNat + b.toNat + c.toNat) / 2 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> rcases hc with h'' | h'' <;>
    rw [h, h', h''] <;> decide

/-! ## 2. The selector collapses

`selConstraints` is the single equation `Σ_{j<80} sel_j − 1 = 0`, and `boolFams` makes every `sel_j`
a bit.  Together: exactly one `j₀ < 80` has `sel_{j₀} = 1`, all the others are `0`.  Every
row-dependent quantity is a `sel`-gated sum, so it collapses to its value at `j₀`:

* `gselAux g 16` — the group's selector sum, `1` on `j₀`'s group and `0` on the other four.
* `kSelAux b k 80` — the group constant, `kl[j₀/16]_k` or `kr[j₀/16]_k`.
* `xselAux`, `rotAux`, `fSumAux` — the same shape (stages 3 and 4).

The machinery is the same as `WasmBase.KeccakSteps`'s `rcSelAux_*`: an induction over the sum's length,
with the one nonzero term handled last. -/

theorem zero_add_f (a : F) : (0 : F) + a = a := by grind
theorem add_zero_f (a : F) : a + (0 : F) = a := by grind
theorem one_mul_f (a : F) : (1 : F) * a = a := by grind
theorem zero_mul_f (a : F) : (0 : F) * a = 0 := by grind

def selSumF (rw : Row) : Nat → F
  | 0 => 0
  | n + 1 => selSumF rw n + rw.cur (selE n)

def selSumN (rw : Row) : Nat → Nat
  | 0 => 0
  | n + 1 => selSumN rw n + (rw.cur (selE n)).toNat

theorem onehotAux_eq_selSumF (rw : Row) (N : Nat) :
    (onehotAux N).eval rw = selSumF rw N := by
  induction N with
  | zero => show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    show (Expr.eval rw (onehotAux n) + Expr.eval rw (v (selE n))) = _
    rw [ih, show (v (selE n)).eval rw = rw.cur (selE n) from rfl]
    rfl

theorem selSumN_le (rw : Row) (N : Nat)
    (hb : ∀ i, i < N → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1) : selSumN rw N ≤ N := by
  induction N with
  | zero => simp [selSumN]
  | succ n ih =>
    have := ih (fun i hi => hb i (by omega))
    have hn := bit_toNat (hb n (by omega))
    simp only [selSumN]
    omega

theorem selSumF_toNat (rw : Row) :
    ∀ N, N < P → (∀ i, i < N → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1) →
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

theorem selSumN_eq_map_sum (rw : Row) : ∀ N, selSumN rw N =
    ((List.range N).map (fun i => (rw.cur (selE i)).toNat)).sum := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show selSumN rw n + (rw.cur (selE n)).toNat = _
    rw [ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]

/-- **The one-hot sum is exactly 1**: bits summing to `1` in `Fp` sum to `1` in `Nat`. -/
theorem onehot_sum_eq_one (rw : Row) (N : Nat) (hN : N < P)
    (hb : ∀ i, i < N → rw.cur (selE i) = 0 ∨ rw.cur (selE i) = 1)
    (h1 : (onehotAux N).eval rw = 1) : selSumN rw N = 1 := by
  rw [onehotAux_eq_selSumF] at h1
  have h := selSumF_toNat rw N hN hb
  rw [h1] at h
  rw [show ZkFormal.Algebra.Fp.toNat (1 : F) = 1 from rfl] at h
  exact h.symm

/-- **Exactly one selector bit is 1.** -/
theorem onehot_at (rw : Row) (N : Nat) (hN : N < P)
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

/-! ### The group selector sum `gselAux g 16` -/

theorem gselAux_zero (rw : Row) (g : Nat) :
    ∀ N, (∀ n, n < N → rw.cur (selE (16 * g + n)) = 0) → (gselAux g N).eval rw = 0 := by
  intro N
  induction N with
  | zero => intro _; show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    intro h
    show (Expr.eval rw (gselAux g n) + Expr.eval rw (v (selE (16 * g + n)))) = 0
    rw [ih (fun i hi => h i (by omega))]
    rw [show Expr.eval rw (v (selE (16 * g + n))) = rw.cur (selE (16 * g + n)) from rfl]
    rw [h n (by omega), add_zero_f]

/-- **`gselAux g 16` is 1 exactly on the group containing the one-hot index.** -/
theorem gselAux_at (rw : Row) (g : Nat) :
    ∀ N n0, n0 < N → rw.cur (selE (16 * g + n0)) = 1 →
      (∀ n, n < N → n ≠ n0 → rw.cur (selE (16 * g + n)) = 0) →
      (gselAux g N).eval rw = 1 := by
  intro N
  induction N with
  | zero => intro n0 hn0 _ _; omega
  | succ n ih =>
    intro n0 hn0 h1 h0
    show (Expr.eval rw (gselAux g n) + Expr.eval rw (v (selE (16 * g + n)))) = 1
    rcases Nat.lt_or_eq_of_le (show n0 ≤ n from by omega) with h' | h'
    · rw [show Expr.eval rw (v (selE (16 * g + n))) = rw.cur (selE (16 * g + n)) from rfl]
      rw [h0 n (by omega) (by omega), add_zero_f]
      exact ih n0 h' h1 (fun i hi hne => h0 i (by omega) hne)
    · have hrn : n0 = n := h'
      subst hrn
      rw [show Expr.eval rw (v (selE (16 * g + n0))) = rw.cur (selE (16 * g + n0)) from rfl]
      rw [show Expr.eval rw (gselAux g n0) = 0 from
        gselAux_zero rw g n0 (fun i hi => h0 i (by omega) (by omega))]
      rw [h1, zero_add_f]

/-! ### The group constant `kSelB b k` -/

theorem kSelAux_zero (rw : Row) (b k : Nat) :
    ∀ N, (∀ j, j < N → rw.cur (selE j) = 0) → (kSelAux b k N).eval rw = 0 := by
  intro N
  induction N with
  | zero => intro _; show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    intro h
    show (Expr.eval rw (kSelAux b k n) +
      Expr.eval rw (v (selE n) * Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k))) = 0
    rw [ih (fun i hi => h i (by omega))]
    rw [show Expr.eval rw (v (selE n) * Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k)) =
        rw.cur (selE n) * ((if b = 0 then klBit (n / 16) k else krBit (n / 16) k : Nat) : F) from by
      show Expr.eval rw (v (selE n)) * Expr.eval rw (Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k)) = _
      rw [show (v (selE n)).eval rw = rw.cur (selE n) from rfl,
        show (Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k)).eval rw =
          ((if b = 0 then klBit (n / 16) k else krBit (n / 16) k : Nat) : F) from rfl]]
    rw [h n (by omega), zero_mul_f, add_zero_f]

/-- **The group constant collapses to `kl[j₀/16]` / `kr[j₀/16]`.** -/
theorem kSelAux_at (rw : Row) (b k : Nat) :
    ∀ N j0, j0 < N → rw.cur (selE j0) = 1 →
      (∀ j, j < N → j ≠ j0 → rw.cur (selE j) = 0) →
      (kSelAux b k N).eval rw =
        ((if b = 0 then klBit (j0 / 16) k else krBit (j0 / 16) k : Nat) : F) := by
  intro N
  induction N with
  | zero => intro j0 hj0 _ _; omega
  | succ n ih =>
    intro j0 hj0 h1 h0
    show (Expr.eval rw (kSelAux b k n) +
      Expr.eval rw (v (selE n) * Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k))) = _
    rw [show Expr.eval rw (v (selE n) * Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k)) =
        rw.cur (selE n) * ((if b = 0 then klBit (n / 16) k else krBit (n / 16) k : Nat) : F) from by
      show Expr.eval rw (v (selE n)) * Expr.eval rw (Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k)) = _
      rw [show (v (selE n)).eval rw = rw.cur (selE n) from rfl,
        show (Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k)).eval rw =
          ((if b = 0 then klBit (n / 16) k else krBit (n / 16) k : Nat) : F) from rfl]]
    rcases Nat.lt_or_eq_of_le (show j0 ≤ n from by omega) with h' | h'
    · rw [h0 n (by omega) (by omega), zero_mul_f, add_zero_f]
      exact ih j0 h' h1 (fun i hi hne => h0 i (by omega) hne)
    · have hrn : j0 = n := h'
      rw [hrn]
      rw [show rw.cur (selE n) = 1 from (hrn ▸ h1 : rw.cur (selE n) = 1)]
      rw [show Expr.eval rw (kSelAux b k n) = 0 from
        kSelAux_zero rw b k n (fun i hi => h0 i (by omega) (by omega))]
      rw [one_mul_f, zero_add_f]

/-- In `F_p`, `x − y = 0` implies `x = y`.  Same argument as `WasmBase.Chips.Keccak.nat_sub_zero`
(the source is in a namespace this file does not import, so the pair is restated here). -/
theorem nat_sub_zero' {a b : Nat} (ha : a < P) (hb : b < P) (h : (a + (P - b)) % P = 0) : a = b := by
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

theorem sub_eq_zero' {a b : F} (h : a - b = 0) : a = b := by
  have hsub : Fp.sub a b = 0 := h
  have h1 : (a.toNat + (P - b.toNat)) % P = 0 := by
    have := congrArg Fp.toNat hsub
    rw [Fp.toNat_sub, Fp.toNat_zero] at this
    simpa using this
  exact Fp.ext (nat_sub_zero' (Fp.toNat_lt a) (Fp.toNat_lt b) h1)

/-! ## 3. The adder chain

Each of the eight additions is a full adder per bit: the sum column `t_k` is `x_k ⊕ y_k ⊕ cyIn_k` and
the carry column `cy_k` is `maj(x_k, y_k, cyIn_k)`, with carry-in zero at bit 0.  The table carries
only 31 carry columns per addition (bit 31's carry is dropped — mod 2³²), so bit 31's sum is the last
constrained one.

`fa_step` turns one row's sum/carry pair into the integer full-adder identity
`x_k + y_k + c_k = t_k + 2·c_{k+1}`, and `ofBits_add32_top` composes 32 of them into
`ofBits t 32 = (ofBits x 32 + ofBits y 32) % 2³²`. -/

/-- Little-endian value of `n` bits. -/
def ofBitsN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ofBitsN f n + 2 ^ n * f n

theorem ofBitsN_succ (f : Nat → Nat) (n : Nat) :
    ofBitsN f (n + 1) = ofBitsN f n + 2 ^ n * f n := rfl

theorem ofBitsN_lt {f : Nat → Nat} :
    ∀ n, (∀ b, b < n → f b ≤ 1) → ofBitsN f n < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp [ofBitsN]
  | succ k ih =>
    intro h
    have hk : ∀ b, b < k → f b ≤ 1 := fun b hb => h b (by omega)
    have h1 := ih hk
    have h2 := h k (by omega)
    have hmul : 2 ^ k * f k ≤ 2 ^ k * 1 := Nat.mul_le_mul_left _ h2
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    rw [ofBitsN_succ, hp]
    omega

/-- Prefix invariant: the row's carry sequence `c` (with a carry for every bit `0..32`) satisfies
`ofBits t n + 2ⁿ·c n = ofBits x n + ofBits y n`. -/
theorem ofBits_ripple (x y t c : Nat → Nat) (hc0 : c 0 = 0)
    (hstep : ∀ k, k < 32 → x k + y k + c k = t k + 2 * c (k + 1)) :
    ∀ n, n ≤ 32 → ofBitsN t n + 2 ^ n * c n = ofBitsN x n + ofBitsN y n := by
  intro n
  induction n with
  | zero => intro _; simp [ofBitsN, hc0]
  | succ k ih =>
    intro hk
    have hk' : k ≤ 32 := by omega
    have hI := ih hk'
    have hs := hstep k (by omega)
    rw [ofBitsN_succ, ofBitsN_succ, ofBitsN_succ, Nat.pow_succ]
    grind

/-- **Adder correctness** (full carry chain): the row's sum bits `t` are the low 32 bits of `x + y`. -/
theorem ofBits_add32 (x y t c : Nat → Nat)
    (ht : ∀ k, k < 32 → t k ≤ 1)
    (hc0 : c 0 = 0)
    (hstep : ∀ k, k < 32 → x k + y k + c k = t k + 2 * c (k + 1)) :
    ofBitsN t 32 = (ofBitsN x 32 + ofBitsN y 32) % 2 ^ 32 := by
  have hinv := ofBits_ripple x y t c hc0 hstep 32 (by omega)
  have hlt := ofBitsN_lt (f := t) 32 ht
  have hmod : (ofBitsN x 32 + ofBitsN y 32) % 2 ^ 32 = ofBitsN t 32 := by
    conv => lhs; rw [← hinv]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  exact hmod.symm

/-- **Adder correctness in the table's shape.**  The table constrains carries only for bits `0..30`
(`cy` has 31 columns per addition), so bit 31's carry is supplied as an explicit top carry `ctop`. -/
theorem ofBits_add32_top (x y t c : Nat → Nat) (ctop : Nat)
    (ht : ∀ k, k < 32 → t k ≤ 1)
    (hc0 : c 0 = 0)
    (hstep : ∀ k, k < 31 → x k + y k + c k = t k + 2 * c (k + 1))
    (hlast : x 31 + y 31 + c 31 = t 31 + 2 * ctop) :
    ofBitsN t 32 = (ofBitsN x 32 + ofBitsN y 32) % 2 ^ 32 := by
  refine ofBits_add32 x y t (fun n => if n = 32 then ctop else c n) ht ?_ ?_
  · show (if 0 = 32 then ctop else c 0) = 0
    rw [if_neg (by omega)]; exact hc0
  · intro k hk
    by_cases h32 : k + 1 = 32
    · have hk31 : k = 31 := by omega
      subst hk31
      rw [if_neg (by omega : ¬ (31 : Nat) = 32), if_pos rfl]
      exact hlast
    · rw [if_neg (by omega : ¬ k = 32), if_neg h32]
      exact hstep k (by omega)

/-! ### From the row's constraints to the full-adder identity -/

/-- **One full-adder step.**  The row's sum and carry constraints at bit `k < 31` give the integer
identity `x_k + y_k + cyIn_k = t_k + 2·cy_k`.  The two equations are the field equations
`xor3 x y cyIn = t_k` and `majE x y cyIn = cy_k`; on bits, `xor3_toNat`/`majE_toNat` read them as
`(x+y+cy) % 2 = t_k` and `(x+y+cy) / 2 = cy_k`, whose sum is `x+y+cy` again. -/
theorem fa_step (rw : Row) (n k : Nat) (xe ye : Expr)
    (hxb : (xe.eval rw) = 0 ∨ (xe.eval rw) = 1)
    (hyb : (ye.eval rw) = 0 ∨ (ye.eval rw) = 1)
    (hcb : (cyIn n k).eval rw = 0 ∨ (cyIn n k).eval rw = 1)
    (htb : rw.cur (tBit n k) = 0 ∨ rw.cur (tBit n k) = 1)
    (hcyb : rw.cur (cyBit n k) = 0 ∨ rw.cur (cyBit n k) = 1)
    (hsum : (addSum n k xe ye).eval rw = 0)
    (hcar : (addCarry n k xe ye).eval rw = 0) :
    (xe.eval rw).toNat + (ye.eval rw).toNat + ((cyIn n k).eval rw).toNat
      = (rw.cur (tBit n k)).toNat + 2 * (rw.cur (cyBit n k)).toNat := by
  -- the sum equation, as an `F` identity
  have h1 : (xor3 xe ye (cyIn n k)).eval rw = rw.cur (tBit n k) := by
    have h := hsum
    rw [addSum] at h
    exact sub_eq_zero' h
  -- the carry equation, as an `F` identity
  have h2 : (majE xe ye (cyIn n k)).eval rw = rw.cur (cyBit n k) := by
    have h := hcar
    rw [addCarry] at h
    exact sub_eq_zero' h
  -- read both through `toNat`
  have hx3 : ((xor3 xe ye (cyIn n k)).eval rw).toNat =
      ((xe.eval rw).toNat + (ye.eval rw).toNat + ((cyIn n k).eval rw).toNat) % 2 := by
    rw [eval_xor3]; exact xor3_toNat hxb hyb hcb
  have hmaj : ((majE xe ye (cyIn n k)).eval rw).toNat =
      ((xe.eval rw).toNat + (ye.eval rw).toNat + ((cyIn n k).eval rw).toNat) / 2 := by
    rw [eval_majE]; exact majE_toNat hxb hyb hcb
  have ht' : (rw.cur (tBit n k)).toNat =
      ((xe.eval rw).toNat + (ye.eval rw).toNat + ((cyIn n k).eval rw).toNat) % 2 := by
    rw [← h1]; exact hx3
  have hcy' : (rw.cur (cyBit n k)).toNat =
      ((xe.eval rw).toNat + (ye.eval rw).toNat + ((cyIn n k).eval rw).toNat) / 2 := by
    rw [← h2]; exact hmaj
  rw [ht', hcy']
  omega

/-! ### The row's carry sequence, and the adder correctness theorem -/

/-- `cyIn n k` on a row is a bit: `0` at bit 0, else the previous carry column. -/
theorem cyIn_bit (rw : Row) (n k : Nat) (hk : k < 32)
    (hcyb : ∀ k, k < 31 → rw.cur (cyBit n k) = 0 ∨ rw.cur (cyBit n k) = 1) :
    (cyIn n k).eval rw = 0 ∨ (cyIn n k).eval rw = 1 := by
  unfold cyIn
  by_cases h : k = 0
  · subst h; rw [if_pos rfl]; exact Or.inl (e0_eval rw)
  · rw [if_neg h]
    exact hcyb (k - 1) (by omega)

/-- **One addition's correctness.**  The row's sum constraints at all 32 bits and the carry
constraints at bits `0..30` say the sum column word is the low 32 bits of the two operand words:
`ofBits t 32 = (ofBits x 32 + ofBits y 32) % 2³²`.  The carry sequence is the row's own `cy` columns,
continued past the table's last carry column by the dropped top carry. -/
theorem adder_chain (rw : Row) (n : Nat) (xe ye : Nat → Expr)
    (hxb : ∀ k, k < 32 → (xe k).eval rw = 0 ∨ (xe k).eval rw = 1)
    (hyb : ∀ k, k < 32 → (ye k).eval rw = 0 ∨ (ye k).eval rw = 1)
    (htb : ∀ k, k < 32 → rw.cur (tBit n k) = 0 ∨ rw.cur (tBit n k) = 1)
    (hcyb : ∀ k, k < 31 → rw.cur (cyBit n k) = 0 ∨ rw.cur (cyBit n k) = 1)
    (hsum : ∀ k, k < 32 → (addSum n k (xe k) (ye k)).eval rw = 0)
    (hcar : ∀ k, k < 31 → (addCarry n k (xe k) (ye k)).eval rw = 0) :
    ofBitsN (fun k => (rw.cur (tBit n k)).toNat) 32
      = (ofBitsN (fun k => (xe k).eval rw |>.toNat) 32
         + ofBitsN (fun k => (ye k).eval rw |>.toNat) 32) % 2 ^ 32 := by
  refine ofBits_add32_top _ _ _ (fun k => ((cyIn n k).eval rw).toNat)
    ((((xe 31).eval rw).toNat + ((ye 31).eval rw).toNat
      + ((cyIn n 31).eval rw).toNat) / 2)
    (fun k hk => by have := bit_toNat_val (htb k hk); omega) ?_ ?_ ?_
  · -- carry into bit 0 is zero
    show ((cyIn n 0).eval rw).toNat = 0
    rw [show (cyIn n 0) = e0 from rfl, e0_eval]
    rfl
  · -- the full-adder step, for every constrained bit
    intro k hk
    exact fa_step rw n k (xe k) (ye k) (hxb k (by omega)) (hyb k (by omega))
      (cyIn_bit rw n k (by omega) hcyb) (htb k (by omega)) (hcyb k hk)
      (hsum k (by omega)) (hcar k hk)
  · -- bit 31's carry is the dropped top carry
    have hsum31 := hsum 31 (by omega)
    have h1 : (xor3 (xe 31) (ye 31) (cyIn n 31)).eval rw = rw.cur (tBit n 31) := by
      have h := hsum31
      rw [addSum] at h
      exact sub_eq_zero' h
    have hx3 : ((xor3 (xe 31) (ye 31) (cyIn n 31)).eval rw).toNat =
        (((xe 31).eval rw).toNat + ((ye 31).eval rw).toNat + ((cyIn n 31).eval rw).toNat) % 2 := by
      rw [eval_xor3]; exact xor3_toNat (hxb 31 (by omega)) (hyb 31 (by omega))
        (cyIn_bit rw n 31 (by omega) hcyb)
    have ht31 : (rw.cur (tBit n 31)).toNat =
        (((xe 31).eval rw).toNat + ((ye 31).eval rw).toNat + ((cyIn n 31).eval rw).toNat) % 2 := by
      rw [← h1]; exact hx3
    rw [ht31]
    have := Nat.div_add_mod (((xe 31).eval rw).toNat + ((ye 31).eval rw).toNat
      + ((cyIn n 31).eval rw).toNat) 2
    omega

end Ripemd
end Chips
end WasmBase
