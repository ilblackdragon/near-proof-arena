import ZkFormal.Sha.Sound.Bridge
import M5T1.Dsl

/-!
# M5T1.Ize — constraints over BabyBear as integer equations; carry chains

`ize e` evaluates a constraint expression over the integers, reading every column (and public
value, selector) as its canonical natural `< p`. `ize_mod`: `ev e ≡ ize e (mod p)`; so a constraint
that vanishes in the field and whose integer value is below `p` in absolute value is an exact
integer equation (`ize_eq_zero`).

`val f n = Σ_{k<n} 256^k · f k` and the carry-chain lemma `chain_val`: limb equations
`T k + carry_in = R k + 256 · carry_out` give `val T N = val R N + 256^N · top`.
-/

namespace M5T1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound

def PP : Nat := 2013265921

section
variable (tr : Trace Fp) (t r : Nat) (pub : List Fp)

/-- Integer value of an expression, every leaf read as its canonical natural. -/
def ize : Expr → Int
  | .const c => (c : Int)
  | .add a b => ize a + ize b
  | .mul a b => ize a * ize b
  | .neg a => - ize a
  | e => (ev tr t r pub e : Int)

/-- Column `i` of the row as a natural. -/
def cv (i : Nat) : Nat := ev tr t r pub (.col i false)
end

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem ize_mod (e : Expr) : ize tr t r pub e % (PP : Int) = (ev tr t r pub e : Int) := by
  induction e with
  | const c =>
    simp only [ize]; rw [ev_const]; unfold PP; omega
  | col i nx => simp only [ize]; have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (.col i nx); unfold PP; omega
  | pub i => simp only [ize]; have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (.pub i); unfold PP; omega
  | isFirst => simp only [ize]; have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) .isFirst; unfold PP; omega
  | isLast => simp only [ize]; have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) .isLast; unfold PP; omega
  | isTransition =>
    simp only [ize]; have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) .isTransition; unfold PP; omega
  | add a b iha ihb =>
    simp only [ize, ev_add]
    rw [Int.add_emod, iha, ihb]; unfold PP; omega
  | mul a b iha ihb =>
    simp only [ize, ev_mul]
    rw [Int.mul_emod, iha, ihb, Int.natCast_emod, Int.natCast_mul]; rfl
  | neg a iha =>
    simp only [ize, ev_neg]
    have h1 := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
    rw [Int.neg_emod, iha]
    unfold PP at *
    split <;> omega

theorem ize_eq_zero {e : Expr} (h : ev tr t r pub e = 0) (h1 : -(PP : Int) < ize tr t r pub e)
    (h2 : ize tr t r pub e < PP) : ize tr t r pub e = 0 := by
  have hm := ize_mod (tr := tr) (t := t) (r := r) (pub := pub) e
  rw [h] at hm
  unfold PP at *
  omega

@[simp] theorem ize_hadd (a b : Expr) : ize tr t r pub (a + b) = ize tr t r pub a + ize tr t r pub b := rfl
@[simp] theorem ize_hmul (a b : Expr) : ize tr t r pub (a * b) = ize tr t r pub a * ize tr t r pub b := rfl
@[simp] theorem ize_hsub (a b : Expr) : ize tr t r pub (a - b) = ize tr t r pub a - ize tr t r pub b := by
  show ize tr t r pub (.add a (.neg b)) = _; simp only [ize]; omega
@[simp] theorem ize_const (c : Nat) : ize tr t r pub (.const c) = c := rfl
@[simp] theorem ize_K (c : Nat) : ize tr t r pub (K c) = c := rfl
@[simp] theorem ize_ofNat (c : Nat) : ize tr t r pub (OfNat.ofNat c : Expr) = c := rfl
@[simp] theorem ize_col (i : Nat) : ize tr t r pub (.col i false) = (cv tr t r pub i : Int) := rfl

theorem ize_sumE : ∀ (es : List Expr), ize tr t r pub (sumE es) = (es.map (ize tr t r pub)).sum
  | [] => by simp [sumE]
  | [a] => by simp only [sumE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
  | a :: b :: rest => by
    have ih := ize_sumE (b :: rest)
    simp only [sumE] at ih ⊢
    simp only [ize, ih, List.map_cons, List.sum_cons]

/-- `x · (x − 1) = 0` in the field: `x ≤ 1`. -/
theorem bool_le {x : Expr} (h : ev tr t r pub (bool x) = 0) : ev tr t r pub x ≤ 1 := by
  change ev tr t r pub (Expr.mul x (Expr.add x (Expr.neg (Expr.const 1)))) = 0 at h
  have hx := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) x
  rcases ev_mul_eq_zero h with h | h
  · omega
  · simp only [ev_add, ev_neg, ev_const] at h
    omega

/-! ## Little-endian values and carry chains -/

def val (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => val f n + 256 ^ n * f n

theorem val_add (f g : Nat → Nat) (n : Nat) : val (fun k => f k + g k) n = val f n + val g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [val, ih, Nat.mul_add]; omega

theorem val_lt (f : Nat → Nat) (n : Nat) (h : ∀ k < n, f k < 256) : val f n < 256 ^ n := by
  induction n with
  | zero => simp [val]
  | succ n ih =>
    simp only [val]
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := h n (by omega)
    have : 256 ^ n * f n ≤ 256 ^ n * 255 := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.pow_succ]; omega

theorem val_congr (f g : Nat → Nat) (n : Nat) (h : ∀ k < n, f k = g k) : val f n = val g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [val, ih (fun k hk => h k (by omega)), h n (by omega)]

/-- **Carry chain.** -/
theorem chain_val (N : Nat) (T R C : Nat → Nat) (top : Nat) (hN : 0 < N)
    (h : ∀ k < N, T k + (if k = 0 then 0 else C (k - 1)) = R k + 256 * (if k + 1 = N then top else C k)) :
    val T N = val R N + 256 ^ N * top := by
  -- prefix invariant
  have key : ∀ n, n ≤ N → 0 < n →
      val T n = val R n + 256 ^ n * (if n = N then top else C (n - 1)) := by
    intro n hn hpos
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        have := h 0 hN
        simp only [val, Nat.pow_zero, Nat.one_mul, Nat.zero_add, ite_true] at this ⊢
        simp only [Nat.pow_one]
        split <;> simp_all <;> omega
      · have ih' := ih (by omega) h0
        have hk := h n (by omega)
        have hne : ¬ n = N := by omega
        simp only [hne, ite_false] at ih'
        have hn0 : ¬ n = 0 := by omega
        simp only [hn0, ite_false] at hk
        simp only [val, ih', Nat.pow_succ]
        by_cases hl : n + 1 = N
        · simp only [hl, ite_true] at hk ⊢
          have : 256 ^ n * (T n + C (n - 1)) = 256 ^ n * (R n + 256 * top) := by rw [hk]
          simp only [Nat.mul_add] at this
          rw [← Nat.mul_assoc] at this
          omega
        · simp only [hl, ite_false] at hk ⊢
          have : 256 ^ n * (T n + C (n - 1)) = 256 ^ n * (R n + 256 * C n) := by rw [hk]
          simp only [Nat.mul_add] at this
          rw [← Nat.mul_assoc] at this
          simp only [Nat.add_sub_cancel]
          omega
  have := key N (Nat.le_refl _) hN
  simpa using this

end M5T1
