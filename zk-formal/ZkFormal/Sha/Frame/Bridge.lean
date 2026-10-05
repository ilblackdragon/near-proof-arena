import ZkFormal.Sha.Statements

/-!
# ZkFormal.Sha.Frame.Bridge — evaluating framing constraints

Evaluation of the expression builders of ZkFormal.Sha.Table in field notation
(`+`, `*`, `-x`), so `grind` can reason with them over `Fp`, and bit sums as
`Fp.ofNat` of `View.ofBits`.
-/

namespace ZkFormal.Sha.Frame

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Layout ZkFormal.Sha.View
open ZkFormal.Sha.Table

section
variable (tr : Trace Fp) (t r : Nat) (pub : List Fp)

@[simp] theorem ev_c (x : Nat) : (E.c x).eval tr t r pub = tr.cell t r x := rfl
@[simp] theorem ev_n (x : Nat) :
    (E.n x).eval tr t r pub = tr.cell t ((r + 1) % tr.height t) x := rfl
@[simp] theorem ev_k (v : Nat) : (E.k v).eval tr t r pub = Fp.ofNat v := rfl
@[simp] theorem ev_const (v : Nat) : (Expr.const v).eval tr t r pub = Fp.ofNat v := rfl
@[simp] theorem ev_add (a b : Expr) :
    (Expr.add a b).eval tr t r pub = a.eval tr t r pub + b.eval tr t r pub := rfl
@[simp] theorem ev_mul (a b : Expr) :
    (Expr.mul a b).eval tr t r pub = a.eval tr t r pub * b.eval tr t r pub := rfl
@[simp] theorem ev_neg (a : Expr) : (Expr.neg a).eval tr t r pub = -(a.eval tr t r pub) := rfl
@[simp] theorem ev_sub (a b : Expr) :
    (E.sub a b).eval tr t r pub = a.eval tr t r pub + -(b.eval tr t r pub) := rfl
@[simp] theorem ev_not (a : Expr) :
    (E.not a).eval tr t r pub = Fp.ofNat 1 + -(a.eval tr t r pub) := rfl
@[simp] theorem ev_smul (v : Nat) (a : Expr) :
    (E.smul v a).eval tr t r pub = Fp.ofNat v * a.eval tr t r pub := rfl
@[simp] theorem ev_eqG (g a b : Expr) :
    (E.eqG g a b).eval tr t r pub = g.eval tr t r pub * (a.eval tr t r pub + -(b.eval tr t r pub)) := rfl
@[simp] theorem ev_isFirst : Expr.isFirst.eval tr t r pub = if r = 0 then 1 else 0 := rfl
theorem ev_sum_nil : (E.sum []).eval tr t r pub = Fp.ofNat 0 := rfl
theorem ev_sum_cons (e : Expr) (es : List Expr) :
    (E.sum (e :: es)).eval tr t r pub = e.eval tr t r pub + (E.sum es).eval tr t r pub := rfl
end

theorem ofNat_zero : Fp.ofNat 0 = 0 := rfl
theorem ofNat_one : Fp.ofNat 1 = 1 := rfl

theorem ofNat_add (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat, Fp.add_def, Fp.toNat_add]
  rw [← Nat.add_mod]

theorem ofNat_mul (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat, Fp.mul_def, Fp.toNat_mul]
  rw [Nat.mul_mod]

theorem ofNat_inj {a b : Nat} (ha : a < P) (hb : b < P) (h : Fp.ofNat a = Fp.ofNat b) : a = b := by
  have := congrArg Fp.toNat h
  simp only [Fp.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem cell_eq_ofNat (tr : Trace Fp) (t r c : Nat) : tr.cell t r c = Fp.ofNat (nv tr t r c) :=
  (Fp.ofNat_toNat _).symm

theorem P_val : P = 2013265921 := rfl

/-- A boolean cell. -/
theorem cell_bool {tr : Trace Fp} {t r c : Nat} (h : nv tr t r c ≤ 1) :
    tr.cell t r c = 0 ∨ tr.cell t r c = 1 := by
  rw [cell_eq_ofNat]
  rcases Nat.lt_or_ge (nv tr t r c) 1 with h1 | h1
  · left; rw [show nv tr t r c = 0 by omega]; rfl
  · right; rw [show nv tr t r c = 1 by omega]; rfl

theorem nv_of_cell_one {tr : Trace Fp} {t r c : Nat} (h : tr.cell t r c = 1) : nv tr t r c = 1 := by
  unfold nv; rw [h]; rfl

theorem nv_of_cell_zero {tr : Trace Fp} {t r c : Nat} (h : tr.cell t r c = 0) : nv tr t r c = 0 := by
  unfold nv; rw [h]; rfl

theorem cell_of_nv_one {tr : Trace Fp} {t r c : Nat} (h : nv tr t r c = 1) : tr.cell t r c = 1 := by
  rw [cell_eq_ofNat, h]; rfl

theorem cell_of_nv_zero {tr : Trace Fp} {t r c : Nat} (h : nv tr t r c = 0) : tr.cell t r c = 0 := by
  rw [cell_eq_ofNat, h]; rfl

/-! ## Bit sums -/

theorem ev_sum_append (tr : Trace Fp) (t r : Nat) (pub : List Fp) (l1 l2 : List Expr) :
    (E.sum (l1 ++ l2)).eval tr t r pub = (E.sum l1).eval tr t r pub + (E.sum l2).eval tr t r pub := by
  induction l1 with
  | nil =>
    show (E.sum l2).eval tr t r pub = Fp.ofNat 0 + _
    apply Fp.ext; simp only [Fp.add_def, Fp.toNat_add, Fp.toNat_ofNat]
    have := (Expr.eval (E.sum l2) tr t r pub).toNat_lt
    simp [Nat.mod_eq_of_lt this]
  | cons e es ih =>
    rw [List.cons_append, ev_sum_cons, ev_sum_cons, ih]
    grind

theorem ofBits_succ (f : Nat → Nat) (n : Nat) : ofBits f (n + 1) = ofBits f n + 2 ^ n * f n := rfl

theorem ev_bits (tr : Trace Fp) (t r : Nat) (pub : List Fp) (x : Nat → Expr) (off len : Nat) :
    (E.bits x off len).eval tr t r pub =
      Fp.ofNat (ofBits (fun b => ((x (off + b)).eval tr t r pub).toNat) len) := by
  induction len with
  | zero => rfl
  | succ n ih =>
    unfold E.bits at ih ⊢
    rw [List.range_succ, List.map_append, ev_sum_append, ih, ofBits_succ, ofNat_add]
    congr 1
    simp only [List.map_cons, List.map_nil, ev_sum_cons, ev_sum_nil, ev_smul]
    rw [ofNat_mul, Fp.ofNat_toNat]
    apply Fp.ext; simp only [Fp.add_def, Fp.toNat_add, Fp.toNat_ofNat]
    have := (Fp.ofNat (2 ^ n) * Expr.eval (x (off + n)) tr t r pub).toNat_lt
    simp [Nat.mod_eq_of_lt this]

theorem ofBits_lt (f : Nat → Nat) (hf : ∀ b, f b ≤ 1) : ∀ n, ofBits f n < 2 ^ n := by
  intro n
  induction n with
  | zero => simp [ofBits]
  | succ n ih =>
    rw [ofBits_succ, Nat.pow_succ]
    have := hf n
    have : 2 ^ n * f n ≤ 2 ^ n := by
      calc 2 ^ n * f n ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ this
        _ = 2 ^ n := Nat.mul_one _
    omega

theorem ofBits_lt' (f : Nat → Nat) (n : Nat) (hf : ∀ b, b < n → f b ≤ 1) : ofBits f n < 2 ^ n := by
  have : ofBits f n = ofBits (fun b => if b < n then f b else 0) n := by
    suffices ∀ m, m ≤ n → ofBits f m = ofBits (fun b => if b < n then f b else 0) m from this n (Nat.le_refl _)
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [ofBits_succ, ofBits_succ, ih (by omega), if_pos (by omega)]
  rw [this]
  exact ofBits_lt _ (fun b => by by_cases h : b < n <;> simp [h, hf]) n

theorem ofBits_split (f : Nat → Nat) (o : Nat) :
    ∀ n, ofBits f (o + n) = ofBits f o + 2 ^ o * ofBits (fun b => f (o + b)) n := by
  intro n
  induction n with
  | zero => simp [ofBits]
  | succ n ih =>
    rw [show o + (n + 1) = (o + n) + 1 by omega, ofBits_succ, ih, ofBits_succ, Nat.pow_add,
      Nat.mul_add, Nat.mul_assoc]
    omega

theorem ofBits_congr (f g : Nat → Nat) (n : Nat) (h : ∀ b, b < n → f b = g b) :
    ofBits f n = ofBits g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ofBits_succ, ofBits_succ, ih (fun b hb => h b (by omega)), h n (by omega)]

/-- An 8-bit window of a bit-decomposed 32-bit word. -/
theorem ofBits_byte (f : Nat → Nat) (hf : ∀ b, b < 32 → f b ≤ 1) (o : Nat) (ho : o + 8 ≤ 32) :
    ofBits f 32 / 2 ^ o % 256 = ofBits (fun b => f (o + b)) 8 := by
  have h1 := ofBits_split f o (32 - o)
  rw [show o + (32 - o) = 32 by omega] at h1
  have h2 := ofBits_split (fun b => f (o + b)) 8 (32 - o - 8)
  rw [show 8 + (32 - o - 8) = 32 - o by omega] at h2
  have hlo : ofBits f o < 2 ^ o := ofBits_lt' f o (fun b hb => hf b (by omega))
  have h8 : ofBits (fun b => f (o + b)) 8 < 2 ^ 8 := ofBits_lt' _ 8 (fun b hb => hf _ (by omega))
  rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos o), Nat.div_eq_of_lt hlo, Nat.zero_add, h2]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h8]

end ZkFormal.Sha.Frame
