import ZkFormal.Chacha.Table
import ZkFormal.Algebra.Fp

/-!
# ZkFormal.Chacha.ZEval — integer evaluation of AIR expressions over BabyBear

`zev Z e` evaluates `e` over `Int` with the cells read as naturals.  For any trace,
`e.eval = ((zev (tenv tr t r pub) e : Int) : Fp)` (`eval_eq`), so a vanishing
constraint whose integer value is in `(-P, P)` has integer value `0` (`zev_eq_zero`).
Completeness proofs show the integer value is `0`.  Word-level lemmas: `BitsOf Z f w`
says the bit expressions `f b` evaluate to the bits of `w`; limbs, xors and rotations
of such words.
-/

namespace ZkFormal.Chacha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table

/-- What an expression reads, on the integers. -/
structure ZEnv where
  cur : Nat → Nat
  nxt : Nat → Nat
  first : Int
  last : Int
  pubv : Nat → Int

def zev (Z : ZEnv) : Expr → Int
  | .const c => (c : Int)
  | .col c nx => if nx then (Z.nxt c : Int) else (Z.cur c : Int)
  | .pub i => Z.pubv i
  | .isFirst => Z.first
  | .isLast => Z.last
  | .isTransition => 1 - Z.last
  | .add a b => zev Z a + zev Z b
  | .mul a b => zev Z a * zev Z b
  | .neg a => - zev Z a

/-- The integer environment of row `r` of table `t`. -/
def tenv (tr : Trace Fp) (t r : Nat) (pub : List Fp) : ZEnv where
  cur c := (tr.cell t r c).toNat
  nxt c := (tr.cell t ((r + 1) % tr.height t) c).toNat
  first := if r = 0 then 1 else 0
  last := if r + 1 = tr.height t then 1 else 0
  pubv i := ((pub.getD i 0).toNat : Int)

theorem intCast_ofNat (n : Nat) : ((n : Int) : Fp) = Fp.ofNat n :=
  Lean.Grind.Ring.intCast_natCast (α := Fp) n

theorem cell_cast (a : Fp) : a = ((a.toNat : Int) : Fp) := by
  rw [intCast_ofNat, Fp.ofNat_toNat]

theorem eval_eq (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    ∀ e : Expr, e.eval tr t r pub = ((zev (tenv tr t r pub) e : Int) : Fp)
  | .const c => by
    show Fp.ofNat c = _; simp only [zev]; rw [intCast_ofNat]
  | .col c nx => by
    cases nx
    · show tr.cell t r c = _; simp only [zev, Bool.false_eq_true, ite_false]; exact cell_cast _
    · show tr.cell t ((r + 1) % tr.height t) c = _; simp only [zev, ite_true]; exact cell_cast _
  | .pub i => by
    show (pub.getD i 0) = (((pub.getD i 0).toNat : Int) : Fp)
    exact cell_cast _
  | .isFirst => by
    show (if r = 0 then 1 else 0 : Fp) = (((if r = 0 then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .isLast => by
    show (if r + 1 = tr.height t then 1 else 0 : Fp) =
      (((if r + 1 = tr.height t then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .isTransition => by
    show (if r + 1 = tr.height t then 0 else 1 : Fp) =
      (((1 - if r + 1 = tr.height t then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .add a b => by
    show Fp.add (a.eval tr t r pub) (b.eval tr t r pub) = _
    rw [eval_eq tr t r pub a, eval_eq tr t r pub b]; simp only [zev]
    exact (Lean.Grind.Ring.intCast_add (α := Fp) _ _).symm
  | .mul a b => by
    show Fp.mul (a.eval tr t r pub) (b.eval tr t r pub) = _
    rw [eval_eq tr t r pub a, eval_eq tr t r pub b]; simp only [zev]
    exact (Lean.Grind.Ring.intCast_mul (α := Fp) _ _).symm
  | .neg a => by
    show Fp.neg (a.eval tr t r pub) = _
    rw [eval_eq tr t r pub a]; simp only [zev]
    exact (Lean.Grind.Ring.intCast_neg (α := Fp) _).symm

theorem P_val : P = 2013265921 := rfl

/-- A vanishing expression with integer value in `(-P, P)` has integer value `0`. -/
theorem zev_eq_zero {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr}
    (h : e.eval tr t r pub = 0) (h1 : -2013265921 < zev (tenv tr t r pub) e)
    (h2 : zev (tenv tr t r pub) e < 2013265921) : zev (tenv tr t r pub) e = 0 := by
  rw [eval_eq] at h
  have := (Lean.Grind.IsCharP.intCast_eq_zero_iff (α := Fp) P _).mp h
  rw [P_val] at this
  omega

/-- Conversely, integer value `0` gives a vanishing expression. -/
theorem eval_zero_of {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr}
    (h : zev (tenv tr t r pub) e = 0) : e.eval tr t r pub = 0 := by
  rw [eval_eq, h]; rfl

theorem tenv_cur_lt (tr : Trace Fp) (t r pub x) : (tenv tr t r pub).cur x < 2013265921 :=
  (tr.cell t r x).toNat_lt

theorem tenv_nxt_lt (tr : Trace Fp) (t r pub x) : (tenv tr t r pub).nxt x < 2013265921 :=
  (tr.cell t _ x).toNat_lt

/-! ## `zev` of the builders -/

section
variable (Z : ZEnv)

@[simp] theorem zev_c (x : Nat) : zev Z (E.c x) = (Z.cur x : Int) := rfl
@[simp] theorem zev_n (x : Nat) : zev Z (E.n x) = (Z.nxt x : Int) := rfl
@[simp] theorem zev_k (v : Nat) : zev Z (E.k v) = (v : Int) := rfl
@[simp] theorem zev_const (v : Nat) : zev Z (.const v) = (v : Int) := rfl
@[simp] theorem zev_add (a b : Expr) : zev Z (.add a b) = zev Z a + zev Z b := rfl
@[simp] theorem zev_mul (a b : Expr) : zev Z (.mul a b) = zev Z a * zev Z b := rfl
@[simp] theorem zev_neg (a : Expr) : zev Z (.neg a) = - zev Z a := rfl
@[simp] theorem zev_isFirst : zev Z .isFirst = Z.first := rfl
@[simp] theorem zev_sub (a b : Expr) : zev Z (E.sub a b) = zev Z a - zev Z b := by
  simp [E.sub, Int.sub_eq_add_neg]
@[simp] theorem zev_smul (v : Nat) (e : Expr) : zev Z (E.smul v e) = (v : Int) * zev Z e := rfl

theorem zev_sum (es : List Expr) : zev Z (E.sum es) = (es.map (zev Z)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [E.sum, ih]

theorem zev_addE (ts : List Expr) (cin res cout : Expr) :
    zev Z (E.addE ts cin res cout) =
      (ts.map (zev Z)).sum + zev Z cin - (zev Z res + 65536 * zev Z cout) := by
  simp [E.addE, zev_sum]

theorem zev_xor2 (x y : Expr) : zev Z (E.xor2 x y) = zev Z x + zev Z y - 2 * (zev Z x * zev Z y) := by
  simp [E.xor2]

/-- Selection by a one-hot flag group. -/
theorem zev_sel (col : Nat → Nat) (n : Nat) (f : Nat → Expr) (p : Nat) (hp : p < n)
    (h1 : Z.cur (col p) = 1) (h0 : ∀ x, x < n → x ≠ p → Z.cur (col x) = 0) :
    zev Z (E.sel col n f) = zev Z (f p) := by
  unfold E.sel
  rw [zev_sum, List.map_map]
  suffices ∀ m, m ≤ n → (((List.range m).map (zev Z ∘ fun x => Expr.mul (E.c (col x)) (f x))).sum
      = if p < m then zev Z (f p) else 0) by
    rw [this n (Nat.le_refl _), if_pos hp]
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp,
      zev_mul, zev_c]
    by_cases hm' : m = p
    · subst hm'; rw [h1]; simp
    · rw [h0 m (by omega) hm']
      by_cases hpm : p < m
      · simp [hpm, show p < m + 1 by omega]
      · simp [hpm, show ¬ p < m + 1 by omega]

/-- All flags of a group off: the selection is `0`. -/
theorem zev_sel_zero (col : Nat → Nat) (n : Nat) (f : Nat → Expr)
    (h0 : ∀ x, x < n → Z.cur (col x) = 0) : zev Z (E.sel col n f) = 0 := by
  unfold E.sel
  rw [zev_sum, List.map_map]
  suffices ∀ m, m ≤ n → (((List.range m).map (zev Z ∘ fun x => Expr.mul (E.c (col x)) (f x))).sum
      = 0) by rw [this n (Nat.le_refl _)]
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    simp [Function.comp, h0 m (by omega)]

end

/-! ## Words as bits -/

/-- `Σ_{b<n} 2^b · f b`. -/
def nbits (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nbits f n + 2 ^ n * f n

theorem nbits_congr {f g : Nat → Nat} {n : Nat} (h : ∀ b, b < n → f b = g b) :
    nbits f n = nbits g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nbits]; rw [ih (fun b hb => h b (by omega)), h n (by omega)]

theorem nbits_lt {f : Nat → Nat} {n : Nat} (h : ∀ b, b < n → f b ≤ 1) : nbits f n < 2 ^ n := by
  induction n with
  | zero => show 0 < 1; decide
  | succ n ih =>
    simp only [nbits, Nat.pow_succ]
    have := ih (fun b hb => h b (by omega))
    have : 2 ^ n * f n ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ (h n (by omega))
    omega

theorem nbits_bt (x n : Nat) : nbits (bt x) n = x % 2 ^ n := by
  induction n with
  | zero => simp [nbits, Nat.mod_one]
  | succ n ih => rw [nbits, ih, Nat.mod_pow_succ]; rfl

theorem bt_nbits {f : Nat → Nat} {n c : Nat} (h : ∀ b, b < n → f b ≤ 1) (hc : c < n) :
    bt (nbits f n) c = f c := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [nbits]
    have hA := nbits_lt (fun b hb => h b (by omega) : ∀ b, b < n → f b ≤ 1)
    by_cases hcn : c < n
    · rw [← ih (fun b hb => h b (by omega)) hcn]
      unfold bt
      obtain ⟨d, hd⟩ : ∃ d, n = c + 1 + d := ⟨n - c - 1, by omega⟩
      have e : 2 ^ n * f n = 2 ^ c * (2 * (2 ^ d * f n)) := by
        rw [hd, Nat.pow_add, Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos c)]
      omega
    · have hc' : c = n := by omega
      subst hc'
      unfold bt
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos c), Nat.div_eq_of_lt hA]
      have := h c (by omega)
      omega

theorem bt_div (x m b : Nat) : bt (x / 2 ^ m) b = bt x (m + b) := by
  unfold bt; rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- The bit expressions `f b` (`b < 32`) evaluate to the bits of `w`. -/
def BitsOf (Z : ZEnv) (f : Nat → Expr) (w : Nat) : Prop :=
  ∀ b, b < 32 → zev Z (f b) = (bt w b : Int)

theorem zev_limb {Z : ZEnv} {f : Nat → Expr} {w : Nat} (h : BitsOf Z f w) {l : Nat} (hl : l < 2) :
    zev Z (E.limb f l) = ((w / 2 ^ (16 * l)) % 65536 : Nat) := by
  unfold E.limb
  rw [zev_sum, List.map_map]
  have key : ∀ m, m ≤ 16 → (((List.range m).map (zev Z ∘ fun b => E.smul (2 ^ b) (f (16 * l + b)))).sum
      = (nbits (bt (w / 2 ^ (16 * l))) m : Int)) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp,
        zev_smul, nbits]
      rw [h (16 * l + m) (by omega), bt_div]
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.add_zero]
  rw [key 16 (Nat.le_refl _), nbits_bt]

theorem bitsOf_cols {Z : ZEnv} {col : Nat → Nat} (h : ∀ b, b < 32 → Z.cur (col b) ≤ 1) :
    BitsOf Z (fun b => E.c (col b)) (nbits (fun b => Z.cur (col b)) 32) := by
  intro b hb
  rw [bt_nbits h hb]; rfl

theorem bitsOf_xor {Z : ZEnv} {f g : Nat → Expr} {x y : Nat} (hf : BitsOf Z f x)
    (hg : BitsOf Z g y) : BitsOf Z (fun b => E.xor2 (f b) (g b)) (x ^^^ y) := by
  intro b hb
  rw [zev_xor2, hf b hb, hg b hb, bt_xor]
  have := bt_le x b; have := bt_le y b
  generalize bt x b = u at *; generalize bt y b = v at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ‹u ≤ 1› with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ‹v ≤ 1› with rfl | rfl <;> decide

theorem bitsOf_rot {Z : ZEnv} {f : Nat → Expr} {x k : Nat} (hf : BitsOf Z f x) (hx : x < 2 ^ 32)
    (hk0 : 0 < k) (hk : k < 32) : BitsOf Z (rot f k) (NearSpecV3.rotl32 x k) := by
  intro b hb
  unfold rot
  rw [hf _ (Nat.mod_lt _ (by decide)), bt_rotl32 hx hk0 hk hb]

theorem bitsOf_lt_word {Z : ZEnv} {f : Nat → Expr} {w : Nat} (h : BitsOf Z f w) :
    ∀ b, b < 32 → 0 ≤ zev Z (f b) ∧ zev Z (f b) ≤ 1 := by
  intro b hb; rw [h b hb]; have := bt_le w b; omega

end ZkFormal.Chacha
