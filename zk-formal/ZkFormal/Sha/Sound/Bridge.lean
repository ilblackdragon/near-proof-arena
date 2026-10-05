import ZkFormal.Sha.Statements
import ZkFormal.Sha.Sound.Bits

/-!
# ZkFormal.Sha.Sound.Bridge — from `Expr.eval … = 0` over BabyBear to `Nat` equations

`ev e` is the value of `e` on row `r` as a natural `< P`.  Sums of bounded
values do not wrap, boolean gadgets (`xor2/xor3/ch/maj`) compute the bitwise
functions, and limb additions `addC` with gate `1` are exact `Nat` equations.
-/

namespace ZkFormal.Sha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View ZkFormal.Sha.Table
open ArenaCore.SHA256

section
variable (tr : Trace Fp) (t r : Nat) (pub : List Fp)

/-- Value of `e` on row `r` as a natural. -/
def ev (e : Expr) : Nat := (e.eval tr t r pub).toNat

/-- 32-bit word whose bit `b` is the value of `f b`. -/
def wv (f : Nat → Expr) : Nat := ofBits (fun b => ev tr t r pub (f b)) 32
end

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem ev_lt (e : Expr) : ev tr t r pub e < 2013265921 := Fp.toNat_lt _

@[simp] theorem ev_const (c : Nat) : ev tr t r pub (.const c) = c % 2013265921 := Fp.toNat_ofNat c
@[simp] theorem ev_add (a b : Expr) :
    ev tr t r pub (.add a b) = (ev tr t r pub a + ev tr t r pub b) % 2013265921 := Fp.toNat_add _ _
@[simp] theorem ev_mul (a b : Expr) :
    ev tr t r pub (.mul a b) = ev tr t r pub a * ev tr t r pub b % 2013265921 := Fp.toNat_mul _ _
@[simp] theorem ev_neg (a : Expr) :
    ev tr t r pub (.neg a) = (2013265921 - ev tr t r pub a) % 2013265921 := Fp.toNat_neg _
@[simp] theorem ev_c (x : Nat) : ev tr t r pub (E.c x) = nv tr t r x := rfl
theorem ev_n' (x : Nat) : ev tr t r pub (E.n x) = nv tr t ((r + 1) % tr.height t) x := rfl
theorem ev_n (h : r + 1 < tr.height t) (x : Nat) : ev tr t r pub (E.n x) = nv tr t (r + 1) x := by
  rw [ev_n', Nat.mod_eq_of_lt h]

theorem ev_of_eval {e : Expr} (h : e.eval tr t r pub = 0) : ev tr t r pub e = 0 := by
  unfold ev; rw [h]; rfl

theorem ev_mul_eq_zero {a b : Expr} (h : ev tr t r pub (.mul a b) = 0) :
    ev tr t r pub a = 0 ∨ ev tr t r pub b = 0 := by
  have h' : Fp.mul (a.eval tr t r pub) (b.eval tr t r pub) = 0 := (Fp.eq_zero_iff _).2 h
  rcases fp_mul_eq_zero h' with h1 | h1
  · left; unfold ev; rw [h1]; rfl
  · right; unfold ev; rw [h1]; rfl

theorem ev_sub_eq {a b : Expr} (h : ev tr t r pub (E.sub a b) = 0) :
    ev tr t r pub a = ev tr t r pub b := by
  have ha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
  have hb := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) b
  simp only [E.sub, ev_add, ev_neg] at h
  omega

theorem ev_mul_gate {g : Expr} (x : Expr) (hg : ev tr t r pub g = 1) :
    ev tr t r pub (.mul g x) = ev tr t r pub x := by
  rw [ev_mul, hg, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)]

theorem ev_sum (es : List Expr) :
    ev tr t r pub (E.sum es) = (es.map (ev tr t r pub)).sum % 2013265921 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [E.sum, ev_add, ih, List.map_cons, List.sum_cons]
    rw [Nat.add_mod_mod]

theorem ev_sum_map {α : Type} (f : α → Expr) (l : List α) :
    ev tr t r pub (E.sum (l.map f)) = (l.map fun a => ev tr t r pub (f a)).sum % 2013265921 := by
  rw [ev_sum, List.map_map]; rfl

theorem sum_le_length (l : List Nat) (h : ∀ x ∈ l, x ≤ 1) : l.sum ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.sum_cons, List.length_cons]
    have := h x (List.mem_cons_self ..)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem le_sum_of_mem' {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with h | h
    · omega
    · have := ih h; omega

theorem pow_lt_P {n : Nat} (h : n ≤ 30) : 2 ^ n < 2013265921 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) h) (by decide)

/-! ## Bit decompositions -/

theorem ev_bits (x : Nat → Expr) (off len : Nat) (hlen : len ≤ 30)
    (hx : ∀ b, b < len → ev tr t r pub (x (off + b)) ≤ 1) :
    ev tr t r pub (E.bits x off len) = ofBits (fun b => ev tr t r pub (x (off + b))) len := by
  unfold E.bits
  rw [ev_sum_map]
  suffices hs : ∀ n, n ≤ len →
      ((List.range n).map fun b => ev tr t r pub (E.smul (2 ^ b) (x (off + b)))).sum =
        ofBits (fun b => ev tr t r pub (x (off + b))) n by
    rw [hs len (Nat.le_refl _)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (ofBits_lt (fun b hb => hx b hb)) (Nat.le_of_lt
      (pow_lt_P hlen)))
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega), ofBits_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, E.smul,
      ev_mul, ev_const]
    have hp := pow_lt_P (n := n) (by omega)
    rw [Nat.mod_eq_of_lt hp]
    have := hx n (by omega)
    rcases (by omega : ev tr t r pub (x (off + n)) = 0 ∨ ev tr t r pub (x (off + n)) = 1) with h | h
    · rw [h]; simp
    · rw [h, Nat.mul_one, Nat.mod_eq_of_lt hp]

theorem ev_limb (f : Nat → Expr) (l : Nat) (hf : ∀ b, b < 16 → ev tr t r pub (f (16 * l + b)) ≤ 1) :
    ev tr t r pub (E.limb f l) = ofBits (fun b => ev tr t r pub (f (16 * l + b))) 16 :=
  ev_bits f (16 * l) 16 (by decide) hf

/-- The two limbs of a boolean-decomposed word. -/
theorem limb_split (f : Nat → Expr) (hf : ∀ b, b < 32 → ev tr t r pub (f b) ≤ 1) :
    ev tr t r pub (E.limb f 0) + 65536 * ev tr t r pub (E.limb f 1) = wv tr t r pub f ∧
    ev tr t r pub (E.limb f 0) < 65536 ∧ ev tr t r pub (E.limb f 1) < 65536 := by
  have h0 : ev tr t r pub (E.limb f 0) = ofBits (fun b => ev tr t r pub (f b)) 16 := by
    rw [ev_limb f 0 (fun b hb => hf _ (by omega))]
    exact ofBits_congr (fun b _ => by rw [Nat.mul_zero, Nat.zero_add])
  have h1 : ev tr t r pub (E.limb f 1) = ofBits (fun b => ev tr t r pub (f (16 + b))) 16 := by
    rw [ev_limb f 1 (fun b hb => hf _ (by omega))]
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, h1, wv, show (32 : Nat) = 16 + 16 from rfl, ofBits_add]
  · rw [h0]; exact ofBits_lt (fun b hb => hf b (by omega))
  · rw [h1]; exact ofBits_lt (fun b hb => hf _ (by omega))

theorem wv_lt (f : Nat → Expr) (hf : ∀ b, b < 32 → ev tr t r pub (f b) ≤ 1) :
    wv tr t r pub f < 2 ^ 32 := ofBits_lt hf

theorem bt_wv {f : Nat → Expr} (hf : ∀ b, b < 32 → ev tr t r pub (f b) ≤ 1) {c : Nat} (hc : c < 32) :
    bt (wv tr t r pub f) c = ev tr t r pub (f c) := bt_ofBits hf hc

theorem wv_eq_of_bits {f : Nat → Expr} {N : Nat} (hN : N < 2 ^ 32)
    (h : ∀ b, b < 32 → ev tr t r pub (f b) = bt N b) : wv tr t r pub f = N := by
  unfold wv
  rw [ofBits_congr h, ofBits_bt, Nat.mod_eq_of_lt hN]

/-- Carries: three boolean bits. -/
theorem ev_bits3_lt (x : Nat → Expr) (hx : ∀ b, b < 3 → ev tr t r pub (x b) ≤ 1) :
    ev tr t r pub (E.bits x 0 3) < 8 := by
  rw [ev_bits x 0 3 (by decide) (fun b hb => by rw [Nat.zero_add]; exact hx b hb)]
  exact ofBits_lt (n := 3) (fun b hb => by rw [Nat.zero_add]; exact hx b hb)

/-! ## Boolean gadgets -/

theorem ev_xor2 {a b : Expr} (ha : ev tr t r pub a ≤ 1) (hb : ev tr t r pub b ≤ 1) :
    ev tr t r pub (E.xor2 a b) = (ev tr t r pub a + ev tr t r pub b) % 2 := by
  simp only [E.xor2, E.sub, E.smul, ev_add, ev_neg, ev_mul, ev_const]
  generalize ev tr t r pub a = p at *
  generalize ev tr t r pub b = q at *
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;>
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> decide

theorem ev_xor3 {a b c : Expr} (ha : ev tr t r pub a ≤ 1) (hb : ev tr t r pub b ≤ 1)
    (hc : ev tr t r pub c ≤ 1) :
    ev tr t r pub (E.xor3 a b c) =
      ((ev tr t r pub a + ev tr t r pub b) % 2 + ev tr t r pub c) % 2 := by
  unfold E.xor3
  rw [ev_xor2 (by rw [ev_xor2 ha hb]; omega) hc, ev_xor2 ha hb]

theorem ev_ch {x y z : Expr} (hx : ev tr t r pub x ≤ 1) (hy : ev tr t r pub y ≤ 1)
    (hz : ev tr t r pub z ≤ 1) :
    ev tr t r pub (E.ch x y z) =
      (ev tr t r pub x * ev tr t r pub y + ((ev tr t r pub x + 1) % 2) * ev tr t r pub z) % 2 := by
  simp only [E.ch, E.not, E.sub, E.k, ev_add, ev_neg, ev_mul, ev_const]
  generalize ev tr t r pub x = p at *
  generalize ev tr t r pub y = q at *
  generalize ev tr t r pub z = s at *
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;>
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;>
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> decide

theorem ev_maj {x y z : Expr} (hx : ev tr t r pub x ≤ 1) (hy : ev tr t r pub y ≤ 1)
    (hz : ev tr t r pub z ≤ 1) :
    ev tr t r pub (E.maj x y z) =
      ((ev tr t r pub x * ev tr t r pub y + ev tr t r pub x * ev tr t r pub z) % 2 +
        ev tr t r pub y * ev tr t r pub z) % 2 := by
  simp only [E.maj, E.sub, E.smul, ev_add, ev_neg, ev_mul, ev_const]
  generalize ev tr t r pub x = p at *
  generalize ev tr t r pub y = q at *
  generalize ev tr t r pub z = s at *
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;>
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;>
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> decide

/-! ## Words of the gadgets -/

theorem wv_sig (x : Nat → Expr) (r1 r2 r3 : Nat) (h1 : r1 < 32) (h2 : r2 < 32) (h3 : r3 < 32)
    (hx : ∀ b, b < 32 → ev tr t r pub (x b) ≤ 1) :
    wv tr t r pub (E.sig x r1 r2 r3 false) =
      rotr (wv tr t r pub x) r1 ^^^ rotr (wv tr t r pub x) r2 ^^^ rotr (wv tr t r pub x) r3 := by
  apply wv_eq_of_bits (sig3_lt _ _ _ _)
  intro b hb
  have hX := wv_lt x hx
  rw [bt_sig3 hX h1 h2 h3 hb, bt_wv hx (Nat.mod_lt _ (by decide)), bt_wv hx (Nat.mod_lt _ (by decide)),
    bt_wv hx (Nat.mod_lt _ (by decide))]
  simp only [E.sig, Bool.false_eq_true, ite_false]
  exact ev_xor3 (hx _ (Nat.mod_lt _ (by decide))) (hx _ (Nat.mod_lt _ (by decide)))
    (hx _ (Nat.mod_lt _ (by decide)))

theorem wv_sigS (x : Nat → Expr) (r1 r2 r3 : Nat) (h1 : r1 < 32) (h2 : r2 < 32)
    (hx : ∀ b, b < 32 → ev tr t r pub (x b) ≤ 1) :
    wv tr t r pub (E.sig x r1 r2 r3 true) =
      rotr (wv tr t r pub x) r1 ^^^ rotr (wv tr t r pub x) r2 ^^^ (wv tr t r pub x >>> r3) := by
  have hX := wv_lt x hx
  apply wv_eq_of_bits (sigS_lt hX _ _ _)
  intro b hb
  rw [bt_sigS hX h1 h2 hb, bt_wv hx (Nat.mod_lt _ (by decide)), bt_wv hx (Nat.mod_lt _ (by decide))]
  simp only [E.sig, ite_true]
  have h3 : ev tr t r pub (if b + r3 < 32 then x (b + r3) else E.k 0) =
      (if b + r3 < 32 then bt (wv tr t r pub x) (b + r3) else 0) := by
    by_cases h : b + r3 < 32
    · simp only [h, ite_true]; rw [bt_wv hx h]
    · simp only [h, ite_false, E.k, ev_const]
  rw [← h3]
  refine ev_xor3 (hx _ (Nat.mod_lt _ (by decide))) (hx _ (Nat.mod_lt _ (by decide))) ?_
  by_cases h : b + r3 < 32
  · simp only [h, ite_true]; exact hx _ h
  · simp only [h, ite_false, E.k, ev_const]; decide

theorem wv_ch (x y z : Nat → Expr) (hx : ∀ b, b < 32 → ev tr t r pub (x b) ≤ 1)
    (hy : ∀ b, b < 32 → ev tr t r pub (y b) ≤ 1) (hz : ∀ b, b < 32 → ev tr t r pub (z b) ≤ 1) :
    wv tr t r pub (fun b => E.ch (x b) (y b) (z b)) =
      ch (wv tr t r pub x) (wv tr t r pub y) (wv tr t r pub z) := by
  apply wv_eq_of_bits (ch_lt _ (wv_lt y hy) (wv_lt z hz))
  intro b hb
  rw [bt_ch hb, bt_wv hx hb, bt_wv hy hb, bt_wv hz hb]
  exact ev_ch (hx b hb) (hy b hb) (hz b hb)

theorem wv_maj (x y z : Nat → Expr) (hx : ∀ b, b < 32 → ev tr t r pub (x b) ≤ 1)
    (hy : ∀ b, b < 32 → ev tr t r pub (y b) ≤ 1) (hz : ∀ b, b < 32 → ev tr t r pub (z b) ≤ 1) :
    wv tr t r pub (fun b => E.maj (x b) (y b) (z b)) =
      maj (wv tr t r pub x) (wv tr t r pub y) (wv tr t r pub z) := by
  apply wv_eq_of_bits (maj_lt _ (wv_lt y hy) (wv_lt z hz))
  intro b hb
  rw [bt_maj, bt_wv hx hb, bt_wv hy hb, bt_wv hz hb]
  exact ev_maj (hx b hb) (hy b hb) (hz b hb)

theorem sig_le (x : Nat → Expr) (r1 r2 r3 : Nat) (shr : Bool)
    (hx : ∀ b, b < 32 → ev tr t r pub (x b) ≤ 1) (b : Nat) :
    ev tr t r pub (E.sig x r1 r2 r3 shr b) ≤ 1 := by
  have h3 : ev tr t r pub (if shr then (if b + r3 < 32 then x (b + r3) else E.k 0)
      else x ((b + r3) % 32)) ≤ 1 := by
    cases shr
    · exact hx _ (Nat.mod_lt _ (by decide))
    · by_cases h : b + r3 < 32
      · simp only [h, ↓reduceIte]; exact hx _ h
      · simp only [h, ↓reduceIte, E.k, ev_const]; decide
  unfold E.sig
  rw [ev_xor3 (hx _ (Nat.mod_lt _ (by decide))) (hx _ (Nat.mod_lt _ (by decide))) h3]
  omega

theorem ch_le (x y z : Nat → Expr) (hx : ∀ b, b < 32 → ev tr t r pub (x b) ≤ 1)
    (hy : ∀ b, b < 32 → ev tr t r pub (y b) ≤ 1) (hz : ∀ b, b < 32 → ev tr t r pub (z b) ≤ 1)
    (b : Nat) (hb : b < 32) : ev tr t r pub (E.ch (x b) (y b) (z b)) ≤ 1 := by
  rw [ev_ch (hx b hb) (hy b hb) (hz b hb)]; omega

theorem maj_le (x y z : Nat → Expr) (hx : ∀ b, b < 32 → ev tr t r pub (x b) ≤ 1)
    (hy : ∀ b, b < 32 → ev tr t r pub (y b) ≤ 1) (hz : ∀ b, b < 32 → ev tr t r pub (z b) ≤ 1)
    (b : Nat) (hb : b < 32) : ev tr t r pub (E.maj (x b) (y b) (z b)) ≤ 1 := by
  rw [ev_maj (hx b hb) (hy b hb) (hz b hb)]; omega

/-! ## Gated equations -/

/-- A limb addition with gate `1` whose two sides are below `P` is an exact `Nat` equation. -/
theorem addC_sound {g : Expr} {ts : List Expr} {ci re co : Expr} (hg : ev tr t r pub g = 1)
    (h : ev tr t r pub (E.addC g ts ci re co) = 0)
    (hb1 : (ts.map (ev tr t r pub)).sum + ev tr t r pub ci < 2013265921)
    (hb2 : ev tr t r pub re + 65536 * ev tr t r pub co < 2013265921) :
    (ts.map (ev tr t r pub)).sum + ev tr t r pub ci = ev tr t r pub re + 65536 * ev tr t r pub co := by
  unfold E.addC at h
  rw [ev_mul_gate _ hg] at h
  have h' := ev_sub_eq h
  simp only [ev_add, ev_sum, E.smul, ev_mul, ev_const] at h'
  omega

theorem eqG_sound {g x y : Expr} (hg : ev tr t r pub g = 1) (h : ev tr t r pub (E.eqG g x y) = 0) :
    ev tr t r pub x = ev tr t r pub y := by
  unfold E.eqG at h
  rw [ev_mul_gate _ hg] at h
  exact ev_sub_eq h

end ZkFormal.Sha.Sound
