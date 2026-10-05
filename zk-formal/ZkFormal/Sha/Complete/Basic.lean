import ZkFormal.Sha.Statements

/-!
# ZkFormal.Sha.Complete.Basic — integer evaluation of the honest trace

Every cell of `honestTrace msgs` is `Fp.ofNat` of a natural, so an AIR
expression evaluates to the image of an integer computed from the `Nat`
cells (`eval_honest`).  The completeness proofs show that integer is `0`.

Also: `zev` of the expression builders of ZkFormal.Sha.Table, and the
bit-level facts (`bit` of rotations, `σ`, `Ch`, `Maj`) they reduce to.
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Table

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

/-- The integer environment of row `r` of the honest trace. -/
def henv (msgs : List Gen.Msg) (t r : Nat) (pub : List Fp) : ZEnv where
  cur c := Gen.honestCell msgs r c
  nxt c := Gen.honestCell msgs ((r + 1) % (honestTrace msgs).height t) c
  first := if r = 0 then 1 else 0
  last := if r + 1 = (honestTrace msgs).height t then 1 else 0
  pubv i := ((pub.getD i 0).toNat : Int)

theorem intCast_ofNat (n : Nat) : ((n : Int) : Fp) = Fp.ofNat n :=
  Lean.Grind.Ring.intCast_natCast (α := Fp) n

theorem intCast_add (a b : Int) : ((a + b : Int) : Fp) = Fp.add (a : Fp) (b : Fp) :=
  Lean.Grind.Ring.intCast_add (α := Fp) a b

theorem intCast_mul (a b : Int) : ((a * b : Int) : Fp) = Fp.mul (a : Fp) (b : Fp) :=
  Lean.Grind.Ring.intCast_mul (α := Fp) a b

theorem intCast_neg (a : Int) : ((-a : Int) : Fp) = Fp.neg (a : Fp) :=
  Lean.Grind.Ring.intCast_neg (α := Fp) a

theorem eval_honest (msgs : List Gen.Msg) (t r : Nat) (pub : List Fp) :
    ∀ e : Expr, e.eval (honestTrace msgs) t r pub = ((zev (henv msgs t r pub) e : Int) : Fp)
  | .const c => by rw [Ev.eval_const]; simp only [zev]; rw [intCast_ofNat]
  | .col c nx => by
    cases nx
    · rw [Ev.eval_col]; simp only [zev, Bool.false_eq_true, ite_false]; rw [intCast_ofNat]; rfl
    · rw [Ev.eval_colNext]; simp only [zev, ite_true]; rw [intCast_ofNat]; rfl
  | .pub i => by
    show (pub.getD i 0) = (((pub.getD i 0).toNat : Int) : Fp)
    rw [intCast_ofNat, Fp.ofNat_toNat]
  | .isFirst => by
    rw [Ev.eval_isFirst]
    show _ = (((if r = 0 then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .isLast => by
    show (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Fp) =
      (((if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .isTransition => by
    show (if r + 1 = (honestTrace msgs).height t then 0 else 1 : Fp) =
      (((1 - if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int)) : Fp)
    split <;> rfl
  | .add a b => by
    rw [Ev.eval_add, eval_honest msgs t r pub a, eval_honest msgs t r pub b]; simp only [zev]
    rw [intCast_add]
  | .mul a b => by
    rw [Ev.eval_mul, eval_honest msgs t r pub a, eval_honest msgs t r pub b]; simp only [zev]
    rw [intCast_mul]
  | .neg a => by
    rw [Ev.eval_neg, eval_honest msgs t r pub a]; simp only [zev]; rw [intCast_neg]

theorem eval_honest_zero {msgs : List Gen.Msg} {t r : Nat} {pub : List Fp} {e : Expr}
    (h : zev (henv msgs t r pub) e = 0) : e.eval (honestTrace msgs) t r pub = 0 := by
  rw [eval_honest, h]; rfl

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
  simp [Table.E.sub, Int.sub_eq_add_neg]
@[simp] theorem zev_smul (v : Nat) (e : Expr) : zev Z (E.smul v e) = (v : Int) * zev Z e := rfl
@[simp] theorem zev_not (e : Expr) : zev Z (E.not e) = 1 - zev Z e := by simp [Table.E.not]

theorem zev_sum (es : List Expr) : zev Z (E.sum es) = (es.map (zev Z)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Table.E.sum, ih]

theorem zev_addC (g : Expr) (ts : List Expr) (cin res cout : Expr) :
    zev Z (E.addC g ts cin res cout) =
      zev Z g * ((ts.map (zev Z)).sum + zev Z cin - (zev Z res + 65536 * zev Z cout)) := by
  simp [Table.E.addC, zev_sum]

theorem zev_eqG (g x y : Expr) : zev Z (E.eqG g x y) = zev Z g * (zev Z x - zev Z y) := by
  simp [Table.E.eqG]

/-- `Σ_{b<n} 2^b · f b` on naturals. -/
def nbits (f : Nat → Nat) (n : Nat) : Nat := ((List.range n).map fun b => 2 ^ b * f b).sum

theorem nbits_succ (f : Nat → Nat) (n : Nat) : nbits f (n + 1) = nbits f n + 2 ^ n * f n := by
  simp [nbits, List.range_succ, List.sum_append]

theorem zev_bits_of (x : Nat → Expr) (off len : Nat) (f : Nat → Nat)
    (h : ∀ b, b < len → zev Z (x (off + b)) = (f b : Int)) :
    zev Z (E.bits x off len) = (nbits f len : Int) := by
  induction len with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun b hb => h b (by omega))
    simp only [Table.E.bits, zev_sum, List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at ih' ⊢
    rw [ih', nbits_succ, zev_smul, h n (by omega)]
    simp [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
end

/-! ## Bits -/

open Gen

theorem bit_lt (x b : Nat) : bit x b < 2 := Nat.mod_lt _ (by decide)

theorem bit_eq (x b : Nat) : bit x b = if x.testBit b then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; unfold bit
  have := Nat.mod_lt (x / 2 ^ b) (show 2 > 0 by decide)
  by_cases h : x / 2 ^ b % 2 = 1 <;> simp [h] <;> omega

theorem nbits_bit (x o : Nat) : ∀ n, nbits (fun b => bit x (o + b)) n = x / 2 ^ o % 2 ^ n
  | 0 => by simp [nbits, Nat.mod_one]
  | n + 1 => by
    rw [nbits_succ, nbits_bit x o n, Nat.mod_pow_succ, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    rfl

theorem limbN_eq (x l : Nat) (hx : x < 2 ^ 32) (hl : l < 2) :
    limbN x l = x / 2 ^ (16 * l) % 2 ^ 16 := by
  unfold limbN lo16 hi16
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · simp
  · simp only [Nat.reduceMul, Nat.reducePow, Nat.one_ne_zero, ite_false]
    rw [Nat.mod_eq_of_lt (by omega)]

theorem nbits_limb (x l : Nat) (hx : x < 2 ^ 32) (hl : l < 2) :
    nbits (fun b => bit x (16 * l + b)) 16 = limbN x l := by
  rw [nbits_bit, limbN_eq x l hx hl]

theorem testBit_ge {x : Nat} (hx : x < 2 ^ 32) {b : Nat} (hb : 32 ≤ b) : x.testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hb))

theorem mask32_eq : ArenaCore.SHA256.mask32 = 2 ^ 32 - 1 := rfl

theorem testBit_mask32 (b : Nat) : ArenaCore.SHA256.mask32.testBit b = decide (b < 32) := by
  rw [mask32_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_rotr (x n b : Nat) (hx : x < 2 ^ 32) (hn : n < 32) (hb : b < 32) :
    (ArenaCore.SHA256.rotr x n).testBit b = x.testBit ((b + n) % 32) := by
  unfold ArenaCore.SHA256.rotr
  rw [Nat.testBit_and, testBit_mask32, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  simp only [decide_eq_true hb, Bool.and_true]
  by_cases h : b + n < 32
  · rw [Nat.mod_eq_of_lt h, show n + b = b + n by omega]
    have : ¬ (b ≥ 32 - n) := by omega
    simp [this]
  · rw [show (b + n) % 32 = b - (32 - n) by omega, testBit_ge hx (show 32 ≤ n + b by omega)]
    have : b ≥ 32 - n := by omega
    simp [this]

theorem rotr_lt (x n : Nat) : ArenaCore.SHA256.rotr x n < 2 ^ 32 :=
  Nat.and_lt_two_pow _ (by decide)

theorem bsig0_lt (x : Nat) : ArenaCore.SHA256.bsig0 x < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _)) (rotr_lt _ _)
theorem bsig1_lt (x : Nat) : ArenaCore.SHA256.bsig1 x < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _)) (rotr_lt _ _)
theorem ssig0_lt (x : Nat) (hx : x < 2 ^ 32) : ArenaCore.SHA256.ssig0 x < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _))
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)
theorem ssig1_lt (x : Nat) (hx : x < 2 ^ 32) : ArenaCore.SHA256.ssig1 x < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _))
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)
theorem ch_lt (x y z : Nat) (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) : ArenaCore.SHA256.ch x y z < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ hy) (Nat.and_lt_two_pow _ hz)
theorem maj_lt (x y z : Nat) (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) :
    ArenaCore.SHA256.maj x y z < 2 ^ 32 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ hy) (Nat.and_lt_two_pow _ hz))
    (Nat.and_lt_two_pow _ hz)

/-- Integer value of a bit. -/
def bv (x : Bool) : Int := if x then 1 else 0

theorem bit_int (x b : Nat) : ((bit x b : Nat) : Int) = bv (x.testBit b) := by
  rw [bit_eq]; unfold bv; split <;> rfl

theorem xor2_bv (p q : Bool) : bv p + bv q - 2 * (bv p * bv q) = bv (p ^^ q) := by
  cases p <;> cases q <;> decide

theorem ch_bv (p q s : Bool) : bv p * bv q + (1 - bv p) * bv s = bv ((p && q) ^^ (!p && s)) := by
  cases p <;> cases q <;> cases s <;> decide

theorem maj_bv (p q s : Bool) :
    bv p * bv q + bv p * bv s + bv q * bv s - 2 * (bv p * bv q * bv s) =
      bv ((p && q) ^^ (p && s) ^^ (q && s)) := by
  cases p <;> cases q <;> cases s <;> decide

theorem testBit_bsig0 (x b : Nat) (hx : x < 2 ^ 32) (hb : b < 32) :
    (ArenaCore.SHA256.bsig0 x).testBit b =
      (x.testBit ((b + 2) % 32) ^^ x.testBit ((b + 13) % 32) ^^ x.testBit ((b + 22) % 32)) := by
  unfold ArenaCore.SHA256.bsig0
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotr _ _ _ hx (by decide) hb,
    testBit_rotr _ _ _ hx (by decide) hb, testBit_rotr _ _ _ hx (by decide) hb]

theorem testBit_bsig1 (x b : Nat) (hx : x < 2 ^ 32) (hb : b < 32) :
    (ArenaCore.SHA256.bsig1 x).testBit b =
      (x.testBit ((b + 6) % 32) ^^ x.testBit ((b + 11) % 32) ^^ x.testBit ((b + 25) % 32)) := by
  unfold ArenaCore.SHA256.bsig1
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotr _ _ _ hx (by decide) hb,
    testBit_rotr _ _ _ hx (by decide) hb, testBit_rotr _ _ _ hx (by decide) hb]

theorem testBit_ssig0 (x b : Nat) (hx : x < 2 ^ 32) (hb : b < 32) :
    (ArenaCore.SHA256.ssig0 x).testBit b =
      (x.testBit ((b + 7) % 32) ^^ x.testBit ((b + 18) % 32) ^^
        (if b + 3 < 32 then x.testBit (b + 3) else false)) := by
  unfold ArenaCore.SHA256.ssig0
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotr _ _ _ hx (by decide) hb,
    testBit_rotr _ _ _ hx (by decide) hb, Nat.testBit_shiftRight]
  by_cases h : b + 3 < 32
  · rw [if_pos h, Nat.add_comm 3 b]
  · rw [if_neg h, testBit_ge hx (show 32 ≤ 3 + b by omega)]

theorem testBit_ssig1 (x b : Nat) (hx : x < 2 ^ 32) (hb : b < 32) :
    (ArenaCore.SHA256.ssig1 x).testBit b =
      (x.testBit ((b + 17) % 32) ^^ x.testBit ((b + 19) % 32) ^^
        (if b + 10 < 32 then x.testBit (b + 10) else false)) := by
  unfold ArenaCore.SHA256.ssig1
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotr _ _ _ hx (by decide) hb,
    testBit_rotr _ _ _ hx (by decide) hb, Nat.testBit_shiftRight]
  by_cases h : b + 10 < 32
  · rw [if_pos h, Nat.add_comm 10 b]
  · rw [if_neg h, testBit_ge hx (show 32 ≤ 10 + b by omega)]

theorem testBit_ch (x y z b : Nat) (hb : b < 32) :
    (ArenaCore.SHA256.ch x y z).testBit b =
      ((x.testBit b && y.testBit b) ^^ (!x.testBit b && z.testBit b)) := by
  unfold ArenaCore.SHA256.ch
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, testBit_mask32]
  simp [hb]

theorem testBit_maj (x y z b : Nat) :
    (ArenaCore.SHA256.maj x y z).testBit b =
      ((x.testBit b && y.testBit b) ^^ (x.testBit b && z.testBit b) ^^ (y.testBit b && z.testBit b)) := by
  unfold ArenaCore.SHA256.maj
  simp only [Nat.testBit_xor, Nat.testBit_and]

/-! ## `sig`, `ch`, `maj` expressions on bit columns -/

section
variable (Z : ZEnv)

theorem zev_xor2 (x y : Expr) (p q : Bool) (hx : zev Z x = bv p) (hy : zev Z y = bv q) :
    zev Z (E.xor2 x y) = bv (p ^^ q) := by
  simp only [Table.E.xor2, zev_sub, zev_add, zev_smul, zev_mul, hx, hy]
  rw [← xor2_bv]; rfl

theorem zev_xor3 (x y z : Expr) (p q s : Bool) (hx : zev Z x = bv p) (hy : zev Z y = bv q)
    (hz : zev Z z = bv s) : zev Z (E.xor3 x y z) = bv (p ^^ q ^^ s) := by
  unfold Table.E.xor3
  rw [zev_xor2 Z _ _ (p ^^ q) s (zev_xor2 Z _ _ p q hx hy) hz, Bool.xor_assoc]

theorem zev_ch (x y z : Expr) (p q s : Bool) (hx : zev Z x = bv p) (hy : zev Z y = bv q)
    (hz : zev Z z = bv s) : zev Z (E.ch x y z) = bv ((p && q) ^^ (!p && s)) := by
  simp only [Table.E.ch, zev_add, zev_mul, zev_not, hx, hy, hz]; exact ch_bv p q s

theorem zev_maj (x y z : Expr) (p q s : Bool) (hx : zev Z x = bv p) (hy : zev Z y = bv q)
    (hz : zev Z z = bv s) : zev Z (E.maj x y z) = bv ((p && q) ^^ (p && s) ^^ (q && s)) := by
  simp only [Table.E.maj, zev_sub, zev_add, zev_mul, zev_smul, hx, hy, hz]
  rw [← maj_bv]; rfl

theorem zev_k0 : zev Z (E.k 0) = bv false := rfl

/-- `sig` over a bit-decomposed word `X` (rotations only). -/
theorem zev_sig_rot (x : Nat → Expr) (X : Nat) (r1 r2 r3 : Nat)
    (hx : ∀ b, b < 32 → zev Z (x b) = bv (X.testBit b)) (b : Nat) :
    zev Z (E.sig x r1 r2 r3 false b) =
      bv (X.testBit ((b + r1) % 32) ^^ X.testBit ((b + r2) % 32) ^^ X.testBit ((b + r3) % 32)) := by
  unfold Table.E.sig
  simp only [Bool.false_eq_true, ite_false]
  exact zev_xor3 Z _ _ _ _ _ _ (hx _ (Nat.mod_lt _ (by decide))) (hx _ (Nat.mod_lt _ (by decide)))
    (hx _ (Nat.mod_lt _ (by decide)))

/-- `sig` with a shift as third term. -/
theorem zev_sig_shr (x : Nat → Expr) (X : Nat) (r1 r2 r3 : Nat)
    (hx : ∀ b, b < 32 → zev Z (x b) = bv (X.testBit b)) (b : Nat) :
    zev Z (E.sig x r1 r2 r3 true b) =
      bv (X.testBit ((b + r1) % 32) ^^ X.testBit ((b + r2) % 32) ^^
        (if b + r3 < 32 then X.testBit (b + r3) else false)) := by
  unfold Table.E.sig
  simp only [if_true]
  apply zev_xor3 Z _ _ _ _ _ _ (hx _ (Nat.mod_lt _ (by decide))) (hx _ (Nat.mod_lt _ (by decide)))
  split
  · exact hx _ (by assumption)
  · rfl

/-- Limb of a bit-decomposed word. -/
theorem zev_limb (x : Nat → Expr) (X l : Nat) (hX : X < 2 ^ 32) (hl : l < 2)
    (hx : ∀ b, b < 32 → zev Z (x b) = bv (X.testBit b)) :
    zev Z (E.limb x l) = (limbN X l : Int) := by
  unfold Table.E.limb
  rw [zev_bits_of Z x (16 * l) 16 (fun b => bit X (16 * l + b))
    (fun b hb => by rw [hx _ (by omega), bit_int]), nbits_limb X l hX hl]

end

end ZkFormal.Sha.Complete
