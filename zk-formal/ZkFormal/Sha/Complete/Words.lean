import ZkFormal.Sha.Complete.Blocks

/-!
# ZkFormal.Sha.Complete.Words — row environments, gates, word-level limbs

* `renv cur nx`: the integer environment of a (row, next row) pair, and
  `henv_eq` (the honest environment is one);
* `zev_kindN_eq`: a kind gate evaluates to `[next row is Rj, j ∈ js]`;
* limbs of `σ`/`Σ`/`Ch`/`Maj` expressions over bit-decomposed words.
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

def renv (cur nx : Row) (first last : Int) (pubv : Nat → Int) : ZEnv :=
  ⟨rowCell cur, rowCell nx, first, last, pubv⟩

theorem henv_eq (msgs : List Msg) (t r : Nat) (pub : List Fp) :
    henv msgs t r pub =
      renv (rowAt msgs r) (rowAt msgs ((r + 1) % (honestTrace msgs).height t))
        (if r = 0 then 1 else 0) (if r + 1 = (honestTrace msgs).height t then 1 else 0)
        (fun i => ((pub.getD i 0).toNat : Int)) := rfl

@[simp] theorem renv_cur (cur nx : Row) (f l : Int) (p : Nat → Int) (c : Nat) :
    (renv cur nx f l p).cur c = rowCell cur c := rfl
@[simp] theorem renv_nxt (cur nx : Row) (f l : Int) (p : Nat → Int) (c : Nat) :
    (renv cur nx f l p).nxt c = rowCell nx c := rfl

/-- Value of a kind gate on the next row. -/
def gateV (nx : Row) (js : List Nat) : Int :=
  match nx with
  | .round j _ => if j ∈ js then 1 else 0
  | _ => 0

theorem sum_ite_eq (js : List Nat) (hnd : js.Nodup) (j0 : Nat) :
    (js.map fun j => (((if j = j0 then 1 else 0 : Nat)) : Int)).sum = if j0 ∈ js then 1 else 0 := by
  induction js with
  | nil => simp
  | cons j js ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, ih hnd.2, List.mem_cons]
    by_cases h : j = j0
    · subst h; simp [hnd.1]
    · by_cases h' : j0 ∈ js
      · simp [h, h', Ne.symm h]
      · simp [h, h', Ne.symm h]

theorem sum_zero_map (js : List Nat) : (js.map fun _ => ((0 : Nat) : Int)).sum = 0 := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem zev_kindN_eq (Z : ZEnv) (js : List Nat) (hjs : ∀ j ∈ js, j < 16) (hnd : js.Nodup) (nx : Row)
    (hZ : ∀ c, Z.nxt c = rowCell nx c) : zev Z (kindN js) = gateV nx js := by
  rw [zev_kindN]
  have e : (js.map fun j => (Z.nxt (colR j) : Int)) = js.map fun j => ((kR nx j : Nat) : Int) := by
    apply List.map_congr_left
    intro j hj
    rw [hZ, cell_R nx j (hjs j hj)]
  rw [e]
  cases nx with
  | round j0 _ => exact sum_ite_eq js hnd j0
  | _ => exact sum_zero_map js

theorem zev_kindC_eq (Z : ZEnv) (js : List Nat) (hjs : ∀ j ∈ js, j < 16) (hnd : js.Nodup) (cur : Row)
    (hZ : ∀ c, Z.cur c = rowCell cur c) : zev Z (kindC js) = gateV cur js := by
  rw [zev_kindC]
  have e : (js.map fun j => (Z.cur (colR j) : Int)) = js.map fun j => ((kR cur j : Nat) : Int) := by
    apply List.map_congr_left
    intro j hj
    rw [hZ, cell_R cur j (hjs j hj)]
  rw [e]
  cases cur with
  | round j0 _ => exact sum_ite_eq js hnd j0
  | _ => exact sum_zero_map js

theorem zev_gRound (cur nx : Row) (f l : Int) (p : Nat → Int) :
    zev (renv cur nx f l p) gRound = gateV nx (List.range 16) :=
  zev_kindN_eq _ _ (fun _ hj => List.mem_range.mp hj) List.nodup_range nx (fun _ => rfl)

theorem zev_gSched (cur nx : Row) (f l : Int) (p : Nat → Int) :
    zev (renv cur nx f l p) gSched = gateV nx (List.range' 4 12) :=
  zev_kindN_eq _ _ (fun j hj => by rw [List.mem_range'_1] at hj; omega) List.nodup_range' nx
    (fun _ => rfl)

theorem zev_gHelp (cur nx : Row) (f l : Int) (p : Nat → Int) :
    zev (renv cur nx f l p) gHelp = gateV nx (List.range' 1 15) :=
  zev_kindN_eq _ _ (fun j hj => by rw [List.mem_range'_1] at hj; omega) List.nodup_range' nx
    (fun _ => rfl)

theorem zev_gMsgC (cur nx : Row) (f l : Int) (p : Nat → Int) :
    zev (renv cur nx f l p) gMsgC = gateV cur (List.range 4) :=
  zev_kindC_eq _ _ (fun j hj => by rw [List.mem_range] at hj; omega) List.nodup_range cur
    (fun _ => rfl)

theorem zev_nR (cur nx : Row) (f l : Int) (p : Nat → Int) (j : Nat) (hj : j < 16) :
    zev (renv cur nx f l p) (E.n (colR j)) = ((kR nx j : Nat) : Int) := by
  simp [cell_R nx j hj]

theorem zev_cR (cur nx : Row) (f l : Int) (p : Nat → Int) (j : Nat) (hj : j < 16) :
    zev (renv cur nx f l p) (E.c (colR j)) = ((kR cur j : Nat) : Int) := by
  simp [cell_R cur j hj]

/-! ## Bits of words -/

section
variable (Z : ZEnv)

theorem zev_bit_c {x X b : Nat} (h : Z.cur x = bit X b) : zev Z (E.c x) = bv (X.testBit b) := by
  rw [zev_c, h, bit_int]

theorem zev_bit_n {x X b : Nat} (h : Z.nxt x = bit X b) : zev Z (E.n x) = bv (X.testBit b) := by
  rw [zev_n, h, bit_int]

/-- Hypothesis shape: `x b` holds bit `b` of `X`. -/
def Holds32 (x : Nat → Expr) (X : Nat) : Prop := ∀ b, b < 32 → zev Z (x b) = bv (X.testBit b)

theorem limb_word (x : Nat → Expr) (X l : Nat) (hX : X < 2 ^ 32) (hl : l < 2) (hx : Holds32 Z x X) :
    zev Z (E.limb x l) = (limbN X l : Int) := zev_limb Z x X l hX hl hx

theorem limb_ssig0 (x : Nat → Expr) (X l : Nat) (hX : X < 2 ^ 32) (hl : l < 2) (hx : Holds32 Z x X) :
    zev Z (E.limb (E.sig x 7 18 3 true) l) = (limbN (ArenaCore.SHA256.ssig0 X) l : Int) :=
  zev_limb Z _ _ l (ssig0_lt X hX) hl fun b hb => by
    rw [zev_sig_shr Z x X 7 18 3 hx b, testBit_ssig0 X b hX hb]

theorem limb_ssig1 (x : Nat → Expr) (X l : Nat) (hX : X < 2 ^ 32) (hl : l < 2) (hx : Holds32 Z x X) :
    zev Z (E.limb (E.sig x 17 19 10 true) l) = (limbN (ArenaCore.SHA256.ssig1 X) l : Int) :=
  zev_limb Z _ _ l (ssig1_lt X hX) hl fun b hb => by
    rw [zev_sig_shr Z x X 17 19 10 hx b, testBit_ssig1 X b hX hb]

theorem limb_bsig0 (x : Nat → Expr) (X l : Nat) (hX : X < 2 ^ 32) (hl : l < 2) (hx : Holds32 Z x X) :
    zev Z (E.limb (E.sig x 2 13 22 false) l) = (limbN (ArenaCore.SHA256.bsig0 X) l : Int) :=
  zev_limb Z _ _ l (bsig0_lt X) hl fun b hb => by
    rw [zev_sig_rot Z x X 2 13 22 hx b, testBit_bsig0 X b hX hb]

theorem limb_bsig1 (x : Nat → Expr) (X l : Nat) (hX : X < 2 ^ 32) (hl : l < 2) (hx : Holds32 Z x X) :
    zev Z (E.limb (E.sig x 6 11 25 false) l) = (limbN (ArenaCore.SHA256.bsig1 X) l : Int) :=
  zev_limb Z _ _ l (bsig1_lt X) hl fun b hb => by
    rw [zev_sig_rot Z x X 6 11 25 hx b, testBit_bsig1 X b hX hb]

theorem limb_ch (x y z : Nat → Expr) (X Y Zw l : Nat) (hY : Y < 2 ^ 32) (hZ : Zw < 2 ^ 32)
    (hl : l < 2) (hx : Holds32 Z x X) (hy : Holds32 Z y Y) (hz : Holds32 Z z Zw) :
    zev Z (E.limb (fun b => E.ch (x b) (y b) (z b)) l) = (limbN (ArenaCore.SHA256.ch X Y Zw) l : Int) :=
  zev_limb Z _ _ l (ch_lt X Y Zw hY hZ) hl fun b hb => by
    rw [zev_ch Z _ _ _ _ _ _ (hx b hb) (hy b hb) (hz b hb), testBit_ch X Y Zw b hb]

theorem limb_maj (x y z : Nat → Expr) (X Y Zw l : Nat) (hY : Y < 2 ^ 32) (hZ : Zw < 2 ^ 32)
    (hl : l < 2) (hx : Holds32 Z x X) (hy : Holds32 Z y Y) (hz : Holds32 Z z Zw) :
    zev Z (E.limb (fun b => E.maj (x b) (y b) (z b)) l) = (limbN (ArenaCore.SHA256.maj X Y Zw) l : Int) :=
  zev_limb Z _ _ l (maj_lt X Y Zw hY hZ) hl fun b hb => by
    rw [zev_maj Z _ _ _ _ _ _ (hx b hb) (hy b hb) (hz b hb), testBit_maj X Y Zw b]

/-- Carry value from three carry-bit columns on the next row. -/
theorem zev_carryN (cc : Nat → Nat → Nat) (l v : Nat) (hv : v < 8)
    (h : ∀ k, k < 3 → Z.nxt (cc l k) = bit v k) : zev Z (carryN cc l) = (v : Int) := by
  unfold carryN
  rw [zev_bits_of Z _ 0 3 (fun k => bit v k) (fun k hk => by
    simp only [Nat.zero_add, zev_n, h k hk])]
  have := nbits_bit v 0 3
  simp only [Nat.zero_add, Nat.pow_zero, Nat.div_one] at this
  rw [this, Nat.mod_eq_of_lt hv]
end

/-! ## Limb arithmetic -/

theorem limbN_lt (x l : Nat) (hx : x < 2 ^ 32) : limbN x l < 65536 := by
  unfold limbN lo16 hi16; split <;> omega

/-- `x mod 2^32` splits into limbs with the carries of `carry`. -/
theorem carry_spec (xs : List Nat) :
    let s := xs.sum % 2 ^ 32
    (xs.map lo16).sum = lo16 s + 65536 * carry xs 0 ∧
    (xs.map hi16).sum + carry xs 0 = hi16 s + 65536 * carry xs 1 := by
  intro s
  have hsplit : xs.sum = (xs.map hi16).sum * 65536 + (xs.map lo16).sum := by
    clear s
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons, ih, lo16, hi16]
      have := Nat.div_add_mod x 65536
      rw [Nat.add_mul]
      omega
  simp only [carry, s, lo16, hi16, if_true, Nat.one_ne_zero, if_false]
  constructor
  · omega
  · omega

theorem sum_lt_len (xs : List Nat) (m : Nat) (h : ∀ x ∈ xs, x < m) : xs.sum ≤ xs.length * (m - 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h x (List.mem_cons_self ..)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem carry_lt (xs : List Nat) (hxs : ∀ x ∈ xs, x < 2 ^ 32) (hlen : xs.length ≤ 7) (l : Nat) :
    carry xs l < 8 := by
  have h1 := sum_lt_len (xs.map lo16) 65536 (by
    intro y hy; simp only [List.mem_map] at hy; obtain ⟨x, -, rfl⟩ := hy; unfold lo16; omega)
  have h2 := sum_lt_len (xs.map hi16) 65536 (by
    intro y hy; simp only [List.mem_map] at hy; obtain ⟨x, hx, rfl⟩ := hy
    have := hxs x hx; unfold hi16; omega)
  simp only [List.length_map] at h1 h2
  have h3 : xs.length * (65536 - 1) ≤ 7 * 65535 := Nat.mul_le_mul_right _ hlen
  unfold carry
  dsimp only
  split <;> omega

end ZkFormal.Sha.Complete
