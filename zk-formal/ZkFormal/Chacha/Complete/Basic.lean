import ZkFormal.Chacha.Gen

/-!
# ZkFormal.Chacha.Complete.Basic — cells of the honest rows, legal transitions, word facts

* `rowCell` read at each column group (`rowCell_S`, `rowCell_X`, …), all cells `< 2^16`;
* `Step X Y`: the legal (row, next row) pairs of the honest trace;
* `HEnv Z X Y`: the integer environment `Z` reads row `X` and next row `Y`;
* word facts: limb additions with carries (`add_carry`), rotations of xors (`rotl_xor`),
  every word of `stBefore (init R) q` is `< 2^32`.
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table ZkFormal.Chacha.Gen
open NearSpecV3

/-! ## Cells -/

theorem rowCell_S (X : Row) {i l : Nat} (hi : i < 16) (hl : l < 2) :
    rowCell X (colS i l) = limbN (sWord X i) l := by
  unfold rowCell colS
  rw [if_pos (by omega), show (2 * i + l) / 2 = i by omega, show (2 * i + l) % 2 = l by omega]

theorem rowCell_X (X : Row) {m b : Nat} (hm : m < 6) (hb : b < 32) :
    rowCell X (colX m b) = bt (xWord X m) b := by
  unfold rowCell colX
  rw [if_neg (by omega), if_pos (by omega), show (32 + 32 * m + b - 32) / 32 = m by omega,
    show (32 + 32 * m + b - 32) % 32 = b by omega]

theorem rowCell_C (X : Row) {q l : Nat} (hq : q < 4) (hl : l < 2) :
    rowCell X (colC q l) = cCell X q l := by
  unfold rowCell colC
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (224 + 2 * q + l - 224) / 2 = q by omega, show (224 + 2 * q + l - 224) % 2 = l by omega]

theorem rowCell_K (X : Row) {j l : Nat} (hj : j < 9) (hl : l < 2) :
    rowCell X (colK j l) = limbN (kWord X j) l := by
  unfold rowCell colK
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (232 + 2 * j + l - 232) / 2 = j by omega, show (232 + 2 * j + l - 232) % 2 = l by omega]

theorem rowCell_fl (X : Row) {c : Nat} (h1 : 250 ≤ c) (h2 : c < 268) :
    rowCell X c = kflag X.kd (c - 250) := by
  unfold rowCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem rowCell_M (X : Row) {kk : Nat} (hk : kk < 4) : rowCell X (colM kk) = mflag X kk := by
  unfold rowCell colM
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), if_pos (by omega), show 268 + kk - 268 = kk by omega]

theorem limbN_lt (x l : Nat) : limbN x l < 65536 := Nat.mod_lt _ (by decide)

theorem carry_le (x y l : Nat) : carry x y l ≤ 1 := by
  have := limbN_lt x 0; have := limbN_lt y 0; have := limbN_lt x 1; have := limbN_lt y 1
  unfold carry
  dsimp only
  split <;> omega

theorem cCell_le (X : Row) (q l : Nat) : cCell X q l ≤ 1 := by
  unfold cCell
  split <;> (try dsimp only) <;> (try split) <;> first | exact carry_le .. | omega

theorem kflag_le (a : Kd) (k : Nat) : kflag a k ≤ 1 := by
  unfold kflag
  split <;> (repeat' split) <;> first | omega | exact bt_le ..

theorem mflag_le (X : Row) (kk : Nat) : mflag X kk ≤ 1 := by
  unfold mflag; split
  · split <;> omega
  · omega

/-- Every honest cell is `< 2^16`. -/
theorem rowCell_lt (X : Row) (c : Nat) : rowCell X c < 65536 := by
  unfold rowCell
  split; · exact limbN_lt ..
  split; · have := bt_le (xWord X ((c - 32) / 32)) ((c - 32) % 32); omega
  split; · have := cCell_le X ((c - 224) / 2) ((c - 224) % 2); omega
  split; · exact limbN_lt ..
  split; · have := kflag_le X.kd (c - 250); omega
  split
  · split
    · have := mflag_le X (c - 268); omega
    · omega
  · omega

/-- Booleanity of the boolean columns. -/
theorem rowCell_bool (X : Row) {c : Nat} (hc : c ∈ boolCols) : rowCell X c ≤ 1 := by
  unfold boolCols at hc
  simp only [List.mem_append, List.mem_range'_1] at hc
  unfold rowCell
  rcases hc with hc | hc
  · rw [if_neg (by omega)]
    split; · exact bt_le ..
    rw [if_pos (by omega)]; exact cCell_le ..
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    split; · exact kflag_le ..
    rw [if_pos (by omega)]; split
    · exact mflag_le ..
    · omega

/-! ## The integer environment of an honest row -/

/-- `Z` reads row `X` (current) and row `Y` (next). -/
structure HEnv (Z : ZEnv) (X Y : Row) : Prop where
  cur : ∀ c, Z.cur c = rowCell X c
  nxt : ∀ c, Z.nxt c = rowCell Y c

section
variable {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y)
include h

theorem zS {i l : Nat} (hi : i < 16) (hl : l < 2) : zev Z (sC i l) = (limbN (sWord X i) l : Int) := by
  simp only [sC, zev_c, h.cur, rowCell_S X hi hl]

theorem zSn {i l : Nat} (hi : i < 16) (hl : l < 2) : zev Z (sN i l) = (limbN (sWord Y i) l : Int) := by
  simp only [sN, zev_n, h.nxt, rowCell_S Y hi hl]

theorem zK {j l : Nat} (hj : j < 9) (hl : l < 2) : zev Z (E.c (colK j l)) = (limbN (kWord X j) l : Int) := by
  simp only [zev_c, h.cur, rowCell_K X hj hl]

theorem zKn {j l : Nat} (hj : j < 9) (hl : l < 2) : zev Z (E.n (colK j l)) = (limbN (kWord Y j) l : Int) := by
  simp only [zev_n, h.nxt, rowCell_K Y hj hl]

theorem zC {q l : Nat} (hq : q < 4) (hl : l < 2) : zev Z (E.c (colC q l)) = (cCell X q l : Int) := by
  simp only [zev_c, h.cur, rowCell_C X hq hl]

theorem zcin {q l : Nat} (hq : q < 4) (hl : l < 2) :
    zev Z (cin q l) = if l = 0 then 0 else (cCell X q 0 : Int) := by
  unfold cin; split
  · rfl
  · exact zC h hq (by decide)

theorem bitsX {m : Nat} (hm : m < 6) : BitsOf Z (xb m) (xWord X m) := by
  intro b hb; simp only [xb, zev_c, h.cur, rowCell_X X hm hb]

theorem zX {m l : Nat} (hm : m < 6) (hl : l < 2) :
    zev Z (E.limb (xb m) l) = (limbN (xWord X m) l : Int) := zev_limb (bitsX h hm) hl

theorem zP {p : Nat} (hp : p < 8) : Z.cur (colP p) = kflag X.kd (2 + p) := by
  have e := rowCell_fl X (c := 252 + p) (by omega) (by omega)
  rw [show 252 + p - 250 = 2 + p by omega] at e
  rw [h.cur]; exact e

theorem zF {j : Nat} (hj : j < 4) : Z.cur (colF j) = kflag X.kd (10 + j) := by
  have e := rowCell_fl X (c := 260 + j) (by omega) (by omega)
  rw [show 260 + j - 250 = 10 + j by omega] at e
  rw [h.cur]; exact e

theorem zI0 : Z.cur colI0 = kflag X.kd 0 := by
  rw [h.cur, rowCell_fl X (by unfold colI0; omega) (by unfold colI0; omega)]; rfl

theorem zI1 : Z.cur colI1 = kflag X.kd 1 := by
  rw [h.cur, rowCell_fl X (by unfold colI1; omega) (by unfold colI1; omega)]; rfl

theorem zM {kk : Nat} (hk : kk < 4) : Z.cur (colM kk) = mflag X kk := by
  rw [h.cur, rowCell_M X hk]

/-- No `P` flag: selections over `P` vanish. -/
theorem selP_zero (h0 : ∀ p, p < 8 → kflag X.kd (2 + p) = 0) (f : Nat → Expr) :
    zev Z (E.sel colP 8 f) = 0 :=
  zev_sel_zero Z colP 8 f fun x hx => by rw [zP h hx, h0 x hx]

theorem selF_zero (h0 : ∀ j, j < 4 → kflag X.kd (10 + j) = 0) (f : Nat → Expr) :
    zev Z (E.sel colF 4 f) = 0 :=
  zev_sel_zero Z colF 4 f fun x hx => by rw [zF h hx, h0 x hx]

end

/-! ## Legal transitions -/

/-- Legal (row, next row) pairs of the honest trace. -/
inductive Step : Row → Row → Prop
  | i0 (R : Req) (hR : ReqOk R) : Step (.i0 R) (.i1 R)
  | i1 (R : Req) (hR : ReqOk R) : Step (.i1 R) (.q R 0 0)
  | qp (R : Req) (hR : ReqOk R) (dr p : Nat) (hdr : dr < 10) (hp : p < 7) :
      Step (.q R dr p) (.q R dr (p + 1))
  | qd (R : Req) (hR : ReqOk R) (dr : Nat) (hdr : dr < 9) : Step (.q R dr 7) (.q R (dr + 1) 0)
  | qf (R : Req) (hR : ReqOk R) : Step (.q R 9 7) (.f R 0)
  | ff (R : Req) (hR : ReqOk R) (j : Nat) (hj : j < 3) : Step (.f R j) (.f R (j + 1))
  | fe (R : Req) (hR : ReqOk R) (Y : Row) (hY : Y = .pad ∨ ∃ R', Y = .i0 R') : Step (.f R 3) Y
  | pd (Y : Row) (hY : Y = .pad ∨ ∃ R', Y = .i0 R') : Step .pad Y

/-- Rows allowed at row 0. -/
def FirstOk (X : Row) : Prop := X = .pad ∨ ∃ R, X = .i0 R

/-! ## Word facts -/

theorem add_carry {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) {l : Nat} (hl : l < 2) :
    (limbN x l : Int) + limbN y l + (if l = 0 then 0 else (carry x y 0 : Int)) -
      ((limbN (add32 x y) l : Int) + 65536 * (carry x y l : Int)) = 0 := by
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> simp [carry, limbN, add32, M32] <;> omega

theorem rotl_xor {x y k : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hk0 : 0 < k) (hk : k < 32) :
    rotl32 x k ^^^ rotl32 y k = rotl32 (x ^^^ y) k := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 32
  · rw [Nat.testBit_xor, testBit_rotl32 hx hk0 hk hb, testBit_rotl32 hy hk0 hk hb,
      testBit_rotl32 (xor_lt32 hx hy) hk0 hk hb, Nat.testBit_xor]
  · have h1 : rotl32 x k ^^^ rotl32 y k < 2 ^ 32 :=
      xor_lt32 (rotl32_lt hx k (by omega)) (rotl32_lt hy k (by omega))
    have h2 := rotl32_lt (xor_lt32 hx hy) k (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem bitsOf_rx {Z : ZEnv} {f g : Nat → Expr} {x y k : Nat} (hf : BitsOf Z f x) (hg : BitsOf Z g y)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hk0 : 0 < k) (hk : k < 32) :
    BitsOf Z (fun b => E.xor2 (rot f k b) (rot g k b)) (rotl32 (x ^^^ y) k) := by
  rw [← rotl_xor hx hy hk0 hk]
  exact bitsOf_xor (bitsOf_rot hf hx hk0 hk) (bitsOf_rot hg hy hk0 hk)

/-- Words of an array, all `< 2^32`. -/
def W32 (s : Array Nat) : Prop := s.size = 16 ∧ ∀ i : Nat, s[i]! < 2 ^ 32

theorem getElem!_lt_of {s : Array Nat} (hs : ∀ i, i < s.size → s[i]! < 2 ^ 32) (i : Nat) :
    s[i]! < 2 ^ 32 := by
  by_cases hi : i < s.size
  · exact hs i hi
  · rw [getElem!_neg s i hi]; decide

theorem qw_lt {a b c d : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) :
    let w := qw a b c d
    w.a1 < 2 ^ 32 ∧ w.d1 < 2 ^ 32 ∧ w.c1 < 2 ^ 32 ∧ w.b1 < 2 ^ 32 ∧ w.a2 < 2 ^ 32 ∧
      w.d2 < 2 ^ 32 ∧ w.c2 < 2 ^ 32 ∧ w.b2 < 2 ^ 32 := by
  have a1 := add32_lt a b
  have d1 := rotl32_lt (xor_lt32 hd a1) 16 (by decide)
  have c1 := add32_lt c (rotl32 (d ^^^ add32 a b) 16)
  have b1 := rotl32_lt (xor_lt32 hb c1) 12 (by decide)
  refine ⟨a1, d1, c1, b1, add32_lt _ _, rotl32_lt (xor_lt32 d1 (add32_lt _ _)) 8 (by decide),
    add32_lt _ _, rotl32_lt (xor_lt32 b1 (add32_lt _ _)) 7 (by decide)⟩

theorem qrf_eq (a b c d : Nat) :
    qrf a b c d = ((qw a b c d).a2, (qw a b c d).b2, (qw a b c d).c2, (qw a b c d).d2) := rfl

theorem qrStep_lt {s : Array Nat} (hs : s.size = 16) (hw : ∀ i : Nat, s[i]! < 2 ^ 32) {p : Nat} (hp : p < 8)
    (i : Nat) : (qrStep p s)[i]! < 2 ^ 32 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Sound.grp_facts hp
  unfold qrStep
  rw [qr_get s _ _ _ _ (by omega) (by omega) (by omega) (by omega) h5 h6 h7 h8 h9 h10, qrf_eq]
  obtain ⟨-, -, -, -, a2, d2, c2, b2⟩ := qw_lt (hw (grp p).1) (hw (grp p).2.1) (hw (grp p).2.2.1)
    (hw (grp p).2.2.2)
  simp only
  split; · exact a2
  split; · exact b2
  split; · exact c2
  split; · exact d2
  exact hw i

theorem stBefore_lt {s : Array Nat} (hs : s.size = 16) (hw : ∀ i : Nat, s[i]! < 2 ^ 32) (q i : Nat) :
    (stBefore s q)[i]! < 2 ^ 32 := by
  induction q generalizing i with
  | zero => exact hw i
  | succ q ih =>
    exact qrStep_lt (by rw [size_stBefore]; exact hs) ih (Nat.mod_lt _ (by decide)) i

/-! ## The input state -/

theorem init_get {R : Req} (hR : ReqOk R) {i : Nat} (hi : i < 16) :
    (init R)[i]! = if i < 4 then consts.getD i 0 else if i < 12 then R.key.getD (i - 4) 0
      else if i = 12 then R.ctr else 0 := by
  unfold init
  rw [Sound.initArr_get hR.1 _ hi]
  have hc := hR.2.2.1
  split; · rfl
  split; · rfl
  split; · unfold M32; omega
  split
  · unfold M32; rw [Nat.div_eq_of_lt (by omega)]
  · rfl

theorem init_size {R : Req} (hR : ReqOk R) : (init R).size = 16 := initArr_size hR.1 _

theorem key_lt {R : Req} (hR : ReqOk R) (j : Nat) : R.key.getD j 0 < 2 ^ 32 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : R.key[j]? with
  | none => decide
  | some x => exact hR.2.1 x (List.mem_of_getElem? h)

theorem consts_lt (i : Nat) : consts.getD i 0 < 2 ^ 32 := by
  unfold consts
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i by omega) with h | h | h | h | h
  all_goals (try subst h)
  all_goals (try decide)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; decide

theorem init_lt {R : Req} (hR : ReqOk R) (i : Nat) : (init R)[i]! < 2 ^ 32 := by
  by_cases hi : i < 16
  · rw [init_get hR hi]
    have := hR.2.2.1
    split; · exact consts_lt i
    split; · exact key_lt hR _
    split; · omega
    · decide
  · rw [getElem!_neg _ i (by rw [init_size hR]; exact hi)]; decide

theorem st_lt {R : Req} (hR : ReqOk R) (q i : Nat) : (stBefore (init R) q)[i]! < 2 ^ 32 :=
  stBefore_lt (init_size hR) (init_lt hR) q i

theorem st_size {R : Req} (hR : ReqOk R) (q : Nat) : (stBefore (init R) q).size = 16 := by
  rw [size_stBefore, init_size hR]

/-- The input-word expressions read the key / counter cells of a block row. -/
theorem zev_initLimb {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) {R : Req} (hR : ReqOk R)
    (hk : ∀ j, kWord X j = if j < 8 then R.key.getD j 0 else if j = 8 then R.ctr else 0)
    {i l : Nat} (hi : i < 16) (hl : l < 2) :
    zev Z (initLimb i l) = (limbN (init R)[i]! l : Int) := by
  rw [init_get hR hi]
  unfold initLimb
  split
  · simp [constLimb, limbN]
  split
  · rw [zK h (by omega) hl, hk, if_pos (by omega)]
  split
  · rw [zK h (by decide) hl, hk]; rfl
  · simp [limbN]

end ZkFormal.Chacha.Complete
