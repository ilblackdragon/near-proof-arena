import NearSpecV3.ChaCha20

/-!
# ZkFormal.Chacha.Spec — `Nat`-level facts about the trusted ChaCha20 spec

`NearSpecV3.qr` is a sequence of `Array.set!`s.  We show it replaces the four
slots `a b c d` by the pure quarter-round `qrf` of their old values
(`qr_get`), name the eight quarter-rounds of a double round (`grp`, `qrStep`),
and iterate them (`stBefore`): `stBefore s 80 = rounds 10 s`.  Bit-level facts
about `rotl32`/`add32` used by the AIR proofs are at the end.
-/

namespace ZkFormal.Chacha

open NearSpecV3

/-- The pure quarter-round on four words (exactly `NearSpecV3.qr`'s update order). -/
def qrf (a b c d : Nat) : Nat × Nat × Nat × Nat :=
  let a := add32 a b
  let d := rotl32 (d ^^^ a) 16
  let c := add32 c d
  let b := rotl32 (b ^^^ c) 12
  let a := add32 a b
  let d := rotl32 (d ^^^ a) 8
  let c := add32 c d
  let b := rotl32 (b ^^^ c) 7
  (a, b, c, d)

theorem getElem!_set! (s : Array Nat) (a x i : Nat) (h : a < s.size) :
    (s.set! a x)[i]! = if i = a then x else s[i]! := by
  simp only [Array.set!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases hi : i = a
  · subst hi; simp [h]
  · simp [Ne.symm hi, hi]

theorem size_set! (s : Array Nat) (a x : Nat) : (s.set! a x).size = s.size := by
  simp [Array.set!]

/-- `qr` replaces slots `a b c d` (distinct, in range) by `qrf` of their values. -/
theorem qr_get (s : Array Nat) (a b c d : Nat) (ha : a < s.size) (hb : b < s.size)
    (hc : c < s.size) (hd : d < s.size) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (i : Nat) :
    (qr s a b c d)[i]! =
      let q := qrf s[a]! s[b]! s[c]! s[d]!
      if i = a then q.1 else if i = b then q.2.1 else if i = c then q.2.2.1
      else if i = d then q.2.2.2 else s[i]! := by
  unfold qr qrf
  simp only [getElem!_set!, size_set!, ha, hb, hc, hd, ite_true]
  simp only [Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd,
    hab, hac, had, hbc, hbd, hcd, ite_false]
  by_cases h1 : i = a
  · subst h1; simp [hab, hac, had]
  · by_cases h2 : i = b
    · subst h2; simp [h1]
    · by_cases h3 : i = c
      · subst h3; simp [h1, h2]
      · by_cases h4 : i = d
        · subst h4; simp [h1, h2, h3]
        · simp [h1, h2, h3, h4]

theorem size_qr (s : Array Nat) (a b c d : Nat) : (qr s a b c d).size = s.size := by
  simp [qr]

/-- Slots of quarter-round `p < 8` of a double round (column rounds, then diagonals). -/
def grp (p : Nat) : Nat × Nat × Nat × Nat :=
  match p with
  | 0 => (0, 4, 8, 12) | 1 => (1, 5, 9, 13) | 2 => (2, 6, 10, 14) | 3 => (3, 7, 11, 15)
  | 4 => (0, 5, 10, 15) | 5 => (1, 6, 11, 12) | 6 => (2, 7, 8, 13) | _ => (3, 4, 9, 14)

def qrStep (p : Nat) (s : Array Nat) : Array Nat :=
  qr s (grp p).1 (grp p).2.1 (grp p).2.2.1 (grp p).2.2.2

theorem doubleRound_eq (s : Array Nat) :
    doubleRound s =
      qrStep 7 (qrStep 6 (qrStep 5 (qrStep 4 (qrStep 3 (qrStep 2 (qrStep 1 (qrStep 0 s))))))) := rfl

/-- State before quarter-round number `q` (`q = 8·dr + p`). -/
def stBefore (s : Array Nat) : Nat → Array Nat
  | 0 => s
  | q + 1 => qrStep (q % 8) (stBefore s q)

theorem stBefore_add8 (s : Array Nat) (d : Nat) :
    stBefore s (8 * d + 8) = doubleRound (stBefore s (8 * d)) := by
  rw [doubleRound_eq]
  simp only [stBefore]
  have h : ∀ k, k < 8 → (8 * d + k) % 8 = k := fun k hk => by omega
  rw [h 7 (by omega), h 6 (by omega), h 5 (by omega), h 4 (by omega), h 3 (by omega),
    h 2 (by omega), h 1 (by omega), show 8 * d = 8 * d + 0 from rfl, h 0 (by omega)]

theorem rounds_succ' (n : Nat) (s : Array Nat) : rounds (n + 1) s = doubleRound (rounds n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [rounds, ih, rounds]

theorem stBefore_rounds (s : Array Nat) (d : Nat) : stBefore s (8 * d) = rounds d s := by
  induction d with
  | zero => rfl
  | succ d ih => rw [show 8 * (d + 1) = 8 * d + 8 by omega, stBefore_add8, ih, rounds_succ']

theorem stBefore_80 (s : Array Nat) : stBefore s 80 = rounds 10 s := stBefore_rounds s 10

theorem size_qrStep (p : Nat) (s : Array Nat) : (qrStep p s).size = s.size := size_qr ..

theorem size_stBefore (s : Array Nat) (q : Nat) : (stBefore s q).size = s.size := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [stBefore, size_qrStep, ih]

/-! ## The initial state and the block -/

def consts : List Nat := [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- The ChaCha20 input state of `chachaBlock key ctr`. -/
def initArr (key : List Nat) (ctr : Nat) : Array Nat :=
  #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ key.toArray ++
    #[ctr % M32, (ctr / M32) % M32, 0, 0]

theorem chachaBlock_eq (key : List Nat) (ctr : Nat) :
    chachaBlock key ctr =
      (List.range 16).map fun i => add32 (stBefore (initArr key ctr) 80)[i]! (initArr key ctr)[i]! := by
  rw [stBefore_80]; rfl

theorem chachaBlock_length (key : List Nat) (ctr : Nat) : (chachaBlock key ctr).length = 16 := by
  simp [chachaBlock]

theorem initArr_size {key : List Nat} (hk : key.length = 8) (ctr : Nat) :
    (initArr key ctr).size = 16 := by
  simp [initArr, hk]

/-! ## Bits of `add32`, `rotl32` -/

/-- Bit `b` of `x` as `0/1`. -/
def bt (x b : Nat) : Nat := x / 2 ^ b % 2

theorem bt_le (x b : Nat) : bt x b ≤ 1 := by
  unfold bt; have := Nat.mod_lt (x / 2 ^ b) (show 2 > 0 by decide); omega

theorem bt_eq (x b : Nat) : bt x b = if x.testBit b then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; unfold bt
  have := Nat.mod_lt (x / 2 ^ b) (show 2 > 0 by decide)
  by_cases h : x / 2 ^ b % 2 = 1
  · simp [h]
  · simp [h]; omega

theorem bt_xor (x y b : Nat) : bt (x ^^^ y) b = (bt x b + bt y b) % 2 := by
  rw [bt_eq, bt_eq, bt_eq, Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> rfl

theorem add32_lt (a b : Nat) : add32 a b < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem rotl32_lt {x : Nat} (hx : x < 2 ^ 32) (n : Nat) (hn : n ≤ 32) : rotl32 x n < 2 ^ 32 := by
  unfold rotl32
  rw [show M32 = 2 ^ 32 from rfl]
  apply Nat.or_lt_two_pow (Nat.mod_lt _ (by decide))
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx

theorem testBit_rotl32 {x n b : Nat} (hx : x < 2 ^ 32) (hn0 : 0 < n) (hn : n < 32) (hb : b < 32) :
    (rotl32 x n).testBit b = x.testBit ((b + 32 - n) % 32) := by
  unfold rotl32
  rw [show M32 = 2 ^ 32 from rfl, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h : n ≤ b
  · have e : (b + 32 - n) % 32 = b - n := by omega
    have hhi : x.testBit (32 - n + b) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hb, h, e, hhi]
  · have e : (b + 32 - n) % 32 = 32 - n + b := by omega
    have h' : ¬ (b ≥ n) := by omega
    simp [hb, h', e]

theorem bt_rotl32 {x n b : Nat} (hx : x < 2 ^ 32) (hn0 : 0 < n) (hn : n < 32) (hb : b < 32) :
    bt (rotl32 x n) b = bt x ((b + 32 - n) % 32) := by
  rw [bt_eq, bt_eq, testBit_rotl32 hx hn0 hn hb]

theorem xor_lt32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : x ^^^ y < 2 ^ 32 :=
  Nat.xor_lt_two_pow hx hy

end ZkFormal.Chacha
