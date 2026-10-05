import ArenaCore

/-!
# ZkFormal.Sha.Spec — `ArenaCore.sha256` restated in the shape of the AIR

The AIR (ZkFormal.Sha.Air) lays out one compression over 16 round rows of
4 rounds each, OpenVM-style: a row holds the four `a` values and the four
`e` values it creates, so the working variables of round `t` are the last
four created `a`s and `e`s.  This file proves, on `Nat`, that
`ArenaCore.SHA256.compress` is that computation:

* `Wt blk t` — message schedule, with the recurrence `Wt_rec`;
* `As`/`Es` — the sequences of created `a`/`e` values, shifted by 3 so the
  initial `d,c,b,a` are `As 0..3` (resp. `h,g,f,e` are `Es 0..3`), with the
  recurrences `As_succ4`/`Es_succ4` (the AIR's round constraints);
* `compress_eq` — `compress h blk` is the final addition of `h` and
  `As 67, As 66, As 65, As 64, Es 67, …`;
* `sha256_eq_foldl` — `sha256 m` folds `compress` over the 64-byte chunks of
  `pad m`.

The same proof structure as openvm-fv's `Sha2BlockHasherVmAir` soundness
(schedule recurrence, round step, digest addition), re-done without Mathlib.
-/

namespace ZkFormal.Sha.Spec

open ArenaCore ArenaCore.SHA256

/-! ## Words mod 2^32 -/

theorem add32_eq (a b : Nat) : add32 a b = (a + b) % 2 ^ 32 := rfl

theorem add32_lt (a b : Nat) : add32 a b < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem mod_add_mod' (a b : Nat) : (a % 2 ^ 32 + b) % 2 ^ 32 = (a + b) % 2 ^ 32 := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem add_mod_mod' (a b : Nat) : (a + b % 2 ^ 32) % 2 ^ 32 = (a + b) % 2 ^ 32 := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-! ## The message schedule -/

/-- Schedule windows, exactly as `ArenaCore.SHA256.rounds` threads them. -/
def win (blk : List Nat) : Nat → List Nat
  | 0 => words blk
  | t + 1 => nextWindow (win blk t)

/-- `W_t`. -/
def Wt (blk : List Nat) (t : Nat) : Nat := (win blk t).headD 0

/-- The next schedule word from a 16-window. -/
def schedNext (w0 w1 w9 w14 : Nat) : Nat := add32 (add32 (ssig1 w14) w9) (add32 (ssig0 w1) w0)

theorem nextWindow_eq (l : List Nat) (h : l.length = 16) :
    nextWindow l = l.tail ++ [schedNext (l.getD 0 0) (l.getD 1 0) (l.getD 9 0) (l.getD 14 0)] := by
  match l, h with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

theorem words_length_aux : ∀ n (l : List Nat), l.length ≤ n → (words l).length = l.length / 4 := by
  intro n
  induction n with
  | zero => intro l hl; match l, hl with | [], _ => rfl
  | succ n ih =>
    intro l hl
    match l with
    | a :: b :: c :: d :: rest =>
      simp only [words, List.length_cons]
      rw [ih rest (by simp at hl; omega)]; omega
    | [] => rfl
    | [_] => simp [words]
    | [_, _] => simp [words]
    | [_, _, _] => simp [words]

theorem words_length (l : List Nat) : (words l).length = l.length / 4 :=
  words_length_aux _ l (Nat.le_refl _)

theorem words_length_16 (blk : List Nat) (h : blk.length = 64) : (words blk).length = 16 := by
  rw [words_length, h]

theorem win_length (blk : List Nat) (h : (words blk).length = 16) (t : Nat) :
    (win blk t).length = 16 := by
  induction t with
  | zero => exact h
  | succ t ih => simp [win, nextWindow_eq _ ih, ih]

theorem win_succ_getD (blk : List Nat) (h : (words blk).length = 16) (t i : Nat) (hi : i < 15) :
    (win blk (t + 1)).getD i 0 = (win blk t).getD (i + 1) 0 := by
  have hl := win_length blk h t
  simp only [win, nextWindow_eq _ hl, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hl]; omega)]
  simp

theorem win_succ_15 (blk : List Nat) (h : (words blk).length = 16) (t : Nat) :
    (win blk (t + 1)).getD 15 0 =
      schedNext ((win blk t).getD 0 0) ((win blk t).getD 1 0) ((win blk t).getD 9 0)
        ((win blk t).getD 14 0) := by
  have hl := win_length blk h t
  simp only [win, nextWindow_eq _ hl, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hl])]
  simp [hl]

theorem win_getD (blk : List Nat) (h : (words blk).length = 16) :
    ∀ i t, i < 16 → (win blk t).getD i 0 = Wt blk (t + i) := by
  intro i
  induction i with
  | zero => intro t _; simp [Wt, List.headD_eq_head?_getD, List.getD_eq_getElem?_getD, List.head?_eq_getElem?]
  | succ i ih =>
    intro t hi
    rw [← win_succ_getD blk h t i (by omega), ih (t + 1) (by omega)]
    congr 1; omega

theorem Wt_lt16 (blk : List Nat) (h : (words blk).length = 16) (t : Nat) (ht : t < 16) :
    Wt blk t = (words blk).getD t 0 := by
  have := win_getD blk h t 0 ht
  simp only [win, Nat.zero_add] at this
  exact this.symm

/-- The schedule recurrence `W_{t+16} = σ₁(W_{t+14}) + W_{t+9} + σ₀(W_{t+1}) + W_t`. -/
theorem Wt_rec (blk : List Nat) (h : (words blk).length = 16) (t : Nat) :
    Wt blk (t + 16) = schedNext (Wt blk t) (Wt blk (t + 1)) (Wt blk (t + 9)) (Wt blk (t + 14)) := by
  have e := win_succ_15 blk h t
  rw [win_getD blk h 15 (t + 1) (by omega), win_getD blk h 0 t (by omega),
    win_getD blk h 1 t (by omega), win_getD blk h 9 t (by omega),
    win_getD blk h 14 t (by omega)] at e
  rw [show t + 16 = t + 1 + 15 by omega, e, Nat.add_zero]

theorem Wt_rec' (blk : List Nat) (h : (words blk).length = 16) (t : Nat) :
    Wt blk (t + 16) = (ssig1 (Wt blk (t + 14)) + Wt blk (t + 9) + ssig0 (Wt blk (t + 1)) + Wt blk t)
      % 2 ^ 32 := by
  rw [Wt_rec blk h t]; simp only [schedNext, add32]; omega

/-! ## Rounds -/

def Kt (t : Nat) : Nat := K.getD t 0

theorem K_length : K.length = 64 := rfl

/-- Working variables before round `t`. -/
def Rs (h blk : List Nat) : Nat → Vars
  | 0 => ofList h
  | t + 1 => round (Rs h blk t) (Kt t) (Wt blk t)

theorem rounds_eq (h blk : List Nat) :
    ∀ n t, t + n = 64 → rounds (Rs h blk t) (K.drop t) (win blk t) = Rs h blk 64 := by
  intro n
  induction n with
  | zero => intro t ht; simp only [Nat.add_zero] at ht; subst ht; rfl
  | succ n ih =>
    intro t ht
    have htl : t < K.length := by rw [K_length]; omega
    rw [List.drop_eq_getElem_cons htl]
    simp only [rounds]
    have hk : K[t] = Kt t := by simp [Kt, List.getD_eq_getElem?_getD, htl]
    rw [hk]
    exact ih (t + 1) (by omega)

/-- Created `a` values, shifted by 3: `As 0,1,2,3 = d,c,b,a` initially and
`As (t+4)` is the `a` created by round `t`. -/
def As (h blk : List Nat) : Nat → Nat
  | 0 => h.getD 3 0
  | 1 => h.getD 2 0
  | 2 => h.getD 1 0
  | u + 3 => (Rs h blk u).a

/-- Created `e` values: `Es 0,1,2,3 = h,g,f,e` initially. -/
def Es (h blk : List Nat) : Nat → Nat
  | 0 => h.getD 7 0
  | 1 => h.getD 6 0
  | 2 => h.getD 5 0
  | u + 3 => (Rs h blk u).e

theorem Rs_view (h blk : List Nat) (t : Nat) :
    Rs h blk t = ⟨As h blk (t + 3), As h blk (t + 2), As h blk (t + 1), As h blk t,
                  Es h blk (t + 3), Es h blk (t + 2), Es h blk (t + 1), Es h blk t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show round (Rs h blk t) (Kt t) (Wt blk t) = _
    have e1 : As h blk (t + 1 + 2) = (Rs h blk t).a := rfl
    have e2 : As h blk (t + 1 + 1) = (Rs h blk t).b := by rw [ih]
    have e3 : As h blk (t + 1) = (Rs h blk t).c := by rw [ih]
    have e4 : Es h blk (t + 1 + 2) = (Rs h blk t).e := rfl
    have e5 : Es h blk (t + 1 + 1) = (Rs h blk t).f := by rw [ih]
    have e6 : Es h blk (t + 1) = (Rs h blk t).g := by rw [ih]
    rw [e1, e2, e3, e4, e5, e6]
    rfl

/-- Round `t` creates `a` (the AIR's `a`-limb constraints). -/
theorem As_succ4 (h blk : List Nat) (t : Nat) :
    As h blk (t + 4) =
      (Es h blk t + bsig1 (Es h blk (t + 3)) + ch (Es h blk (t + 3)) (Es h blk (t + 2)) (Es h blk (t + 1))
        + Kt t + Wt blk t + bsig0 (As h blk (t + 3)) + maj (As h blk (t + 3)) (As h blk (t + 2)) (As h blk (t + 1)))
        % 2 ^ 32 := by
  show (Rs h blk (t + 1)).a = _
  simp only [Rs, round, Rs_view h blk t, add32]
  omega

/-- Round `t` creates `e` (the AIR's `e`-limb constraints). -/
theorem Es_succ4 (h blk : List Nat) (t : Nat) :
    Es h blk (t + 4) =
      (As h blk t + Es h blk t + bsig1 (Es h blk (t + 3)) + ch (Es h blk (t + 3)) (Es h blk (t + 2)) (Es h blk (t + 1))
        + Kt t + Wt blk t) % 2 ^ 32 := by
  show (Rs h blk (t + 1)).e = _
  simp only [Rs, round, Rs_view h blk t, add32]
  omega

/-- One compression is the final addition of the chaining value and the last
four created `a`s and `e`s. -/
theorem compress_eq (h blk : List Nat) :
    compress h blk =
      [add32 (h.getD 0 0) (As h blk 67), add32 (h.getD 1 0) (As h blk 66),
       add32 (h.getD 2 0) (As h blk 65), add32 (h.getD 3 0) (As h blk 64),
       add32 (h.getD 4 0) (Es h blk 67), add32 (h.getD 5 0) (Es h blk 66),
       add32 (h.getD 6 0) (Es h blk 65), add32 (h.getD 7 0) (Es h blk 64)] := by
  have e := rounds_eq h blk 64 0 rfl
  simp only [List.drop_zero] at e
  have e' : rounds (ofList h) K (words blk) = Rs h blk 64 := e
  simp only [compress, e', Rs_view]

/-! ## Messages: `sha256` folds `compress` over the padded chunks -/

theorem blocks_flatten (bs : List (List Nat)) (hb : ∀ b ∈ bs, b.length = 64) :
    ∀ (h : List Nat), blocks bs.length h bs.flatten = bs.foldl compress h := by
  induction bs with
  | nil => intro h; rfl
  | cons b bs ih =>
    intro h
    have hb64 := hb b (List.mem_cons_self ..)
    have hne : b ++ bs.flatten ≠ [] := by
      intro e; have := congrArg List.length e; simp [hb64] at this
    simp only [List.length_cons, List.flatten_cons, List.foldl_cons]
    rw [blocks]
    · rw [List.take_left' hb64, List.drop_left' hb64]
      exact ih (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) _
    · exact hne

theorem sha256_eq_foldl (m : Bytes) (bs : List (List Nat))
    (hb : ∀ b ∈ bs, b.length = 64) (hp : pad (m.map UInt8.toNat) = bs.flatten) :
    sha256 m = digestBytes (bs.foldl compress H0) := by
  have hlen : (pad (m.map UInt8.toNat)).length / 64 = bs.length := by
    rw [hp]
    have : ∀ (bs : List (List Nat)), (∀ b ∈ bs, b.length = 64) → bs.flatten.length = 64 * bs.length := by
      intro bs hb
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        simp only [List.flatten_cons, List.length_append, List.length_cons,
          hb b (List.mem_cons_self ..), ih (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))]
        omega
    rw [this bs hb]; omega
  show digestBytes (blocks ((pad (m.map UInt8.toNat)).length / 64) H0 (pad (m.map UInt8.toNat))) = _
  rw [hlen, hp, blocks_flatten bs hb]

end ZkFormal.Sha.Spec
