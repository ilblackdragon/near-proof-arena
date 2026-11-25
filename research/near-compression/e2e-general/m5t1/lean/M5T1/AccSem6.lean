import M5T1.AccSem5

/-!
# M5T1.AccSem6 — an `ACC` run hashes its blocks from `IV384` (F-4)

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.AccSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.AccDef M5T1.RbSem M5T1.BndLay StateM5a.Sha512If

/-! ## SHA-512 block folding -/

theorem blocks_one (h B : List Nat) (hB : B.length = 128) :
    NearSpecV3.SHA512.blocks 1 h B = NearSpecV3.SHA512.compress h B := by
  match B, hB with
  | x :: xs, hB =>
    simp only [NearSpecV3.SHA512.blocks]
    rw [List.take_of_length_le (by omega)]

theorem blocks_append : ∀ (a b : Nat) (h A B : List Nat), A.length = 128 * a →
    NearSpecV3.SHA512.blocks (a + b) h (A ++ B) =
      NearSpecV3.SHA512.blocks b (NearSpecV3.SHA512.blocks a h A) B
  | 0, b, h, A, B, hA => by
    have : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [NearSpecV3.SHA512.blocks]
  | a + 1, b, h, A, B, hA => by
    match A, hA with
    | x :: xs, hA =>
      rw [show a + 1 + b = (a + b) + 1 by omega, List.cons_append]
      simp only [NearSpecV3.SHA512.blocks]
      rw [← List.cons_append, List.take_append_of_le_length (by simp at hA ⊢; omega),
        List.drop_append_of_le_length (by simp at hA ⊢; omega)]
      exact blocks_append a b _ _ _ (by simp at hA ⊢; omega)

/-- The block bytes of rows `f .. f + k − 1`. -/
def msg (tr : Trace Fp) (f k : Nat) : List Nat := (List.range k).flatMap fun i => blkOf tr (f + i)

theorem blkOf_len (tr : Trace Fp) (r : Nat) : (blkOf tr r).length = 128 := by simp [blkOf]

theorem msg_succ (tr : Trace Fp) (f k : Nat) : msg tr f (k + 1) = msg tr f k ++ blkOf tr (f + k) := by
  simp [msg, List.range_succ, List.flatMap_append]

theorem msg_len (tr : Trace Fp) (f : Nat) : ∀ k, (msg tr f k).length = 128 * k
  | 0 => rfl
  | k + 1 => by rw [msg_succ, List.length_append, msg_len tr f k, blkOf_len]; omega

theorem msg_take (tr : Trace Fp) (f : Nat) : ∀ k, (msg tr f (k + 1)).take 42 = (blkOf tr f).take 42
  | 0 => by simp [msg]
  | k + 1 => by
    rw [msg_succ, List.take_append_of_le_length (by rw [msg_len]; omega), msg_take tr f k]

/-- Two 8-word lists with equal limbs are equal. -/
theorem eq_of_wl {L L' : List Nat} (hl : L.length = 8) (hl' : L'.length = 8)
    (h : ∀ t < 8, Acc.wlimbs (L.getD t 0) = Acc.wlimbs (L'.getD t 0)) : L = L' := by
  apply List.ext_getElem (by rw [hl, hl'])
  intro t h1 h2
  have := h t (by omega)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] at this
  rw [← wlimbs_eq] at this
  exact wlimbs_inj this

/-- A first row's input words are `IV384`. -/
theorem iv_limbs {f : Nat → Nat} (h : ∀ l < 24, f l = (Acc.wlimbs (Acc.IV384.getD (l / 3) 0)).getD (l % 3) 0) :
    ∀ t < 8, [f (3 * t), f (3 * t + 1), f (3 * t + 2)] = Acc.wlimbs (Acc.IV384.getD t 0) := by
  intro t ht
  rw [h _ (by omega), h _ (by omega), h _ (by omega)]
  rw [show 3 * t / 3 = t by omega, show (3 * t + 1) / 3 = t by omega, show (3 * t + 2) / 3 = t by omega,
    show 3 * t % 3 = 0 by omega, show (3 * t + 1) % 3 = 1 by omega, show (3 * t + 2) % 3 = 2 by omega]
  rfl

section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (fullAir tape xtape) pub tr)
  (hr1 : NoRng tape) (hr2 : NoRng xtape)
  (hi1 : NoSendOn B_IF384 tape) (hi2 : NoSendOn B_IF384 xtape) (hC : ChipOK tr)
include H hr1 hr2 hi1 hi2 hC

/-- **A run's blocks fold to its rows' outputs.** -/
theorem fold {h f ℓ : Nat} (hR : AccRun tr h f ℓ) : ∀ k, f + k ≤ ℓ →
    ∃ O : List Nat, O.length = 8 ∧ W64 O ∧
      (∀ t < 8, Acc.wlimbs (O.getD t 0) =
        [accC tr (f + k) "o" (3 * t), accC tr (f + k) "o" (3 * t + 1), accC tr (f + k) "o" (3 * t + 2)]) ∧
      NearSpecV3.SHA512.blocks (k + 1) NearSpecV3.E2E.Bnd.IV384 (msg tr f (k + 1)) = O := by
  obtain ⟨hfl, hℓ, hff, -, -, -, hin⟩ := hR
  intro k
  induction k with
  | zero =>
    intro hk
    have hr : f < tr.height 7 := by omega
    obtain ⟨hw, bw, h8, h16, wb, hh, ho, hb⟩ := row_ok H hi1 hi2 hC hr (fst_act H hr hff)
    have hiv : hw = Acc.IV384 := eq_of_wl h8 rfl (fun t ht => by
      rw [hh t ht]; exact iv_limbs (fst_iv H hr hff) t ht)
    have hbw := blk_words H hr1 hr2 hr (fst_act H hr hff) h16 wb hb
    refine ⟨cW hw bw, (compressOK_cW hw bw).1, (compressOK_cW hw bw).2, ho, ?_⟩
    rw [show msg tr f 1 = blkOf tr f by simp [msg], blocks_one _ _ (blkOf_len tr f), cW, hbw, hiv]
    rfl
  | succ k ih =>
    intro hk
    obtain ⟨O, hO8, wO, hOl, hOb⟩ := ih (by omega)
    have hr : f + (k + 1) < tr.height 7 := by omega
    obtain ⟨ha', hf'⟩ := hin (f + (k + 1)) (by omega) hk
    obtain ⟨hw, bw, h8, h16, wb, hh, ho, hb⟩ := row_ok H hi1 hi2 hC hr ha'
    obtain ⟨-, -, -, hch⟩ := trans_facts H (r := f + k) (by omega) ha' hf'
    have hwO : hw = O := eq_of_wl h8 hO8 (fun t ht => by
      rw [hh t ht, hOl t ht, show f + (k + 1) = f + k + 1 by omega, hch _ (by omega), hch _ (by omega),
        hch _ (by omega)])
    have hbw := blk_words H hr1 hr2 hr ha' h16 wb hb
    refine ⟨cW hw bw, (compressOK_cW hw bw).1, (compressOK_cW hw bw).2, ho, ?_⟩
    rw [msg_succ, blocks_append (k + 1) 1 _ _ _ (by rw [msg_len]), hOb,
      blocks_one _ _ (blkOf_len tr _), cW, hbw, hwO]

/-- `hid` is constant along a run. -/
theorem run_hid {h f ℓ : Nat} (hR : AccRun tr h f ℓ) : ∀ k, f + k ≤ ℓ → accC tr (f + k) "hid" = accC tr f "hid"
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := run_hid hR k (by omega)
    obtain ⟨-, hℓ, -, -, -, -, hin⟩ := hR
    obtain ⟨ha', hf'⟩ := hin (f + (k + 1)) (by omega) hk
    obtain ⟨-, -, e, -⟩ := trans_facts H (r := f + k) (by omega) ha' hf'
    rw [show f + (k + 1) = f + k + 1 by omega, e]
    exact ih
end

end M5T1.AccSem
