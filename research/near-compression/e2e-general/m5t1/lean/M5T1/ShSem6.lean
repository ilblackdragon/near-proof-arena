import M5T1.ShSem5

/-!
# M5T1.ShSem6 — an `ACC` run hashes its blocks from `IV384` (F-7, from `AccSem6`)

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.ShSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.ShDef M5T1.BndLay StateM5a.Sha512If
open M5T1.AccDef (cW wbytes chainDig)
open M5T1.AccSem (evAdd evMul evSub evK evOne evZero evFirst0 evFirstS evTrans evPub gate_eq bool_le
  compressOK_cW wlimbs_eq getD_map_wl wbytes_cons wbytes_eq beN8_map digestBytes_map word_bytes
  blocks_one blocks_append eq_of_wl iv_limbs)

/-! ## SHA-512 block folding -/

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

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hr2 : NoRng xtape)
  (hi2 : NoSendOn B_IF384 xtape) (hC : ChipOK tr)
include H hr2 hi2 hC

/-- **A run's blocks fold to its rows' outputs.** -/
theorem fold {f ℓ : Nat} (hR : ShRun tr f ℓ) : ∀ k, f + k ≤ ℓ →
    ∃ O : List Nat, O.length = 8 ∧ W64 O ∧
      (∀ t < 8, Acc.wlimbs (O.getD t 0) =
        [shC tr (f + k) "o" (3 * t), shC tr (f + k) "o" (3 * t + 1), shC tr (f + k) "o" (3 * t + 2)]) ∧
      NearSpecV3.SHA512.blocks (k + 1) NearSpecV3.E2E.Bnd.IV384 (msg tr f (k + 1)) = O := by
  obtain ⟨hfl, hℓ, hff, -, -, hin⟩ := hR
  intro k
  induction k with
  | zero =>
    intro hk
    have hr : f < tr.height 2 := by omega
    obtain ⟨hw, bw, h8, h16, wb, hh, ho, hb⟩ := row_ok H hi2 hC hr (fst_act H hr hff)
    have hiv : hw = Acc.IV384 := eq_of_wl h8 rfl (fun t ht => by
      rw [hh t ht]; exact iv_limbs (fst_iv H hr hff) t ht)
    have hbw := blk_words H hr2 hr (fst_act H hr hff) h16 wb hb
    refine ⟨cW hw bw, (compressOK_cW hw bw).1, (compressOK_cW hw bw).2, ho, ?_⟩
    rw [show msg tr f 1 = blkOf tr f by simp [msg], blocks_one _ _ (blkOf_len tr f), cW, hbw, hiv]
    rfl
  | succ k ih =>
    intro hk
    obtain ⟨O, hO8, wO, hOl, hOb⟩ := ih (by omega)
    have hr : f + (k + 1) < tr.height 2 := by omega
    obtain ⟨ha', hf'⟩ := hin (f + (k + 1)) (by omega) hk
    obtain ⟨hw, bw, h8, h16, wb, hh, ho, hb⟩ := row_ok H hi2 hC hr ha'
    obtain ⟨-, -, -, -, -, hch⟩ := trans_facts H (r := f + k) (by omega) ha' hf'
    have hwO : hw = O := eq_of_wl h8 hO8 (fun t ht => by
      rw [hh t ht, hOl t ht, show f + (k + 1) = f + k + 1 by omega, hch _ (by omega), hch _ (by omega),
        hch _ (by omega)])
    have hbw := blk_words H hr2 hr ha' h16 wb hb
    refine ⟨cW hw bw, (compressOK_cW hw bw).1, (compressOK_cW hw bw).2, ho, ?_⟩
    rw [msg_succ, blocks_append (k + 1) 1 _ _ _ (by rw [msg_len]), hOb,
      blocks_one _ _ (blkOf_len tr _), cW, hbw, hwO]

/-- `hid` is constant along a run. -/
theorem run_hid {f ℓ : Nat} (hR : ShRun tr f ℓ) : ∀ k, f + k ≤ ℓ → shC tr (f + k) "hid" = shC tr f "hid"
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := run_hid hR k (by omega)
    obtain ⟨-, hℓ, -, -, -, hin⟩ := hR
    obtain ⟨ha', hf'⟩ := hin (f + (k + 1)) (by omega) hk
    obtain ⟨-, -, e, -, -, -⟩ := trans_facts H (r := f + k) (by omega) ha' hf'
    rw [show f + (k + 1) = f + k + 1 by omega, e]
    exact ih
end

end M5T1.ShSem
