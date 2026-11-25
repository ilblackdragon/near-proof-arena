import M5T1.AccSem6

/-!
# M5T1.AccSem — the resume edge's SHA-384 accumulator appends, from the circuit (F-4)

**`acc_sound`**: on every `Holds (fullAir tape xtape)` trace whose public values are bytes, whose
public tapes send nothing on `RNG` / `IF384` and receive nothing on `ACCD`, and whose `IF384` chip
stub is a faithful SHA-512 compression chip (`AccDef.ChipOK`, lane B's named contract), both
accumulator appends of `ACC` hold (`AccDef.AccOK`): for `hid ∈ {0, 1}` the message of the
(chosen) `ACC` run is a whole number of byte blocks, starts with the input record's accumulator,
and its chained SHA-384 from `IV384`, truncated to 42 bytes, is the output record's accumulator.

Route (files `AccSem1`–`AccSem6`):
1. `RB` row 0 sends `ACCD [h]`; its receiver is an `ACC` row `ℓ` with `lst = 1`, `hid = h`
   (`send_receiver`, `accd_receiver`): `lst_exists`;
2. the backward walk from `ℓ` to the hash's first row (`walk`: row 0 is first if active, an
   active non-first row's predecessor is active and chains) gives an `AccRun`;
3. every active row is one chip compression (`row_ok`: the 16 `IF384` receives come from the chip
   stub, lane B's `comp_sound`), its block words are its bytes (`blk_words`) and its first row
   starts from `IV384` (`fst_iv`);
4. the run folds to `SHA512.blocks` (`fold`), and the last row's `dg` bytes are its output words'
   big-endian bytes (`dg_words`): the first 42 are the output accumulator (`lst_dg`); the first
   row's first 42 block bytes are the input accumulator (`fst_prefix`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.AccSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.AccDef M5T1.RbSem M5T1.BndLay StateM5a.Sha512If

theorem msgOf_spec {tr : Trace Fp} {h : Nat} (hx : ∃ f ℓ, AccRun tr h f ℓ) :
    ∃ f ℓ, AccRun tr h f ℓ ∧ AccDef.msgOf tr h = (List.range (ℓ + 1 - f)).flatMap fun i => blkOf tr (f + i) := by
  classical
  refine ⟨Classical.choose hx, Classical.choose (Classical.choose_spec hx),
    Classical.choose_spec (Classical.choose_spec hx), ?_⟩
  unfold AccDef.msgOf
  rw [dif_pos hx]

theorem blkOf_take (tr : Trace Fp) (r : Nat) :
    (blkOf tr r).take 42 = (List.range 42).map fun j => accC tr r "blk" j := by
  simp only [blkOf, List.map_take, List.take_range]; rfl

theorem bytesOf_eq (pub : List Fp) (a n : Nat) :
    SegRt.bytesOf pub a n = (List.range n).map fun i => UInt8.ofNat (SegRt.pv pub (a + i)) := rfl

section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (fullAir tape xtape) pub tr)
include H

omit H in
theorem rb_lt' : 6 < (fullAir tape xtape).tables.length := by rw [fullAir_len]; decide

/-- **Each `hid` has a last `ACC` row** (`RB`'s `ACCD` demand). -/
theorem lst_exists (hd1 : NoRecvOn B_ACCD tape) (hd2 : NoRecvOn B_ACCD xtape) (h : Nat) (h2 : h < 2) :
    ∃ ℓ, ℓ < tr.height 7 ∧ accC tr ℓ "lst" = 1 ∧ accC tr ℓ "hid" = h := by
  have hi : snd B_ACCD .isFirst [K h] ∈ ((fullAir tape xtape).tables[6]'rb_lt').interactions := by
    show _ ∈ Rb.table.interactions
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h0 : 0 < tr.height 6 := by unfold Trace.height; exact Nat.two_pow_pos _
  have hm : 0 < (snd B_ACCD .isFirst [K h]).multNat tr 6 0 pub := by
    simp [snd, Interaction.multNat, Interaction.multNat.go, Expr.eval, Expr.evalWith, rowEnv]
  obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, hmp⟩ := send_receiver H rb_lt' h0 hi rfl hm
  obtain ⟨rfl, rfl⟩ := accd_receiver hd1 hd2 ht' hi' hb' hs'
  have hl1 : (Acc.c "lst").eval tr 7 r' pub = 1 := by
    by_cases hne : (Acc.c "lst").eval tr 7 r' pub = 1
    · exact hne
    · simp [accdRcv, rcv, Interaction.multNat, Interaction.multNat.go, hne] at hmp
  refine ⟨r', hr', ?_, ?_⟩
  · show ((Acc.c "lst").eval tr 7 r' pub).toNat = 1
    rw [hl1]; rfl
  · simp only [accdRcv, rcv, snd, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] at hmv
    have := congrArg Fp.toNat hmv
    show ((Acc.c "hid").eval tr 7 r' pub).toNat = h
    rw [this]
    show ev tr 6 0 pub (K h) = h
    rw [evK, Nat.mod_eq_of_lt (by omega)]

/-- **The backward walk** from an active row to its hash's first row. -/
theorem walk : ∀ i, i < tr.height 7 → accC tr i "act" = 1 →
    ∃ f ≤ i, accC tr f "fst" = 1 ∧ ∀ j, f < j → j ≤ i → accC tr j "act" = 1 ∧ accC tr j "fst" = 0
  | 0, hr, ha => ⟨0, Nat.le_refl _, row0_fst H hr ha, fun j h1 h2 => absurd h2 (by omega)⟩
  | i + 1, hr, ha => by
    have hb := (bools H hr).2.1
    by_cases hf : accC tr (i + 1) "fst" = 1
    · exact ⟨i + 1, Nat.le_refl _, hf, fun j h1 h2 => absurd h2 (by omega)⟩
    · have hf0 : accC tr (i + 1) "fst" = 0 := by omega
      obtain ⟨ha', -, -, -⟩ := trans_facts H hr ha hf0
      obtain ⟨f, hfi, hff, hin⟩ := walk i (by omega) ha'
      refine ⟨f, by omega, hff, fun j h1 h2 => ?_⟩
      by_cases hj : j = i + 1
      · subst hj; exact ⟨ha, hf0⟩
      · exact hin j h1 (by omega)

variable (hb : ∀ i < 1531, SegRt.pv pub i < 256) (hr1 : NoRng tape) (hr2 : NoRng xtape)
  (hi1 : NoSendOn B_IF384 tape) (hi2 : NoSendOn B_IF384 xtape) (hC : ChipOK tr)
include hr1 hr2 hi1 hi2 hC

/-- **Every run is an accumulator append.** -/
theorem run_msg {h f ℓ : Nat} (h2 : h < 2) (hR : AccRun tr h f ℓ) :
    IsAccMsg pub h ((List.range (ℓ + 1 - f)).flatMap fun i => blkOf tr (f + i)) := by
  obtain ⟨hfl, hℓ, hff, haℓ, hlℓ, hhℓ, hin⟩ := hR
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = f + k := ⟨ℓ - f, by omega⟩
  rw [show f + k + 1 - f = k + 1 by omega]
  show IsAccMsg pub h (msg tr f (k + 1))
  have hhf : accC tr f "hid" = h := by
    rw [← hhℓ]; exact (run_hid H hr1 hr2 hi1 hi2 hC ⟨hfl, hℓ, hff, haℓ, hlℓ, hhℓ, hin⟩ k (Nat.le_refl _)).symm
  have hfr : f < tr.height 7 := by omega
  refine ⟨by rw [msg_len]; omega, by rw [msg_len]; omega, ?_, ?_, ?_⟩
  · intro x hx
    simp only [msg, List.mem_flatMap, List.mem_range] at hx
    obtain ⟨i, hi, hx⟩ := hx
    have hact : accC tr (f + i) "act" = 1 := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact fst_act H hfr hff
      · exact (hin (f + i) (by omega) (by omega)).1
    simp only [blkOf, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (blk_ranges H hr1 hr2 (by omega) hact).1 j hj
  · rw [msg_take, blkOf_take, List.map_map, accIn, bytesOf_eq]
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp]
    rw [fst_prefix H hfr hff hhf h2 j (List.mem_range.1 hj)]
  · obtain ⟨O, hO8, wO, hOl, hOb⟩ := fold H hr1 hr2 hi1 hi2 hC ⟨hfl, hℓ, hff, haℓ, hlℓ, hhℓ, hin⟩ k
      (Nat.le_refl _)
    unfold chainDig
    rw [msg_len, show 128 * (k + 1) / 128 = k + 1 by omega, hOb]
    have hd : NearSpecV3.SHA512.digestBytes O = (wbytes O).map UInt8.ofNat := by
      have e : ∀ l : List UInt8, l.map (UInt8.ofNat ∘ UInt8.toNat) = l := fun l => by
        induction l with
        | nil => rfl
        | cons x l ih => simp only [List.map_cons, ih, Function.comp, UInt8.ofNat_toNat]
      rw [← digestBytes_map, List.map_map, e]
    rw [hd, wbytes_eq, hO8, List.map_map, ← List.map_take, List.take_range, accOut, bytesOf_eq]
    simp only [show min 42 (8 * 8) = 42 from rfl]
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.1 hj
    simp only [Function.comp]
    rw [dg_words H hr1 hr2 hℓ hlℓ hO8 wO hOl j (by omega), lst_dg H hℓ hlℓ hhℓ h2 j hj]

end

/-- **The `ACC` rows establish both accumulator appends.** -/
theorem acc_sound {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp}
    (H : Holds (fullAir tape xtape) pub tr) (hb : ∀ i < 1531, SegRt.pv pub i < 256)
    (hr1 : NoRng tape) (hr2 : NoRng xtape)
    (hi1 : NoSendOn B_IF384 tape) (hi2 : NoSendOn B_IF384 xtape)
    (hd1 : NoRecvOn B_ACCD tape) (hd2 : NoRecvOn B_ACCD xtape)
    (hC : ChipOK tr) : AccOK pub tr := by
  intro h h2
  obtain ⟨ℓ, hℓ, hl, hh⟩ := lst_exists H hd1 hd2 h h2
  obtain ⟨f, hfl, hff, hin⟩ := walk H ℓ hℓ (lst_act H hℓ hl)
  obtain ⟨f', ℓ', hR, he⟩ := msgOf_spec ⟨f, ℓ, hfl, hℓ, hff, lst_act H hℓ hl, hl, hh, hin⟩
  rw [he]
  exact run_msg H hr1 hr2 hi1 hi2 hC h2 hR

#print axioms acc_sound

end M5T1.AccSem
