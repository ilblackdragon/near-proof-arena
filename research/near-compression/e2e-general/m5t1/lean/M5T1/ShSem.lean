import M5T1.ShSem7

/-!
# M5T1.ShSem — the STATE engine half's SHA-384 hashes, from the circuit (F-7)

**`sh_sound`**: on every `Holds (Se.fullSe xtape)` trace whose stand-in tape sends nothing on
`RNG` / `IF384` / `SHB` and receives nothing on `SHD`, and whose `IF384` chip stub is a faithful
SHA-512 compression chip (`ShDef.ChipOK`, lane B's named contract), **every hash `SE` demands**
(`Se.hashes`, multiplicity `1` on row 0) holds (`ShDef.HashOK`): a message of byte blocks whose
chained SHA-384 from `IV384`, truncated to 42 bytes, is the hash's digest bytes on `SE` row 0 —
and for a fixed-content hash the message **is** `SE`'s padded message `Se.padE s.msg` on row 0.

Route (`ShSem1`–`ShSem7`, from `AccSem1`–`AccSem6`):
1. `SE` row 0 sends `SHD [hid, fx, nb − 1, limbs(dig)]`; its receiver is an `SH` row `ℓ` with
   `lst = 1` and that `hid` / `fx` / `bi` / digest limbs (`shd_receiver`): `lst_of`;
2. the backward walk from `ℓ` gives a run `f .. ℓ` (`walk`), along which `hid`, `fx` are constant
   and `bi` counts the blocks (`run_hid`, `run_fx`, `run_bi`), so a fixed run has `nBlk` rows;
3. the run folds to `SHA512.blocks` (`fold`); its last row's digest bytes are its output words'
   (`dg_words`) and equal the demanded digest bytes (limbs of bytes, `limb3_inj`);
4. (fixed content) each row of the run receives `SHB [hid, bi, limbs(blk)]`; its sender is `SE` row
   0's block `bi` of the same hash (`shb_sender`, `se_shb`, `hid_inj`), so the row's block is `SE`'s
   padded block (`blk_eq`), and the run's message is the padded message (`flat_blocks`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.ShSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.ShDef StateM5a.Sha512If
open M5T1.AccDef (cW wbytes chainDig)
open M5T1.AccSem (evAdd evMul evSub evK evOne evZero evFirst0 evFirstS evTrans evPub gate_eq bool_le
  send_receiver wbytes_eq digestBytes_map NoRecvOn)

/-! ## Lists -/

theorem eq_of_map_nodup {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, a, ha, _, _, _ => absurd ha (by simp)
  | x :: xs, hn, a, ha, b, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hx, hn⟩ := hn
    rcases List.mem_cons.1 ha with h1 | ha' <;> rcases List.mem_cons.1 hb with h2 | hb'
    · rw [h1, h2]
    · exfalso; apply hx; rw [← h1, he]; exact List.mem_map_of_mem hb'
    · exfalso; apply hx; rw [← h2, ← he]; exact List.mem_map_of_mem ha'
    · exact eq_of_map_nodup f xs hn a ha' b hb' he

theorem hid_inj {a b : Se.HSpec} (ha : a ∈ Se.hashes) (hb : b ∈ Se.hashes) (h : a.hid = b.hid) : a = b :=
  eq_of_map_nodup Se.HSpec.hid Se.hashes (by decide) a ha b hb h

theorem hid_lt : ∀ s ∈ Se.hashes, s.hid < 9 := by
  intro s hs; simp only [Se.hashes, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A list of `128 n` elements is the concatenation of its `n` blocks. -/
theorem flat_blocks {α : Type} (d : α) : ∀ (n : Nat) (L : List α), L.length = 128 * n →
    (List.range n).flatMap (fun i => (List.range 128).map fun j => L.getD (128 * i + j) d) = L
  | 0, L, h => by simp at h; subst h; rfl
  | n + 1, L, h => by
    rw [List.range_succ (n := n), List.flatMap_append, List.flatMap_singleton]
    have h1 := flat_blocks d n (L.take (128 * n)) (by simp only [List.length_take, h]; omega)
    have e1 : (List.range n).flatMap (fun i => (List.range 128).map fun j => L.getD (128 * i + j) d) =
        L.take (128 * n) := by
      conv => rhs; rw [← h1]
      show (List.map _ (List.range n)).flatten = (List.map _ (List.range n)).flatten
      congr 1
      apply List.map_congr_left
      intro i hi
      apply List.map_congr_left
      intro j hj
      have hi := List.mem_range.1 hi; have hj := List.mem_range.1 hj
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_take_of_lt (by omega)]
    have e2 : (List.range 128).map (fun j => L.getD (128 * n + j) d) = L.drop (128 * n) := by
      apply List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_drop, h]; omega)
      intro j h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_drop, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp at h1; omega)]
      rfl
    rw [e1, e2, List.take_append_drop]

theorem msg_len_le : ∀ s ∈ Se.hashes, s.msg.length ≤ 139 := by
  intro s hs
  simp only [Se.hashes, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Se.serIn, Se.cols, Se.hS0, Se.hS1, Se.hS2, Se.hS3, Se.hS4, Se.hS5, Se.hS6, Se.hS7, Se.hS8]

theorem padE_len (m : List Expr) : (Se.padE m).length = 128 * Se.nBlk m := by
  simp only [Se.nBlk, Se.padE, List.length_append, List.length_singleton, List.length_replicate,
    List.length_map, List.length_range]
  omega

theorem nBlk_pos (m : List Expr) : 0 < Se.nBlk m := by
  simp only [Se.nBlk, Se.padE, List.length_append, List.length_singleton, List.length_replicate,
    List.length_map, List.length_range]
  omega

/-! ## Message decomposition -/

theorem map_append_inj {α β : Type} {f g : α → β} {A B C D : List α} (hl : A.length = C.length)
    (h : (A ++ B).map f = (C ++ D).map g) : A.map f = C.map g ∧ B.map f = D.map g := by
  rw [List.map_append, List.map_append] at h
  exact List.append_inj h (by simp [hl])

theorem fp_ev {a b : Fp} (h : a = b) : a.toNat = b.toNat := congrArg _ h

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hr2 : NoRng xtape)
include H hr2

/-- The digest send of hash `s` on `SE` row 0. -/
def shdSnd (s : Se.HSpec) : Interaction :=
  snd B_SHD s.mul ((if s.fx then [K s.hid, K 1, K (Se.nBlk s.msg - 1)] else [K s.hid, K 0, s.nb]) ++
    Rb.limbs s.dig)

omit H hr2 in
theorem shdSnd_mem {s : Se.HSpec} (hs : s ∈ Se.hashes) : shdSnd s ∈ Se.table.interactions := by
  show _ ∈ Se.interactions5 ++ Se.interactions7
  refine List.mem_append_right _ ?_
  rw [ix7_eq]
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨s, hs, ?_⟩)
  unfold Se.hashIx shdSnd
  cases h : s.fx <;> simp [h]

omit H hr2 in
/-- A hash's multiplicity is `isFirst`-gated: it is `1` only on row 0. -/
theorem mul_row0 : ∀ s ∈ Se.hashes, ∀ r, ev tr 0 r pub s.mul = 1 → r = 0 := by
  intro s hs r h
  by_cases hr : r = 0
  · exact hr
  exfalso
  simp only [Se.hashes, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [evFirstS hr, evMul, Se.hS0, Se.hS1, Se.hS2, Se.hS3, Se.hS4, Se.hS5, Se.hS6, Se.hS7, Se.hS8] at h

/-- **The demanded digest's last row.** -/
theorem lst_of (hd : NoRecvOn B_SHD xtape) {s : Se.HSpec} (hs : s ∈ Se.hashes)
    (hm : ev tr 0 0 pub s.mul = 1) :
    ∃ ℓ, ℓ < tr.height 2 ∧ shC tr ℓ "lst" = 1 ∧ shC tr ℓ "hid" = s.hid ∧
      shC tr ℓ "fx" = (if s.fx then 1 else 0) ∧ (s.fx = true → shC tr ℓ "bi" = Se.nBlk s.msg - 1) ∧
      ∀ j < 42, shC tr ℓ "dg" j = ev tr 0 0 pub (s.dig j) := by
  have hme : s.mul.eval tr 0 0 pub = 1 := by
    have := eval_of_ev (e := s.mul) (t := 0) (r := 0) hm (by decide); rw [this]; rfl
  have hpos : 0 < (shdSnd s).multNat tr 0 0 pub := by
    simp [shdSnd, snd, Interaction.multNat, Interaction.multNat.go, hme]
  obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, hmp⟩ :=
    send_receiver H se_lt (h0pos H hr2) (shdSnd_mem hs) rfl hpos
  obtain ⟨rfl, rfl⟩ := shd_receiver hd ht' hi' hb' hs'
  have hl1 : (Sh.c "lst").eval tr 2 r' pub = 1 := by
    by_cases hne : (Sh.c "lst").eval tr 2 r' pub = 1
    · exact hne
    · exfalso; simp [shdRcv, rcv, Interaction.multNat, Interaction.multNat.go, hne] at hmp
  have hlst : shC tr r' "lst" = 1 := by show ((Sh.c "lst").eval tr 2 r' pub).toNat = 1; rw [hl1]; rfl
  obtain ⟨hB0, -⟩ := dg_ranges H hr2 hr' hlst
  have hB : ∀ k < 48, ev tr 2 r' pub (Sh.dgB k) < 256 := fun k hk => by
    show shC tr r' "dg" k < 256; exact hB0 k hk
  have hdl := se_dig_lt H hr2 s hs
  simp only [Interaction.msgVal, shdRcv, shdSnd, rcv, snd] at hmv
  obtain ⟨h3, h14⟩ := map_append_inj (by cases s.fx <;> rfl) hmv
  refine ⟨r', hr', hlst, ?_, ?_, ?_, ?_⟩
  · have := hid_lt s hs
    cases hf : s.fx <;> simp only [hf, Bool.false_eq_true, ite_true, ite_false, List.map_cons, List.map_nil,
      List.cons.injEq] at h3 <;>
    · have e := fp_ev h3.1
      show ev tr 2 r' pub (Sh.c "hid") = _
      unfold ev; rw [e]; show ev tr 0 0 pub (K s.hid) = _; rw [evK]; omega
  · cases hf : s.fx <;> simp only [hf, Bool.false_eq_true, ite_true, ite_false, List.map_cons, List.map_nil,
      List.cons.injEq] at h3 <;>
    · have e := fp_ev h3.2.1
      show ev tr 2 r' pub (Sh.c "fx") = _
      unfold ev; rw [e]; rfl
  · intro hf
    simp only [hf, ite_true, List.map_cons, List.map_nil, List.cons.injEq] at h3
    have e := fp_ev h3.2.2.1
    show ev tr 2 r' pub (Sh.c "bi") = _
    unfold ev; rw [e]; show ev tr 0 0 pub (K _) = _; rw [evK]
    apply Nat.mod_eq_of_lt
    simp only [Se.nBlk, Se.padE, List.length_append, List.length_singleton, List.length_replicate,
      List.length_map, List.length_range]
    have := msg_len_le s hs
    omega
  · intro j hj
    simp only [Sh.dgLimbs, Rb.limbs, List.map_map] at h14
    have hl := map_range_eq h14 (j / 3) (by omega)
    simp only [Function.comp] at hl
    have hl' := fp_ev hl
    change ev tr 2 r' pub (Rb.limb Sh.dgB (j / 3)) = ev tr 0 0 pub (Rb.limb s.dig (j / 3)) at hl'
    simp only [Rb.limb] at hl'
    rw [ev_limb3 (hB _ (by omega)) (hB _ (by omega)) (hB _ (by omega)),
      ev_limb3 (hdl _ (by omega)) (hdl _ (by omega)) (hdl _ (by omega))] at hl'
    obtain ⟨a0, a1, a2⟩ := limb3_inj (hB _ (by omega)) (hB _ (by omega)) (hB _ (by omega))
      (hdl _ (by omega)) (hdl _ (by omega)) (hdl _ (by omega)) hl'
    have : j = 3 * (j / 3) ∨ j = 3 * (j / 3) + 1 ∨ j = 3 * (j / 3) + 2 := by omega
    rcases this with h | h | h <;> rw [h]
    · exact a0
    · exact a1
    · exact a2

end

/-! ## The run behind a demand -/

theorem getD_map_ev {tr : Trace Fp} {t r : Nat} {pub : List Fp} (l : List Expr) (n : Nat) :
    (l.map (ev tr t r pub)).getD n 0 = ev tr t r pub (l.getD n 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? with
  | none => show 0 = ev tr t r pub (.const 0); simp
  | some x => rfl

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hr2 : NoRng xtape) (hi2 : NoSendOn B_IF384 xtape) (hC : ChipOK tr)
include H hr2 hi2 hC

/-- **A run's message hashes to its last row's digest bytes.** -/
theorem run_digest {f ℓ : Nat} (hR : ShRun tr f ℓ) :
    chainDig (msg tr f (ℓ - f + 1)) = (List.range 42).map fun j => UInt8.ofNat (shC tr ℓ "dg" j) := by
  obtain ⟨hfl, hℓ, hff, haℓ, hlℓ, hin⟩ := hR
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = f + k := ⟨ℓ - f, by omega⟩
  rw [show f + k - f + 1 = k + 1 by omega]
  obtain ⟨O, hO8, wO, hOl, hOb⟩ := fold H hr2 hi2 hC ⟨hfl, hℓ, hff, haℓ, hlℓ, hin⟩ k (Nat.le_refl _)
  unfold chainDig
  rw [msg_len, show 128 * (k + 1) / 128 = k + 1 by omega, hOb]
  have hd : NearSpecV3.SHA512.digestBytes O = (wbytes O).map UInt8.ofNat := by
    have e : ∀ l : List UInt8, l.map (UInt8.ofNat ∘ UInt8.toNat) = l := fun l => by
      induction l with
      | nil => rfl
      | cons x l ih => simp only [List.map_cons, ih, Function.comp, UInt8.ofNat_toNat]
    rw [← digestBytes_map, List.map_map, e]
  rw [hd, wbytes_eq, hO8, List.map_map, ← List.map_take, List.take_range]
  simp only [show min 42 (8 * 8) = 42 from rfl]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.1 hj
  simp only [Function.comp]
  rw [dg_words H hr2 hℓ hlℓ hO8 wO hOl j (by omega)]

omit hi2 hC in
/-- **A fixed-content run's row carries `SE`'s padded block** (its `SHB` receive's sender). -/
theorem blk_eq (hb : NoSendOn B_SHB xtape) {s : Se.HSpec} (hs : s ∈ Se.hashes) {r i : Nat}
    (hr : r < tr.height 2) (ha : shC tr r "act" = 1) (hfx1 : shC tr r "fx" = 1)
    (hhid : shC tr r "hid" = s.hid) (hbi : shC tr r "bi" = i) :
    i < Se.nBlk s.msg ∧ blkOf tr r = (List.range 128).map fun j => ev tr 0 0 pub (Se.blkE s.msg i j) := by
  have hm1 : (Sh.c "act" * Sh.c "fx").eval tr 2 r pub = 1 := by
    have : ev tr 2 r pub (Sh.c "act" * Sh.c "fx") = 1 := by
      simp only [evMul]; show shC tr r "act" * shC tr r "fx" % 2013265921 = 1; rw [ha, hfx1]
    have := eval_of_ev (e := Sh.c "act" * Sh.c "fx") (t := 2) (r := r) this (by decide); rw [this]; rfl
  obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, hmp⟩ :=
    recv_sender H sh_lt hr shbRcv_mem rfl (by rw [shbRcv, multNat_one hm1]; exact Nat.one_pos)
  obtain ⟨rfl, hiS⟩ := shb_sender hb ht' hi' hb' hs'
  obtain ⟨s', hsm, hfx', kk, hkk, rfl⟩ := se_shb hiS hb'
  -- the sender is `SE` row 0
  have hmul : ev tr 0 r' pub s'.mul = 1 := by
    by_cases he : s'.mul.eval tr 0 r' pub = 1
    · show (s'.mul.eval tr 0 r' pub).toNat = 1; rw [he]; rfl
    · exfalso; simp [snd, Interaction.multNat, Interaction.multNat.go, he] at hmp
  obtain rfl := mul_row0 s' hsm r' hmul
  simp only [Interaction.msgVal, shbRcv, snd, rcv, List.map_cons, List.cons.injEq] at hmv
  obtain ⟨e1, e2, e3⟩ := hmv
  have hn := nBlk_pos s'.msg
  have ehid : s'.hid = s.hid := by
    have := fp_ev e1
    change ev tr 0 0 pub (K s'.hid) = ev tr 2 r pub (Sh.c "hid") at this
    rw [evK, Nat.mod_eq_of_lt (by have := hid_lt s' hsm; omega)] at this
    rw [this]; exact hhid
  obtain rfl := hid_inj hsm hs ehid
  have eki : kk = i := by
    have e2' := fp_ev e2
    change ev tr 0 0 pub (K kk) = ev tr 2 r pub (Sh.c "bi") at e2'
    have hml := msg_len_le s' hsm
    have h3 : Se.nBlk s'.msg ≤ 3 := by
      simp only [Se.nBlk, Se.padE, List.length_append, List.length_singleton, List.length_replicate,
        List.length_map, List.length_range]
      omega
    rw [evK, Nat.mod_eq_of_lt (by omega)] at e2'
    rw [e2']; exact hbi
  subst eki
  refine ⟨hkk, ?_⟩
  -- the block bytes, limb by limb
  obtain ⟨hB0, -⟩ := blk_ranges H hr2 hr ha
  have hB : ∀ k < 128, ev tr 2 r pub (Sh.blkB k) < 256 := fun k hk => by
    show shC tr r "blk" k < 256; exact hB0 k hk
  have hE : ∀ k < 128, ev tr 0 0 pub (Se.blkE s'.msg kk k) < 256 := by
    intro k hk
    unfold Se.blkE
    rw [List.getD_eq_getElem?_getD]
    cases h : (Se.padE s'.msg)[128 * kk + k]? with
    | none => show ev tr 0 0 pub (.const 0) < 256; simp
    | some x => exact se_pad_lt H hr2 s' hsm x (List.mem_of_getElem? h)
  simp only [Sh.limbs43, List.map_map] at e3
  have hl := map_range_eq e3
  simp only [Function.comp] at hl
  unfold blkOf
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.1 hj
  by_cases hq : j / 3 < 42
  · have h1 := fp_ev (hl (j / 3) (by omega))
    simp only [hq, ite_true] at h1
    change ev tr 0 0 pub _ = ev tr 2 r pub _ at h1
    rw [ev_limb3 (hE _ (by omega)) (hE _ (by omega)) (hE _ (by omega)),
      ev_limb3 (hB _ (by omega)) (hB _ (by omega)) (hB _ (by omega))] at h1
    obtain ⟨a0, a1, a2⟩ := limb3_inj (hE _ (by omega)) (hE _ (by omega)) (hE _ (by omega))
      (hB _ (by omega)) (hB _ (by omega)) (hB _ (by omega)) h1
    have : j = 3 * (j / 3) ∨ j = 3 * (j / 3) + 1 ∨ j = 3 * (j / 3) + 2 := by omega
    rcases this with h | h | h <;> rw [h]
    · exact a0.symm
    · exact a1.symm
    · exact a2.symm
  · have h1 := fp_ev (hl 42 (by omega))
    simp only [show ¬ (42 < 42) by omega, ite_false] at h1
    change ev tr 0 0 pub _ = ev tr 2 r pub _ at h1
    rw [ev_limb2 (hE _ (by omega)) (hE _ (by omega)), ev_limb2 (hB _ (by omega)) (hB _ (by omega))] at h1
    obtain ⟨a0, a1⟩ := limb2_inj (hE _ (by omega)) (hE _ (by omega)) (hB _ (by omega)) (hB _ (by omega)) h1
    have : j = 126 ∨ j = 127 := by omega
    rcases this with h | h <;> rw [h]
    · exact a0.symm
    · exact a1.symm

/-- **Every hash `SE` demands holds** (module doc). -/
theorem sh_sound (hd : NoRecvOn B_SHD xtape) (hb : NoSendOn B_SHB xtape) :
    ∀ s ∈ Se.hashes, ev tr 0 0 pub s.mul = 1 → HashOK pub tr s := by
  intro s hs hm
  obtain ⟨ℓ, hℓ, hl, hhid, hfx, hbi, hdg⟩ := lst_of H hr2 hd hs hm
  obtain ⟨f, hfl, hff, hin⟩ := walk H ℓ hℓ (lst_act H hℓ hl)
  have hR : ShRun tr f ℓ := ⟨hfl, hℓ, hff, lst_act H hℓ hl, hl, hin⟩
  have hact : ∀ i, i ≤ ℓ - f → shC tr (f + i) "act" = 1 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact fst_act H (by omega) hff
    · exact (hin (f + i) (by omega) (by omega)).1
  refine ⟨msg tr f (ℓ - f + 1), by rw [msg_len]; omega, by rw [msg_len]; omega, ?_, ?_, ?_⟩
  · intro x hx
    simp only [msg, List.mem_flatMap, List.mem_range] at hx
    obtain ⟨i, hi, hx⟩ := hx
    simp only [blkOf, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (blk_ranges H hr2 (by omega) (hact i (by omega))).1 j hj
  · intro hf
    have hfx1 : shC tr ℓ "fx" = 1 := by rw [hfx, hf]; rfl
    have hbiℓ := hbi hf
    have hlen : ℓ - f = Se.nBlk s.msg - 1 := by
      have := run_bi H hR (ℓ - f) (by omega)
      rw [show f + (ℓ - f) = ℓ by omega, hbiℓ] at this
      exact this.symm
    have hrow : ∀ i, i ≤ ℓ - f →
        blkOf tr (f + i) = (List.range 128).map fun j => ev tr 0 0 pub (Se.blkE s.msg i j) := by
      intro i hi
      have hfxi : shC tr (f + i) "fx" = 1 := by
        rw [run_fx H hR i (by omega), ← run_fx H hR (ℓ - f) (by omega), show f + (ℓ - f) = ℓ by omega, hfx1]
      have hhi : shC tr (f + i) "hid" = s.hid := by
        rw [run_hid H hr2 hi2 hC hR i (by omega), ← run_hid H hr2 hi2 hC hR (ℓ - f) (by omega),
          show f + (ℓ - f) = ℓ by omega, hhid]
      exact (blk_eq H hr2 hb hs (by omega) (hact i hi) hfxi hhi (run_bi H hR i (by omega))).2
    have hn := nBlk_pos s.msg
    unfold msg
    rw [show ℓ - f + 1 = Se.nBlk s.msg by omega]
    rw [← flat_blocks (0 : Nat) (Se.nBlk s.msg) ((Se.padE s.msg).map (ev tr 0 0 pub))
      (by rw [List.length_map, padE_len])]
    show (List.map _ (List.range _)).flatten = (List.map _ (List.range _)).flatten
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.1 hi
    rw [hrow i (by omega)]
    apply List.map_congr_left
    intro j _
    rw [getD_map_ev]; rfl
  · rw [run_digest H hr2 hi2 hC hR, digOf]
    apply List.map_congr_left
    intro j hj
    rw [hdg j (List.mem_range.1 hj)]

end

#print axioms sh_sound

end M5T1.ShSem
