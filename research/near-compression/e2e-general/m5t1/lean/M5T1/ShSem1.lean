import M5T1.ShDef

/-!
# M5T1.ShSem1 — `SH` evaluation and bus facts on the STATE engine half's AIR (F-7, part of `ShSem`)

The AIR is `Se.fullSe xtape = [SE, RNG, SH, chip stub, XTAPE]`. Bus facts: the only `SHD` receiver
is `SH`'s `lst` receive, the only `SHB` senders are `SE`'s hash sends (`Se.hashes`), the only
`IF384` sender is the chip stub (table 3), only `RNG` sends on `RNG` (with a tape that sends
nothing there).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.ShSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.ShDef
open M5T1.AccSem (evAdd evMul evSub evK evOne evZero evFirst0 evFirstS evTrans evPub gate_eq
  bool_le NoRecv NoRecvOn noRecv_spec tape_receiver)

abbrev Tp := List (Nat × Bool × List Nat)

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}
theorem evSc (s : String) (j : Nat) : ev tr 2 r pub (Sh.c s j) = shC tr r s j := rfl
theorem evSn {s : String} {j : Nat} (h : r + 1 < tr.height 2) :
    ev tr 2 r pub (Sh.n s j) = shC tr (r + 1) s j := by
  show ((tr.cell 2 ((r + 1) % tr.height 2) _)).toNat = _
  rw [Nat.mod_eq_of_lt h]; rfl
theorem shC_lt (s : String) (j : Nat) : shC tr r s j < 2013265921 := Fp.toNat_lt _
end

/-! ## The AIR's tables -/

section
variable {xtape : Tp}

theorem fullSe_tables (xtape : Tp) :
    (Se.fullSe xtape).tables = [Se.table, Rng.table, Sh.table, chipStub, tapeTable xtape] := rfl

theorem fullSe_len : (Se.fullSe xtape).tables.length = 5 := rfl

theorem sh_lt : 2 < (Se.fullSe xtape).tables.length := by rw [fullSe_len]; decide
theorem se_lt : 0 < (Se.fullSe xtape).tables.length := by rw [fullSe_len]; decide

theorem tbl_eq (t : Nat) (ht : t < (Se.fullSe xtape).tables.length) :
    (Se.fullSe xtape).tables[t]'ht =
      ([Se.table, Rng.table, Sh.table, chipStub, tapeTable xtape].getD t default) := by
  simp only [fullSe_tables] at ht ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl

/-! ## `SE`'s interactions on the new buses -/

theorem ix5_noSHB : (Se.interactions5.all fun i => !(i.bus == B_SHB)) = true := by decide +kernel
theorem ix5_noSHD : (Se.interactions5.all fun i => !(i.bus == B_SHD)) = true := by decide +kernel
theorem ix5_noIF : (Se.interactions5.all fun i => !(i.bus == B_IF384)) = true := by decide +kernel

/-- The interactions of `interactions7` that are not hash interactions are `RNG` receives. -/
def rngPart : List Interaction :=
  [rcv B_RNG .isFirst [Se.c "tgi" + 1], rcv B_RNG .isFirst [Se.c "tgi"], rcv B_RNG .isFirst [Se.c "tgo"]] ++
  (Se.byteGroups.flatMap fun (s, w) => (List.range w).map fun j => rcv B_RNG .isFirst [Se.c s j])

theorem ix7_eq : Se.interactions7 = rngPart ++ Se.hashes.flatMap Se.hashIx := rfl

theorem rngPart_bus : ∀ i ∈ rngPart, i.bus = B_RNG := by
  intro i hi
  simp only [rngPart, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap,
    List.mem_map, List.mem_range] at hi
  rcases hi with (rfl | rfl | rfl) | ⟨_, _, j, _, rfl⟩ <;> rfl

theorem hashIx_bus (s : Se.HSpec) : ∀ i ∈ Se.hashIx s, i.bus = B_SHB ∨ i.bus = B_SHD := by
  intro i hi
  unfold Se.hashIx at hi
  split at hi
  · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hi
    rcases hi with ⟨k, _, rfl⟩ | rfl
    · exact .inl rfl
    · exact .inr rfl
  · simp only [List.mem_singleton] at hi; subst hi; exact .inr rfl

theorem hashIx_send (s : Se.HSpec) : ∀ i ∈ Se.hashIx s, i.send = true := by
  intro i hi
  unfold Se.hashIx at hi
  split at hi
  · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hi
    rcases hi with ⟨k, _, rfl⟩ | rfl <;> rfl
  · simp only [List.mem_singleton] at hi; subst hi; rfl

theorem all_mem {l : List Interaction} {p : Interaction → Bool} (h : l.all p = true) {i : Interaction}
    (hi : i ∈ l) : p i = true := List.all_eq_true.1 h i hi

/-- **`SE`'s `SHB` interactions are the fixed hashes' block sends.** -/
theorem se_shb {i : Interaction} (hi : i ∈ Se.table.interactions) (hb : i.bus = B_SHB) :
    ∃ s ∈ Se.hashes, s.fx = true ∧ ∃ k < Se.nBlk s.msg,
      i = snd B_SHB s.mul (K s.hid :: K k :: Sh.limbs43 (Se.blkE s.msg k)) := by
  change i ∈ Se.interactions5 ++ Se.interactions7 at hi
  rcases List.mem_append.1 hi with hi | hi
  · have := all_mem ix5_noSHB hi; simp [hb] at this
  rw [ix7_eq] at hi
  rcases List.mem_append.1 hi with hi | hi
  · have := rngPart_bus i hi; rw [hb] at this; exact absurd this (by decide)
  obtain ⟨s, hs, hi⟩ := List.mem_flatMap.1 hi
  refine ⟨s, hs, ?_⟩
  unfold Se.hashIx at hi
  split at hi
  · rename_i hfx
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hi
    rcases hi with ⟨k, hk, rfl⟩ | rfl
    · exact ⟨hfx, k, hk, rfl⟩
    · simp [snd, B_SHB, B_SHD] at hb
  · simp only [List.mem_singleton] at hi; subst hi; simp [snd, B_SHB, B_SHD] at hb

/-- **`SE`'s `SHD` interactions are the hashes' digest sends.** -/
theorem se_shd {i : Interaction} (hi : i ∈ Se.table.interactions) (hb : i.bus = B_SHD) :
    ∃ s ∈ Se.hashes, i = snd B_SHD s.mul ((if s.fx then [K s.hid, K 1, K (Se.nBlk s.msg - 1)]
      else [K s.hid, K 0, s.nb]) ++ Rb.limbs s.dig) := by
  change i ∈ Se.interactions5 ++ Se.interactions7 at hi
  rcases List.mem_append.1 hi with hi | hi
  · have := all_mem ix5_noSHD hi; simp [hb] at this
  rw [ix7_eq] at hi
  rcases List.mem_append.1 hi with hi | hi
  · have := rngPart_bus i hi; rw [hb] at this; exact absurd this (by decide)
  obtain ⟨s, hs, hi⟩ := List.mem_flatMap.1 hi
  refine ⟨s, hs, ?_⟩
  unfold Se.hashIx at hi
  split at hi
  · rename_i hfx
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hi
    rcases hi with ⟨k, hk, rfl⟩ | rfl
    · simp [snd, B_SHB, B_SHD] at hb
    · simp [hfx]
  · rename_i hfx
    simp only [List.mem_singleton] at hi; subst hi; simp [hfx]

/-- The interactions of `SE` that are sends on `IF384`, `SHD` receives: none. -/
theorem se_noIF {i : Interaction} (hi : i ∈ Se.table.interactions) (hb : i.bus = B_IF384) : False := by
  change i ∈ Se.interactions5 ++ Se.interactions7 at hi
  rcases List.mem_append.1 hi with hi | hi
  · have := all_mem ix5_noIF hi; simp [hb] at this
  rw [ix7_eq] at hi
  rcases List.mem_append.1 hi with hi | hi
  · have := rngPart_bus i hi; rw [hb] at this; exact absurd this (by decide)
  obtain ⟨s, _, hi⟩ := List.mem_flatMap.1 hi
  rcases hashIx_bus s i hi with h | h <;> rw [hb] at h <;> exact absurd h (by decide)

theorem se_recv_SHD {i : Interaction} (hi : i ∈ Se.table.interactions) (hb : i.bus = B_SHD)
    (hs : i.send = false) : False := by
  obtain ⟨s, _, rfl⟩ := se_shd hi hb
  simp [snd] at hs

/-! ## Who sends / receives -/

/-- The `SHD` receive of `SH`. -/
def shdRcv : Interaction := rcv B_SHD (Sh.c "lst") ([Sh.c "hid", Sh.c "fx", Sh.c "bi"] ++ Sh.dgLimbs)

/-- The `SHB` receive of `SH`. -/
def shbRcv : Interaction := rcv B_SHB (Sh.c "act" * Sh.c "fx") (Sh.c "hid" :: Sh.c "bi" :: Sh.limbs43 Sh.blkB)

theorem sh_shd : ∀ i ∈ Sh.table.interactions, i.bus = B_SHD → i = shdRcv := by decide +kernel
theorem sh_shb : ∀ i ∈ Sh.table.interactions, i.bus = B_SHB → i = shbRcv := by decide +kernel

theorem shdRcv_mem : shdRcv ∈ Sh.table.interactions := by
  show _ ∈ Sh.interactions
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_cons_self ..)))))

theorem shbRcv_mem : shbRcv ∈ Sh.table.interactions := by
  show _ ∈ Sh.interactions
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))

/-- **The only `SHD` receiver is `SH`'s `lst` receive.** -/
theorem shd_receiver (hd : NoRecvOn B_SHD xtape) {t : Nat}
    (ht : t < (Se.fullSe xtape).tables.length) {i : Interaction}
    (hi : i ∈ ((Se.fullSe xtape).tables[t]'ht).interactions) (hb : i.bus = B_SHD)
    (hs : i.send = false) : t = 2 ∧ i = shdRcv := by
  have h5 : t < 5 := fullSe_len (xtape := xtape) ▸ ht
  rw [tbl_eq t ht] at hi
  obtain _ | _ | _ | _ | _ | t := t
  · exact (se_recv_SHD hi hb hs).elim
  · exact (noRecv_spec (by decide +kernel : NoRecv Rng.table B_SHD = true) hi hb hs).elim
  · exact ⟨rfl, sh_shd i hi hb⟩
  · exact (noRecv_spec (by decide +kernel : NoRecv chipStub B_SHD = true) hi hb hs).elim
  · exact (tape_receiver hd hi hb hs).elim
  · omega

/-- **The only `SHB` senders are `SE`'s.** -/
theorem shb_sender (hd : NoSendOn B_SHB xtape) {t : Nat}
    (ht : t < (Se.fullSe xtape).tables.length) {i : Interaction}
    (hi : i ∈ ((Se.fullSe xtape).tables[t]'ht).interactions) (hb : i.bus = B_SHB)
    (hs : i.send = true) : t = 0 ∧ i ∈ Se.table.interactions := by
  have h5 : t < 5 := fullSe_len (xtape := xtape) ▸ ht
  rw [tbl_eq t ht] at hi
  obtain _ | _ | _ | _ | _ | t := t
  · exact ⟨rfl, hi⟩
  · exact (noSend_spec (by decide +kernel : NoSend Rng.table B_SHB = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Sh.table B_SHB = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend chipStub B_SHB = true) hi hb hs).elim
  · exact (tape_sender hd hi hb hs).elim
  · omega

/-- **The only `IF384` sender is the chip stub** (table 3). -/
theorem if_sender (hi2 : NoSendOn B_IF384 xtape) {t : Nat}
    (ht : t < (Se.fullSe xtape).tables.length) {i : Interaction}
    (hi : i ∈ ((Se.fullSe xtape).tables[t]'ht).interactions) (hb : i.bus = B_IF384)
    (hs : i.send = true) : t = 3 ∧ i = stubIx := by
  have h5 : t < 5 := fullSe_len (xtape := xtape) ▸ ht
  rw [tbl_eq t ht] at hi
  obtain _ | _ | _ | _ | _ | t := t
  · exact (se_noIF hi hb).elim
  · exact (noSend_spec (by decide +kernel : NoSend Rng.table B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Sh.table B_IF384 = true) hi hb hs).elim
  · exact ⟨rfl, List.mem_singleton.1 hi⟩
  · exact (tape_sender hi2 hi hb hs).elim
  · omega

end

end M5T1.ShSem
