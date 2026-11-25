import M5T1.ShSem3

/-!
# M5T1.ShSem4 — each active `ACC` row is one chip compression (F-7, from `AccSem4`)

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

/-- The 32 limb triples of `ACC`'s compression. -/
def WS : List Acc.W3 := Sh.hW ++ Sh.blockW ++ Sh.oW

def trip (k : Nat) : List Expr :=
  let w := WS.getD k (0, 0, 0)
  [w.1, w.2.1, w.2.2]

theorem comp_eq (g cid : Expr) : Acc.comp g cid WS =
    (List.range 16).map fun m => rcv B_IF384 g ([cid, K m] ++ trip (2 * m) ++ trip (2 * m + 1)) := by
  unfold Acc.comp
  apply List.map_congr_left
  intro m _
  rfl

theorem WS_len : WS.length = 32 := by decide

theorem WS_h {k : Nat} (hk : k < 8) : WS.getD k (0, 0, 0) = Sh.limbW "h" k := by
  simp only [WS, Sh.hW, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hk]
  rfl

theorem WS_b {k : Nat} (hk : k < 16) : WS.getD (8 + k) (0, 0, 0) = Acc.wordOf Sh.blkB Sh.blkS k := by
  simp only [WS, Sh.hW, Sh.blockW, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]
  simp [hk]

theorem WS_o {k : Nat} (hk : k < 8) : WS.getD (24 + k) (0, 0, 0) = Sh.limbW "o" k := by
  simp only [WS, Sh.hW, Sh.blockW, Sh.oW, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp [show 24 + k - 8 - 16 = k by omega, hk]

/-- An active row's facts about one compression. -/
def RowOK (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop :=
  ∃ hw bw : List Nat, hw.length = 8 ∧ bw.length = 16 ∧ W64 bw ∧
    (∀ t < 8, Acc.wlimbs (hw.getD t 0) = [shC tr r "h" (3 * t), shC tr r "h" (3 * t + 1),
      shC tr r "h" (3 * t + 2)]) ∧
    (∀ t < 8, Acc.wlimbs ((cW hw bw).getD t 0) = [shC tr r "o" (3 * t), shC tr r "o" (3 * t + 1),
      shC tr r "o" (3 * t + 2)]) ∧
    (∀ w < 16, Acc.wlimbs (bw.getD w 0) = (trip (8 + w)).map (ev tr 2 r pub))

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hi2 : NoSendOn B_IF384 xtape) (hC : ChipOK tr)
include H hi2 hC

theorem row_ok {r : Nat} (hr : r < tr.height 2) (ha : shC tr r "act" = 1) : RowOK tr pub r := by
  obtain ⟨chip, hcon, hmem⟩ := hC
  let lv : Nat → List Nat := fun k => (trip k).map (ev tr 2 r pub)
  let ws : List (List Nat) := (List.range 32).map lv
  have hws : ∀ k < 32, ws.getD k zeroL = lv k := by
    intro k hk
    simp [ws, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  have hge : (Sh.c "act").eval tr 2 r pub = 1 := by
    have := eval_of_ev (pub := pub) (e := Sh.c "act") (t := 2) (r := r) (by rw [evSc, ha]) (by decide)
    rw [this]; rfl
  have hin : ∀ x ∈ compRecv (shC tr r "cid") ws, x ∈ chip := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    have hm16 := List.mem_range.1 hm
    have hI : rcv B_IF384 (Sh.c "act") ([Sh.c "cid", K m] ++ trip (2 * m) ++ trip (2 * m + 1)) ∈
        ((Se.fullSe xtape).tables[2]'sh_lt).interactions := by
      show _ ∈ Sh.table.interactions
      apply mi1
      show _ ∈ Acc.comp (Sh.c "act") (Sh.c "cid") WS
      rw [comp_eq]
      exact List.mem_map.2 ⟨m, hm, rfl⟩
    obtain ⟨t', r', ht', hr', i', hi', hb', hs', hmv, hmp⟩ :=
      recv_sender H sh_lt hr hI rfl (by rw [multNat_one hge]; decide)
    obtain ⟨rfl, rfl⟩ := if_sender hi2 ht' hi' hb' hs'
    -- the stub's row sends (multiplicity bit 1)
    have hnz : nv tr 3 r' 0 ≠ 0 := by
      intro h0
      have : (Expr.col 0 false).eval tr 3 r' pub = 0 := by
        apply Fp.toNat_inj.1; exact h0
      simp [Interaction.multNat, Interaction.multNat.go, stubIx, this] at hmp
      exact absurd hmp (by decide)
    have hrow := hmem r' hr' hnz
    have key : chipRow tr r' =
        ⟨shC tr r "cid", m, ws.getD (2 * m) zeroL, ws.getD (2 * m + 1) zeroL⟩ := by
      rw [hws _ (by omega), hws _ (by omega)]
      simp only [Interaction.msgVal, stubIx, rcv, trip, List.map_append, List.map_cons, List.map_nil,
        List.map_map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
        List.cons.injEq] at hmv
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := hmv
      have hK : ((K m).eval tr 2 r pub).toNat = m := by
        show ev tr 2 r pub (K m) = m
        rw [evK, Nat.mod_eq_of_lt (by omega)]
      simp only [chipRow, nv, lv, trip, List.map_cons, List.map_nil]
      have g1 : (tr.cell 3 r' 1).toNat = shC tr r "cid" := congrArg Fp.toNat e1
      have g2 : (tr.cell 3 r' 2).toNat = m := (congrArg Fp.toNat e2).trans hK
      have g3 : (tr.cell 3 r' 3).toNat = _ := congrArg Fp.toNat e3
      have g4 : (tr.cell 3 r' 4).toNat = _ := congrArg Fp.toNat e4
      have g5 : (tr.cell 3 r' 5).toNat = _ := congrArg Fp.toNat e5
      have g6 : (tr.cell 3 r' 6).toNat = _ := congrArg Fp.toNat e6
      have g7 : (tr.cell 3 r' 7).toNat = _ := congrArg Fp.toNat e7
      have g8 : (tr.cell 3 r' 8).toNat = _ := congrArg Fp.toNat e8
      rw [g1, g2, g3, g4, g5, g6, g7, g8]; rfl
    rw [key] at hrow; exact hrow
  obtain ⟨hw, bw, h8, h16, -, wb, e⟩ :=
    comp_sound compressOK_cW hcon (by simp [ws]) hin
  have hl : (hw ++ bw ++ cW hw bw).length = 32 := by
    simp [h8, h16, (compressOK_cW hw bw).1]
  have hk : ∀ k < 32, lv k = Acc.wlimbs ((hw ++ bw ++ cW hw bw).getD k 0) := by
    intro k hk
    rw [← hws k hk, e, getD_map_wl _ (by rw [hl]; exact hk)]
  refine ⟨hw, bw, h8, h16, wb, fun t ht => ?_, fun t ht => ?_, fun w hw' => ?_⟩
  · have := hk t (by omega)
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD] at this
    rw [← this]
    simp only [lv, trip, WS_h ht, Sh.limbW, List.map_cons, List.map_nil, evSc]
  · have := hk (24 + t) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [h8, h16]),
      ← List.getD_eq_getElem?_getD] at this
    simp only [List.length_append, h8, h16, show 24 + t - (8 + 16) = t by omega] at this
    rw [← this]
    simp only [lv, trip, WS_o ht, Sh.limbW, List.map_cons, List.map_nil, evSc]
  · have := hk (8 + w) (by omega)
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega),
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD] at this
    simp only [h8, show 8 + w - 8 = w by omega] at this
    exact this.symm
end

end M5T1.ShSem
