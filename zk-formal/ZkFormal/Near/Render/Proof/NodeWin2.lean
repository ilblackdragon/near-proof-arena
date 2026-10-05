import ZkFormal.Near.Render.Proof.NodeWin1

/-!
# ZkFormal.Near.Render.Proof.NodeWin2 — branch windows: slot, index, last-window flag
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-- An element of the enumerated present children: its slot, and its index = present children below. -/
theorem present_at : ∀ (Q : List Kid) (s : Nat) (P : List (Kid × Nat)),
    P = (Q.zip (List.range' s Q.length)).filter (fun (k, _) => k ≠ .none) →
    ∀ w k j, P[w]? = some (k, j) →
      s ≤ j ∧ j < s + Q.length ∧ Q.getD (j - s) .none = k ∧ k ≠ .none ∧ popK (Q.take (j - s)) = w
  | [], s, P, hP, w, k, j, h => by subst hP; simp at h
  | q :: Q, s, P, hP, w, k, j, h => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filter_cons] at hP
    by_cases hq : q = .none
    · simp only [hq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false] at hP
      have := present_at Q (s + 1) P hP w k j h
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_, this.2.2.2.1, ?_⟩
      · rw [show j - s = (j - (s + 1)) + 1 by omega, List.getD_cons_succ]; exact this.2.2.1
      · rw [show j - s = (j - (s + 1)) + 1 by omega, List.take_succ_cons]
        simp only [popK, List.filter_cons, hq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
        exact this.2.2.2.2
    · simp only [hq, ne_eq, not_false_eq_true, decide_true, ite_true] at hP
      subst hP
      cases w with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [popK, hq]
      | succ w =>
        simp only [List.getElem?_cons_succ] at h
        have := present_at Q (s + 1) _ rfl w k j h
        refine ⟨by omega, by simp only [List.length_cons]; omega, ?_, this.2.2.2.1, ?_⟩
        · rw [show j - s = (j - (s + 1)) + 1 by omega, List.getD_cons_succ]; exact this.2.2.1
        · rw [show j - s = (j - (s + 1)) + 1 by omega, List.take_succ_cons]
          simp only [popK, List.filter_cons, hq, ne_eq, not_false_eq_true, decide_true, ite_true, List.length_cons]
          have := this.2.2.2.2; simp only [popK, ne_eq] at this ⊢; omega

theorem branch_win (I : Info) (kids : List Kid) (hl : kids.length = 16) (w : Win)
    (h : F.ch w ∈ branchWins I kids) :
    ∃ j k, j < 16 ∧ kids.getD j .none = k ∧ k ≠ .none ∧ w = kidWin I k (popK (kids.take j))
      (popK (kids.take j) + 1 = popK kids) (some j) := by
  rw [branchWins_eq] at h
  unfold winsOf at h
  rw [List.mem_map] at h
  obtain ⟨⟨⟨k, j⟩, t⟩, hmem, he⟩ := h
  obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.1 hmem
  simp only [List.getElem_zip, List.getElem_range', Nat.zero_add, Prod.mk.injEq] at hx
  obtain ⟨hx1, rfl⟩ := hx
  have hP : (presentOf kids)[i]? = some (k, j) := by
    rw [List.getElem?_eq_getElem (by simpa using hi)]; rw [hx1]
  have := present_at kids 0 (presentOf kids) (by unfold presentOf; rw [List.range_eq_range']) i k j hP
  simp only [Nat.sub_zero, Nat.zero_add] at this
  obtain ⟨_, h2, h3, h4, h5⟩ := this
  refine ⟨j, k, by omega, h3, h4, ?_⟩
  simp only [F.ch.injEq] at he
  rw [← he, h5, popK_eq, Nat.one_mul]

/-- Present children below slot `j` as a bit sum. -/
theorem below_eq (kids : List Kid) (j : Nat) (hj : j ≤ kids.length) :
    ((List.range j).map fun i => bitOf (bitmapOf kids 0) i).sum = popK (kids.take j) := by
  rw [← sum_kidBit (kids.take j) j (by simp; omega)]
  congr 1
  apply List.map_congr_left; intro i hi
  rw [bitOf_bitmap]
  have hi' := List.mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi']

theorem kidWin_w (I : Info) (k : Kid) (w : Nat) (l : Bool) (s : Option Nat) :
    (kidWin I k w l s).w = w ∧ (kidWin I k w l s).lastw = l ∧ (kidWin I k w l s).slot = s := by
  cases k <;> exact ⟨rfl, rfl, rfl⟩

/-- A child window: the extension's (index `0`, last, no slot) or a branch's (slot `j`, index = present
children below `j`, last iff it is the last present child). -/
theorem ch_facts (I : Info) (n : Nat) (nr : NodeRec) (w : Win) (hf : F.ch w ∈ fieldsOf I n nr) (hw : nr.wf) :
    ((typeOf nr).2.1 = 1 ∧ (typeOf nr).2.2.1 = 0 ∧ (typeOf nr).2.2.2 = 0 ∧ w.w = 0 ∧ w.lastw = true ∧ w.slot = none) ∨
    ((typeOf nr).2.1 = 0 ∧ (typeOf nr).2.2.1 + (typeOf nr).2.2.2 = 1 ∧ ∃ j0, j0 < 16 ∧ w.slot = some j0 ∧
      bitOf (bmvOf nr) j0 = 1 ∧ w.w = ((List.range j0).map fun i => bitOf (bmvOf nr) i).sum ∧
      (w.lastw = true ↔ w.w + 1 = ((List.range 16).map fun i => bitOf (bmvOf nr) i).sum)) := by
  cases nr with
  | leaf k v m => simp [fieldsOf] at hf
  | ext k kid m =>
    simp [fieldsOf] at hf; subst hf
    left; have := kidWin_w I kid 0 true none; exact ⟨rfl, rfl, rfl, this.1, this.2.1, this.2.2⟩
  | branch v kids m =>
    right
    have hb' : F.ch w ∈ branchWins I kids := by cases v <;> simpa [fieldsOf, NodeRec.kids] using hf
    obtain ⟨j0, k, hj0, hk, hkn, rfl⟩ := branch_win I kids hw.1 w hb'
    have hbel := below_eq kids j0 (by rw [hw.1]; omega)
    have hpop := below_eq kids 16 (by rw [hw.1]; exact Nat.le_refl _)
    rw [List.take_of_length_le (by rw [hw.1]; exact Nat.le_refl _)] at hpop
    have hkw := kidWin_w I k (popK (kids.take j0)) (decide (popK (kids.take j0) + 1 = popK kids)) (some j0)
    simp only [bmvOf, isLE, Bool.false_eq_true, ite_false, NodeRec.kids]
    refine ⟨by cases v <;> rfl, by cases v <;> rfl, j0, hj0, hkw.2.2, ?_, ?_, ?_⟩
    · rw [bitOf_bitmap, hk]; cases k <;> simp_all [kidBit]
    · rw [hkw.1, hbel]
    · rw [hkw.2.1, hkw.1, hpop]; simp

/-- The row-local window constraints. -/
abbrev wLoc : List Expr :=
  [ .mul Node.winE (sub (c Node.b) (c (Node.reg 0))), .mul Node.winE (sub (c Node.pb) (c (Node.preg 0))),
    .mul (c Node.rv) (Dsl.not (c Node.sCH)),
    sub (c Node.gD) (.add (c Node.gP) (.mul Node.vhStart (c Node.tv))),
    .mul (c Node.gP) (sub (c Node.dI) (mid K_NPRE (c Node.cid))),
    .mul (c Node.gP) (sub (c Node.dL) (c Node.clen)),
    .mul Node.valStart (sub (c Node.dI) (mid K_VPRE (c Node.nid))),
    .mul Node.valStart (sub (c Node.dL) (k 72)),
    mul3 Node.isBr (c Node.sCH) (sub (sum ((List.range 16).map fun i => c (Node.jj i))) (k 1)),
    mul3 Node.isBr (c Node.sCH) (sub (sum ((List.range 16).map fun i => .mul (c (Node.jj i)) (c (Node.bm i)))) (k 1)),
    mul3 Node.isBr (c Node.sCH) (sub Node.belowE (c Node.w)),
    .mul (c Node.te) (.mul (c Node.sCH) (c Node.w)),
    mul3 (c Node.lastw) (c Node.sCH) (sub (.add (c Node.w) (k 1)) Node.nWinE) ]

set_option maxHeartbeats 8000000 in
theorem wLoc_rec (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) (hf : r.f ∈ fieldsOf I r.n (I.nodeAt r.n))
    (hw : (I.nodeAt r.n).wf) (hb : r.b = (NodeLay.fbytes (I.nodeAt r.n) false r.f).getD r.idx 0)
    (hpb : r.pb = (NodeLay.fbytes (I.nodeAt r.n) true r.f).getD r.idx 0)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int) (hC : ∀ x, x < 163 → C x = (rowCell I u r x : Int)) :
    ∀ ex ∈ wLoc, ev C D fst lst trn P ex = 0 := by
  intro ex hex
  simp only [wLoc, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only at hf hb hpb hw hC
  cases f
  case vh w =>
    have hws := (win_shape I rn _ w).2 hf
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC]
    all_goals node_rc []
    all_goals simp [F.state, F.chw, F.win, digOf, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n, msgId, NodeLay.fbytes] at hb hpb ⊢
    all_goals first
      | (rw [hb]; simp [Int.add_right_neg])
      | (rw [hpb]; simp [Int.add_right_neg])
      | (rw [hws.1]; cases (I.nodeAt rn).touched <;> by_cases hj : j = 0 <;> simp [hj] <;> omega)
      | (cases hl : w.look <;> by_cases hj : j = 0 <;> simp_all [Int.add_right_neg] <;> omega)
      | trace_state
  case ch w =>
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC]
    all_goals node_rc []
    all_goals simp [F.state, F.chw, F.win, digOf, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n, msgId, NodeLay.fbytes] at hb hpb ⊢
    · rw [hb]; simp [Int.add_right_neg]
    · rw [hpb]; simp [Int.add_right_neg]
    all_goals try (cases hl : w.look <;> by_cases hj : j = 0 <;> simp [hj, hl, Int.add_right_neg] <;> omega)
    all_goals
      rcases ch_facts I rn _ w hf hw with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, j0, hj0, h3, h4, h5, h6⟩
      · simp [h1, h2, h3, h4, h5, h6]
      · simp only [h1, h3, Option.some.injEq]
        have ht : ((typeOf (I.nodeAt rn)).2.2.1 = 1 ∧ (typeOf (I.nodeAt rn)).2.2.2 = 0) ∨
            ((typeOf (I.nodeAt rn)).2.2.1 = 0 ∧ (typeOf (I.nodeAt rn)).2.2.2 = 1) := by omega
        by_cases hl : w.lastw = true
        · have h6' := h6.1 hl
          rcases (show j0 = 0 ∨ j0 = 1 ∨ j0 = 2 ∨ j0 = 3 ∨ j0 = 4 ∨ j0 = 5 ∨ j0 = 6 ∨ j0 = 7 ∨ j0 = 8 ∨ j0 = 9 ∨
            j0 = 10 ∨ j0 = 11 ∨ j0 = 12 ∨ j0 = 13 ∨ j0 = 14 ∨ j0 = 15 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases ht with ⟨ha, hb2⟩ | ⟨ha, hb2⟩ <;>
          simp only [ha, hb2, hl, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, List.nil_append, ite_true, ite_false] at h4 h5 h6' ⊢ <;>
          simp <;> omega
        · have h6' : ¬ (w.w + 1 = _) := fun h => hl (h6.2 h)
          rcases (show j0 = 0 ∨ j0 = 1 ∨ j0 = 2 ∨ j0 = 3 ∨ j0 = 4 ∨ j0 = 5 ∨ j0 = 6 ∨ j0 = 7 ∨ j0 = 8 ∨ j0 = 9 ∨
            j0 = 10 ∨ j0 = 11 ∨ j0 = 12 ∨ j0 = 13 ∨ j0 = 14 ∨ j0 = 15 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases ht with ⟨ha, hb2⟩ | ⟨ha, hb2⟩ <;>
          simp only [ha, hb2, hl, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, List.nil_append, ite_true, ite_false, Bool.false_eq_true]
            at h4 h5 h6' ⊢ <;>
          simp <;> omega
  all_goals
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC]
    all_goals node_rc []
    all_goals simp [F.state, F.chw, F.win, digOf, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n, msgId, NodeLay.fbytes] at hb hpb ⊢

end NodeRow

end ZkFormal.Near.Render
