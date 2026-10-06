import ZkFormal.NearV3.Render.Node.Win

/-!
# ZkFormal.NearV3.Render.Node.Win2 — `cWindows`: lookups, child slots, window constants; assembly
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (wOf lwOf len_facts mem_len)

namespace NodeGen3

set_option maxHeartbeats 16000000 in
theorem wLoc_rec (vs : List NodeS3) (r : NRec) (hf : r.f ∈ fieldsOf (rec vs r.n).v)
    (hw : (rec vs r.n).v.wf) (hb : r.b = (fbytes (rec vs r.n).v false r.f).getD r.idx 0)
    (hpb : r.pb = (fbytes (rec vs r.n).v true r.f).getD r.idx 0)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int) (hC : ∀ x, x < 185 → C x = (rowCell vs r x : Int)) :
    ∀ ex ∈ wLoc, ev C D fst lst trn P ex = 0 := by
  intro ex hex
  simp only [wLoc, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only at hf hb hpb hw hC
  cases f
  case vh w =>
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC]
    all_goals node_rc3 []
    all_goals simp [F.state, NodeGen.F.chw, NodeGen.F.win, digOf, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY,
      Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n, msgId, fbytes, NodeGen.F.isCh, NodeGen.F.isVh] at hb hpb ⊢
    all_goals first
      | (rw [hb]; simp [Int.add_right_neg])
      | (rw [hpb]; simp [Int.add_right_neg])
      | (cases tvOf (rec vs rn).v <;> by_cases hj : j = 0 <;> simp [hj] <;> omega)
      | skip
  case ch w =>
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC]
    all_goals node_rc3 []
    all_goals simp [F.state, NodeGen.F.chw, NodeGen.F.win, digOf, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY,
      Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n, msgId, fbytes] at hb hpb ⊢
    · rw [hb]; simp [Int.add_right_neg]
    · rw [hpb]; simp [Int.add_right_neg]
    all_goals try (cases hl : w.look <;> by_cases hj : j = 0 <;> simp [hj, hl, Int.add_right_neg] <;> omega)
    all_goals
      rcases ch_facts _ w hf hw with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, j0, hj0, h3, h4, h5, h6⟩
      · simp [h1, h2, h3, h4, h5, h6]
      · simp only [h1, h3, Option.some.injEq]
        have ht : ((typeOf (rec vs rn).v).2.2.1 = 1 ∧ (typeOf (rec vs rn).v).2.2.2 = 0) ∨
            ((typeOf (rec vs rn).v).2.2.1 = 0 ∧ (typeOf (rec vs rn).v).2.2.2 = 1) := by omega
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
    all_goals node_ev3 [hC]
    all_goals node_rc3 []
    all_goals simp [F.state, NodeGen.F.chw, NodeGen.F.win, digOf, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY,
      Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n, msgId, fbytes] at hb hpb ⊢

section
variable {vs : List NodeS3} (ok : NodeOk vs) {H : Nat} (hHR : R vs + 1 ≤ H)
include ok hHR

set_option maxHeartbeats 8000000 in
theorem wTr_node {q : Nat} (hqn : q < R vs) : RowGoal vs H wTr q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off vs n + p + 1) % H = off vs n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hw := rwf ok hn
  have hidx := (fmem ok hn hp).2
  have hsr := state_range ((layN vs n).getD p default).1
  simp only [wTr, NodeV3.windowConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  simp only [mkR] at hC'
  rcases next_row hn hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · have hD' : ∀ x, x < 185 → D x = (rowCell vs (mkR vs n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    simp only [mkR] at hD'
    have hadj := lay_adj hw h1
    simp only [show layout (fieldsOf (rec vs n).v) (hplenOf (rec vs n).v) = layN vs n from rfl] at hadj
    have hsr' := state_range ((layN vs n).getD (p + 1) default).1
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals try simp only [rc70, rc71]
    all_goals node_rc3 []
    all_goals rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    all_goals first
      | (simp only [a1, a2]; simp [Int.add_right_neg]; done)
      | (simp only [a1, a2, b2n, decide_eq_true_eq]; (repeat' split) <;> omega)
      | (obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3
         clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16
         simp only [b2n, decide_eq_true_eq]; (repeat' split) <;> omega)
  · have hD' : ∀ x, x < 185 → D x = (rowCell vs (mkR vs (n + 1) 0) x : Int) := by
      intro x hx; rw [hD x hx, X_node h3, h4]
    simp only [mkR] at hD'
    have hlast := (last_iff ok hn hp).1 h1
    have hl9 := mem_len ((layN vs n).getD p default).1 (hplenOf (rec vs n).v) hlast.1
    have htag := (tag_iff ok h2 (p := 0) (by have := lay_pos (rec vs (n + 1)).v; simp only [layN]; omega)).2 rfl
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals try simp only [rc70, rc71]
    all_goals node_rc3 []
    all_goals simp only [hlast.1, hlast.2, hl9, htag, b2n]
    all_goals simp
  · have hD' : ∀ x, x < 185 → D x = (sumCell (total vs) x : Int) := by
      intro x hx; rw [hD x hx, h3, X_sum]
    have hlast := (last_iff ok hn hp).1 h1
    have hl9 := mem_len ((layN vs n).getD p default).1 (hplenOf (rec vs n).v) hlast.1
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals try simp only [rc70, rc71]
    all_goals node_rc3 []
    all_goals simp only [hlast.1, hlast.2, hl9, b2n]
    all_goals simp [sumCell]

theorem wTr_other {q : Nat} (hq : R vs ≤ q) : RowGoal vs H wTr q := by
  intro C D P hC hD ex hex
  have hC' := cells_other hq hC
  simp only [wTr, NodeV3.windowConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  generalize total vs = T at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev3 [hC']
  all_goals split <;> simp [sumCell, padCell]

theorem wTr_ok : GroupOk vs H wTr :=
  groupOk_of vs H (fun _ h => wTr_node ok hHR h) (wTr_other ok hHR (Nat.le_refl _))
    (fun _ h1 _ => wTr_other ok hHR (by omega))

theorem wLoc_ok : GroupOk vs H wLoc := by
  apply groupOk_of
  · intro q hqn C D P hC hD ex hex
    obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
    have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
      intro x hx; rw [hC x hx, X_node hqn, hr]
    exact wLoc_rec vs _ (fmem ok hn hp).1 (rwf ok hn) (row_b ok hn hp false) (row_b ok hn hp true)
      C D _ _ _ P hC' ex hex
  · intro C D P hC hD ex hex
    have hC' := cells_other (Nat.le_refl _) hC
    simp only [wLoc, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals simp [sumCell, padCell]
  · intro q hq _ C D P hC hD ex hex
    have hC' := cells_other (Nat.le_of_lt hq) hC
    simp only [wLoc, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals split <;> simp [sumCell, padCell]

/-- **`cWindows`.** -/
theorem cWindows_ok : GroupOk vs H NodeV3.cWindows := by
  intro q hq C D P hC hD ex hex
  have h : ex ∈ wLoc ∨ ex ∈ wShift ∨ ex ∈ wUnrev ∨ ex ∈ wTr := by
    simp only [NodeV3.cWindows, List.mem_append] at hex
    rcases hex with (((h | h) | h) | h) | h
    · left; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [wLoc]
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (List.mem_append_left _ h)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (left; simp [wLoc]; done)
        | (right; right; right; simp [wTr]; done)
  rcases h with h | h | h | h
  · exact wLoc_ok ok hHR q hq C D P hC hD ex h
  · exact wShift_ok ok hHR q hq C D P hC hD ex h
  · exact wUnrev_ok ok hHR q hq C D P hC hD ex h
  · exact wTr_ok ok hHR q hq C D P hC hD ex h

end

end NodeGen3

end ZkFormal.NearV3.Render
