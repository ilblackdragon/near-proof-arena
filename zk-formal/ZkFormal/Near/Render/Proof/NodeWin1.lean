import ZkFormal.Near.Render.Proof.NodeWin0

/-!
# ZkFormal.Near.Render.Proof.NodeWin1 — `cWindows`: the shift registers and the unrevealed windows
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-- The shift-register constraints. -/
abbrev wShift : List Expr := (List.range 31).flatMap (fun i =>
    [ mul3 Node.winE (Dsl.not (c Node.fe)) (sub (n (Node.reg i)) (c (Node.reg (i + 1)))),
      mul3 Node.winE (Dsl.not (c Node.fe)) (sub (n (Node.preg i)) (c (Node.preg (i + 1)))) ])

/-- Unrevealed child / untouched value. -/
abbrev wUnrev : List Expr := (List.range 32).flatMap (fun i =>
    [ .mul (mul3 (c Node.fs) (c Node.sCH) (Dsl.not (c Node.rv))) (sub (c (Node.preg i)) (c (Node.reg i))),
      .mul (mul3 (c Node.fs) (c Node.sVH) (Dsl.not (c Node.tv))) (sub (c (Node.preg i)) (c (Node.reg i))) ])

theorem unrev_ch (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) (i : Nat) (hi : i < 32)
    (hf : r.f ∈ fieldsOf I r.n (I.nodeAt r.n)) :
    ((rowCell I u r 24 : Nat) : Int) * ((rowCell I u r 21 : Nat) : Int) * (((1 : Nat) : Int) + -((rowCell I u r 136 : Nat) : Int)) *
      (((rowCell I u r (104 + i) : Nat) : Int) + -((rowCell I u r (72 + i) : Nat) : Int)) = 0 := by
  rw [rc_reg _ _ _ i hi, rc_preg _ _ _ i hi, NodeRc.r21, rc_fs, rc_rv]
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only at hf ⊢
  cases f
  case ch w =>
    have := (win_shape _ _ _ w).1 hf
    cases hl : w.look <;> simp_all [Int.add_right_neg, F.state, F.chw, F.win, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n]
  all_goals simp [F.state, F.chw, F.win, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n]

theorem unrev_vh (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) (i : Nat) (hi : i < 32)
    (hf : r.f ∈ fieldsOf I r.n (I.nodeAt r.n)) :
    ((rowCell I u r 24 : Nat) : Int) * ((rowCell I u r 19 : Nat) : Int) * (((1 : Nat) : Int) + -((rowCell I u r 139 : Nat) : Int)) *
      (((rowCell I u r (104 + i) : Nat) : Int) + -((rowCell I u r (72 + i) : Nat) : Int)) = 0 := by
  rw [rc_reg _ _ _ i hi, rc_preg _ _ _ i hi, NodeRc.r19, rc_fs, rc_tv]
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only at hf ⊢
  cases f
  case vh w =>
    have := (win_shape _ _ _ w).2 hf
    cases ht : (I.nodeAt rn).touched <;> simp_all [Int.add_right_neg, F.state, F.chw, F.win, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n]
  all_goals simp [F.state, F.chw, F.win, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n]

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

theorem wShift_node {q : Nat} (hqn : q < RN c e) : RowGoal c e wShift q := by
  intro C D P hC hD ex hex
  have hRH := RN_lt (c := c) (e := e)
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off (mkInfo c e) n + p + 1) % HN c e = off (mkInfo c e) n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hw := nodeAt_wf hg hs hn
  have hidx := (fmem hg hs hn hp).2
  dsimp only [mkR] at hidx
  simp only [wShift, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  generalize HN c e = H at *
  by_cases h1 : p + 1 < (NodeLay.layN (mkInfo c e) n).length
  · have h2 : off (mkInfo c e) n + p + 1 < RN c e := by
      rcases next_row hn hp with ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have h3 : (recsOf (mkInfo c e)).getD (off (mkInfo c e) n + p + 1) default = mkR (mkInfo c e) n (p + 1) := by
      rcases next_row hn hp with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      all_goals omega
    have hD' : ∀ x, x < 163 → D x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    have hadj := lay_adj hw h1
    rcases hex with rfl | rfl
    all_goals
      simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, Node.winE, Node.fe, Node.sVH, Node.sCH,
        Node.reg, Node.preg, ite_true, ite_false, Bool.false_eq_true]
      rw [hC' 19 (by decide), hC' 21 (by decide), hC' 25 (by decide)]
      first
        | rw [hD' (72 + i) (by omega), hC' (72 + (i + 1)) (by omega), rc_reg _ _ _ i (by omega),
            rc_reg _ _ _ (i + 1) (by omega)]
        | rw [hD' (104 + i) (by omega), hC' (104 + (i + 1)) (by omega), rc_preg _ _ _ i (by omega),
            rc_preg _ _ _ (i + 1) (by omega)]
      simp only [NodeRc.r19, NodeRc.r21, rc_fe]
      rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
      · simp only [a1, a2, show ((NodeLay.layN (mkInfo c e) n).getD p default).2 + 1 + i =
          ((NodeLay.layN (mkInfo c e) n).getD p default).2 + (i + 1) by omega]
        simp only [Int.add_neg_cancel_right, Int.sub_self, Int.mul_zero, Int.add_right_neg]
      · simp only [b2n, decide_eq_true_eq, a1, ite_true]; simp
  · rcases hex with rfl | rfl
    all_goals
      simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, Node.winE, Node.fe, Node.sVH, Node.sCH,
        Node.reg, Node.preg, ite_true, ite_false, Bool.false_eq_true]
      rw [hC' 19 (by decide), hC' 21 (by decide), hC' 25 (by decide)]
      simp only [NodeRc.r19, NodeRc.r21, rc_fe]
      have hlast := (last_iff hg hs hn hp).1 (by omega)
      have hl9 := mem_len ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n)) hlast.1
      simp only [hlast.1, hlast.2, hl9, b2n]
      simp

theorem cells_other {q : Nat} (hq : RN c e ≤ q) {C : Nat → Int} (hC : ∀ x, x < 163 → C x = X c e q x) :
    ∀ x, x < 163 → C x = (if q = RN c e then (sumCell (totalOf (mkInfo c e)) x : Int)
      else (padCell (totalOf (mkInfo c e)) x : Int)) := by
  intro x hx; rw [hC x hx]
  split
  · subst q; rw [X_sum]
  · rw [X_pad (by omega)]

theorem wShift_other {q : Nat} (hq : RN c e ≤ q) : RowGoal c e wShift q := by
  intro C D P hC hD ex hex
  have hC' := cells_other hg hs hq hC
  simp only [wShift, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  generalize totalOf (mkInfo c e) = T at *
  rcases hex with rfl | rfl
  all_goals
    simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, Node.winE, Node.fe, Node.sVH, Node.sCH,
      Node.reg, Node.preg, ite_true, ite_false, Bool.false_eq_true]
    rw [hC' 19 (by decide), hC' 21 (by decide)]
    split <;> simp [sumCell, padCell, Node.sumr, Node.sz]

theorem wUnrev_node {q : Nat} (hqn : q < RN c e) : RowGoal c e wUnrev q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hfm := (fmem hg hs hn hp).1
  simp only [wUnrev, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  rcases hex with rfl | rfl
  all_goals
    simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, Node.fs, Node.rv, Node.tv, Node.sVH, Node.sCH,
      Node.reg, Node.preg, ite_true, ite_false, Bool.false_eq_true]
    simp only [hC' 24 (by decide), hC' 21 (by decide), hC' 19 (by decide), hC' 136 (by decide), hC' 139 (by decide),
      hC' (104 + i) (by omega), hC' (72 + i) (by omega)]
  · exact unrev_ch _ _ _ i hi hfm
  · exact unrev_vh _ _ _ i hi hfm

theorem wUnrev_other {q : Nat} (hq : RN c e ≤ q) : RowGoal c e wUnrev q := by
  intro C D P hC hD ex hex
  have hC' := cells_other hg hs hq hC
  simp only [wUnrev, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  generalize totalOf (mkInfo c e) = T at *
  rcases hex with rfl | rfl
  all_goals
    simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, Node.fs, Node.rv, Node.tv, Node.sVH, Node.sCH,
      Node.reg, Node.preg, ite_true, ite_false, Bool.false_eq_true]
    rw [hC' 24 (by decide)]
    split <;> simp [sumCell, padCell, Node.sumr, Node.sz]

theorem wShift_ok : GroupOk c e wShift :=
  groupOk_of (fun _ h => wShift_node hg hs h) (wShift_other hg hs (Nat.le_refl _)) (fun _ h1 _ => wShift_other hg hs (by omega))

theorem wUnrev_ok : GroupOk c e wUnrev :=
  groupOk_of (fun _ h => wUnrev_node hg hs h) (wUnrev_other hg hs (Nat.le_refl _)) (fun _ h1 _ => wUnrev_other hg hs (by omega))

end

end NodeRow

end ZkFormal.Near.Render
