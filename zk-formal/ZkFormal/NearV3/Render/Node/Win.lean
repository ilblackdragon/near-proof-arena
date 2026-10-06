import ZkFormal.NearV3.Render.Node.WinFacts

/-!
# ZkFormal.NearV3.Render.Node.Win — `cWindows`: registers, unrevealed windows, lookups, child slots
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (wOf lwOf len_facts mem_len)

namespace NodeGen3

/-- The shift-register constraints. -/
abbrev wShift : List Expr := (List.range 31).flatMap (fun i =>
    [ mul3 NodeV3.winE (Dsl.not (c NodeV3.fe)) (sub (n (NodeV3.reg i)) (c (NodeV3.reg (i + 1)))),
      mul3 NodeV3.winE (Dsl.not (c NodeV3.fe)) (sub (n (NodeV3.preg i)) (c (NodeV3.preg (i + 1)))) ])

/-- Unrevealed child / unwritten value. -/
abbrev wUnrev : List Expr := (List.range 32).flatMap (fun i =>
    [ .mul (mul3 (c NodeV3.fs) (c NodeV3.sCH) (Dsl.not (c NodeV3.rv))) (sub (c (NodeV3.preg i)) (c (NodeV3.reg i))),
      .mul (mul3 (c NodeV3.fs) (c NodeV3.sVH) (Dsl.not (c NodeV3.tw))) (sub (c (NodeV3.preg i)) (c (NodeV3.reg i))) ])

/-- The window transitions. -/
abbrev wTr : List Expr :=
  NodeV3.windowConst.map (fun x => mul3 (c NodeV3.sCH) (Dsl.not (c NodeV3.fe)) (sub (n x) (c x))) ++
  [ .mul (mul3 (c NodeV3.fe) (Dsl.not (c NodeV3.sCH)) (n NodeV3.sCH)) (n NodeV3.w),
    .mul (mul3 (c NodeV3.fe) (c NodeV3.sCH) (n NodeV3.sCH)) (sub (n NodeV3.w) (.add (c NodeV3.w) (k 1))) ]

/-- The row-local window constraints. -/
abbrev wLoc : List Expr :=
  [ .mul NodeV3.winE (sub (c NodeV3.b) (c (NodeV3.reg 0))), .mul NodeV3.winE (sub (c NodeV3.pb) (c (NodeV3.preg 0))),
    .mul (c NodeV3.rv) (Dsl.not (c NodeV3.sCH)),
    sub (c NodeV3.gD) (.add (c NodeV3.gP) (.mul NodeV3.vhStart (c NodeV3.tv))),
    .mul (c NodeV3.gP) (sub (c NodeV3.dI) (mid K_NPRE (c NodeV3.cid))),
    .mul (c NodeV3.gP) (sub (c NodeV3.dL) (c NodeV3.clen)),
    .mul NodeV3.valStart (sub (c NodeV3.dI) (mid K_VPRE (c NodeV3.vid))),
    .mul NodeV3.valStart (sub (c NodeV3.dL) (c NodeV3.vlen)),
    mul3 NodeV3.isBr (c NodeV3.sCH) (sub (sum ((List.range 16).map fun i => c (NodeV3.jj i))) (k 1)),
    mul3 NodeV3.isBr (c NodeV3.sCH) (sub (sum ((List.range 16).map fun i => .mul (c (NodeV3.jj i)) (c (NodeV3.bm i)))) (k 1)),
    mul3 NodeV3.isBr (c NodeV3.sCH) (sub NodeV3.belowE (c NodeV3.w)),
    .mul (c NodeV3.te) (.mul (c NodeV3.sCH) (c NodeV3.w)),
    mul3 (c NodeV3.lastw) (c NodeV3.sCH) (sub (.add (c NodeV3.w) (k 1)) NodeV3.nWinE) ]

theorem cells_other {vs : List NodeS3} {H q : Nat} (hq : R vs ≤ q) {C : Nat → Int}
    (hC : ∀ x, x < 185 → C x = X vs H q x) :
    ∀ x, x < 185 → C x = (if q = R vs then (sumCell (total vs) x : Int) else (padCell (total vs) x : Int)) := by
  intro x hx; rw [hC x hx]
  split
  · subst q; rw [X_sum]
  · rw [X_pad (by omega)]

theorem rc_reg (vs : List NodeS3) (r : NRec) (i : Nat) (hi : i < 32) :
    rowCell vs r (72 + i) = (match r.f.win with | some w => w.pre.getD (r.idx + i) 0 | none => 0) := by
  unfold rowCell
  simp only [show ¬ 72 + i < 29 by omega, show ¬ 72 + i < 33 by omega, show ¬ 72 + i < 37 by omega,
      show ¬ 72 + i < 53 by omega, show ¬ 72 + i = 53 by omega, show ¬ 72 + i < 70 by omega,
      show ¬ 72 + i = 70 by omega, show ¬ 72 + i = 71 by omega, show 72 + i < 104 by omega, if_false, if_true,
      Nat.add_sub_cancel_left]
  generalize r.f.win = x; cases x <;> rfl

theorem rc_preg (vs : List NodeS3) (r : NRec) (i : Nat) (hi : i < 32) :
    rowCell vs r (104 + i) = (match r.f.win with | some w => w.post.getD (r.idx + i) 0 | none => 0) := by
  unfold rowCell
  simp only [show ¬ 104 + i < 29 by omega, show ¬ 104 + i < 33 by omega, show ¬ 104 + i < 37 by omega,
      show ¬ 104 + i < 53 by omega, show ¬ 104 + i = 53 by omega, show ¬ 104 + i < 70 by omega,
      show ¬ 104 + i = 70 by omega, show ¬ 104 + i = 71 by omega, show ¬ 104 + i < 104 by omega,
      show 104 + i < 136 by omega, if_false, if_true, Nat.add_sub_cancel_left]
  generalize r.f.win = x; cases x <;> rfl

theorem unrev_ch (vs : List NodeS3) (r : NRec) (i : Nat) (hi : i < 32) (hw : (rec vs r.n).v.wf)
    (hf : r.f ∈ fieldsOf (rec vs r.n).v) :
    ((rowCell vs r 24 : Nat) : Int) * ((rowCell vs r 21 : Nat) : Int) * (((1 : Nat) : Int) + -((rowCell vs r 136 : Nat) : Int)) *
      (((rowCell vs r (104 + i) : Nat) : Int) + -((rowCell vs r (72 + i) : Nat) : Int)) = 0 := by
  have e1 := rc_preg vs r i hi
  have e2 := rc_reg vs r i hi
  rw [e1, e2, Rc.c21, Rc.c24, Rc.c136]
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only at hf hw ⊢
  cases f
  case ch w =>
    have := (win_shape _ hw w).1 hf
    cases hl : w.look <;> simp_all [F.state, NodeGen.F.chw, NodeGen.F.win, Node.sCH, b2n] <;> try simp [Int.add_right_neg]
  all_goals simp [F.state, NodeGen.F.chw, NodeGen.F.win, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN,
    Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n]

theorem unrev_vh (vs : List NodeS3) (r : NRec) (i : Nat) (hi : i < 32) (hw : (rec vs r.n).v.wf)
    (hf : r.f ∈ fieldsOf (rec vs r.n).v) :
    ((rowCell vs r 24 : Nat) : Int) * ((rowCell vs r 19 : Nat) : Int) * (((1 : Nat) : Int) + -((rowCell vs r 167 : Nat) : Int)) *
      (((rowCell vs r (104 + i) : Nat) : Int) + -((rowCell vs r (72 + i) : Nat) : Int)) = 0 := by
  have e1 := rc_preg vs r i hi
  have e2 := rc_reg vs r i hi
  rw [e1, e2, Rc.c19, Rc.c24, Rc.c167]
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only at hf hw ⊢
  cases f
  case vh w =>
    have := (win_shape _ hw w).2 hf
    cases ht : twOf (rec vs rn).v <;> simp_all [F.state, NodeGen.F.chw, NodeGen.F.win, Node.sVH, b2n] <;> try simp [Int.add_right_neg]
  all_goals simp [F.state, NodeGen.F.chw, NodeGen.F.win, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN,
    Node.sVH, Node.sBM, Node.sCH, Node.sMEM, b2n]

section
variable {vs : List NodeS3} (ok : NodeOk vs) {H : Nat} (hHR : R vs + 1 ≤ H)
include ok hHR

theorem wShift_node {q : Nat} (hqn : q < R vs) : RowGoal vs H wShift q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off vs n + p + 1) % H = off vs n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hw := rwf ok hn
  simp only [wShift, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  have hreg := rc_reg vs
  have hpreg := rc_preg vs
  by_cases h1 : p + 1 < (layN vs n).length
  · have h2 : off vs n + p + 1 < R vs := by
      rcases next_row hn hp with ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have h3 : (recsOf vs).getD (off vs n + p + 1) default = mkR vs n (p + 1) := by
      rcases next_row hn hp with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      all_goals omega
    have hD' : ∀ x, x < 185 → D x = (rowCell vs (mkR vs n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    have hadj := lay_adj hw h1
    simp only [show layout (fieldsOf (rec vs n).v) (hplenOf (rec vs n).v) = layN vs n from rfl] at hadj
    rcases hex with rfl | rfl
    all_goals
      simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, NodeV3.winE, NodeV3.fe, NodeV3.sVH,
        NodeV3.sCH, NodeV3.reg, NodeV3.preg, ite_true, ite_false, Bool.false_eq_true]
      rw [hC' 19 (by decide), hC' 21 (by decide), hC' 25 (by decide)]
      first
        | rw [hD' (72 + i) (by omega), hC' (72 + (i + 1)) (by omega), hreg _ i (by omega),
            hreg _ (i + 1) (by omega)]
        | rw [hD' (104 + i) (by omega), hC' (104 + (i + 1)) (by omega), hpreg _ i (by omega),
            hpreg _ (i + 1) (by omega)]
      simp only [Rc.c19, Rc.c21, Rc.c25, mkR]
      rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
      · simp only [a1, a2, show ((layN vs n).getD p default).2 + 1 + i =
          ((layN vs n).getD p default).2 + (i + 1) by omega]
        simp only [Int.add_neg_cancel_right, Int.sub_self, Int.mul_zero, Int.add_right_neg]
      · simp only [b2n, decide_eq_true_eq, a1, ite_true]; simp
  · rcases hex with rfl | rfl
    all_goals
      simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, NodeV3.winE, NodeV3.fe, NodeV3.sVH,
        NodeV3.sCH, NodeV3.reg, NodeV3.preg, ite_true, ite_false, Bool.false_eq_true]
      rw [hC' 19 (by decide), hC' 21 (by decide), hC' 25 (by decide)]
      simp only [Rc.c19, Rc.c21, Rc.c25, mkR]
      have hlast := (last_iff ok hn hp).1 (by omega)
      have hl9 := mem_len ((layN vs n).getD p default).1 (hplenOf (rec vs n).v) hlast.1
      simp only [hlast.1, hlast.2, hl9, b2n]
      simp

theorem wShift_other {q : Nat} (hq : R vs ≤ q) : RowGoal vs H wShift q := by
  intro C D P hC hD ex hex
  have hC' := cells_other hq hC
  simp only [wShift, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  generalize total vs = T at *
  rcases hex with rfl | rfl
  all_goals
    simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, NodeV3.winE, NodeV3.fe, NodeV3.sVH,
      NodeV3.sCH, NodeV3.reg, NodeV3.preg, ite_true, ite_false, Bool.false_eq_true]
    rw [hC' 19 (by decide), hC' 21 (by decide)]
    split <;> simp [sumCell, padCell]

theorem wUnrev_node {q : Nat} (hqn : q < R vs) : RowGoal vs H wUnrev q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hfm := (fmem ok hn hp).1
  have hw := rwf ok hn
  simp only [wUnrev, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  rcases hex with rfl | rfl
  all_goals
    simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, NodeV3.fs, NodeV3.rv, NodeV3.tw, NodeV3.sVH,
      NodeV3.sCH, NodeV3.reg, NodeV3.preg, ite_true, ite_false, Bool.false_eq_true]
    simp only [hC' 24 (by decide), hC' 21 (by decide), hC' 19 (by decide), hC' 136 (by decide), hC' 167 (by decide),
      hC' (104 + i) (by omega), hC' (72 + i) (by omega)]
  · exact unrev_ch vs _ i hi hw hfm
  · exact unrev_vh vs _ i hi hw hfm

theorem wUnrev_other {q : Nat} (hq : R vs ≤ q) : RowGoal vs H wUnrev q := by
  intro C D P hC hD ex hex
  have hC' := cells_other hq hC
  simp only [wUnrev, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨i, hi, hex⟩ := hex
  generalize total vs = T at *
  rcases hex with rfl | rfl
  all_goals
    simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not, NodeV3.fs, NodeV3.rv, NodeV3.tw, NodeV3.sVH,
      NodeV3.sCH, NodeV3.reg, NodeV3.preg, ite_true, ite_false, Bool.false_eq_true]
    rw [hC' 24 (by decide)]
    split <;> simp [sumCell, padCell]

theorem wShift_ok : GroupOk vs H wShift :=
  groupOk_of vs H (fun _ h => wShift_node ok hHR h) (wShift_other ok hHR (Nat.le_refl _))
    (fun _ h1 _ => wShift_other ok hHR (by omega))

theorem wUnrev_ok : GroupOk vs H wUnrev :=
  groupOk_of vs H (fun _ h => wUnrev_node ok hHR h) (wUnrev_other ok hHR (Nat.le_refl _))
    (fun _ h1 _ => wUnrev_other ok hHR (by omega))

end

end NodeGen3

end ZkFormal.NearV3.Render
