import ZkFormal.NearV3.Render.Node.Cells

/-!
# ZkFormal.NearV3.Render.Node.Frame — constraints over the integers, row by row

As v1 `NodeRow0`: `constr_of` reduces local legality to `GroupOk` (every group of
constraints vanishes over `ℤ` on every row, `EvI.ev`); rows are node rows `mkR vs n p`,
the `SUM` row (`q = R`) or padding (`q > R`).  `node_ev3` unfolds an integer evaluation.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

/-- Unfold the integer value of a `nodeV3` expression. -/
syntax "node_ev3" "[" (Lean.Parser.Tactic.simpLemma),* "]" : tactic
macro_rules
  | `(tactic| node_ev3 [$ts,*]) => `(tactic| simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not,
      Dsl.smul, Dsl.sum, Dsl.bits, Dsl.mid, Dsl.bool, List.map, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.map_append, ite_true, ite_false,
      Bool.false_eq_true, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, Nat.reduceLT, Int.reduceNeg,
      NodeV3.act, NodeV3.nf, NodeV3.nl, NodeV3.sumr, NodeV3.nid, NodeV3.pos, NodeV3.len, NodeV3.depth, NodeV3.b,
      NodeV3.pb, NodeV3.tl, NodeV3.te, NodeV3.tb1, NodeV3.tb2, NodeV3.sTAG, NodeV3.sHPL, NodeV3.sHPF, NodeV3.sKEY,
      NodeV3.sVLEN, NodeV3.sVH, NodeV3.sBM, NodeV3.sCH, NodeV3.sMEM, NodeV3.idx, NodeV3.fs, NodeV3.fe,
      NodeV3.hplen, NodeV3.odd, NodeV3.nokey, NodeV3.hbit, NodeV3.lbit, NodeV3.bm, NodeV3.nochild, NodeV3.jj,
      NodeV3.w, NodeV3.lastw, NodeV3.reg, NodeV3.preg, NodeV3.rv, NodeV3.cid, NodeV3.clen, NodeV3.tv, NodeV3.dI,
      NodeV3.dL, NodeV3.gD, NodeV3.gP, NodeV3.gV, NodeV3.gA, NodeV3.aI, NodeV3.aS, NodeV3.aN, NodeV3.aJ,
      NodeV3.mA, NodeV3.mB, NodeV3.sz, NodeV3.res, NodeV3.cres, NodeV3.xres, NodeV3.xrv, NodeV3.xdead,
      NodeV3.xlast0, NodeV3.eext, NodeV3.gB, NodeV3.bN, NodeV3.bJ, NodeV3.tau, NodeV3.dbit8, NodeV3.vid,
      NodeV3.vlen, NodeV3.tw, NodeV3.vacc, NodeV3.vsc, NodeV3.dup, NodeV3.hd, NodeV3.repE, NodeV3.mBm,
      NodeV3.aK, NodeV3.bK, NodeV3.bI, NodeV3.bS, NodeV3.gL, NodeV3.xtgt, NodeV3.xtgJ, NodeV3.gS, NodeV3.dE,
      NodeV3.gDp, NodeV3.gBm, NodeV3.hiE, NodeV3.loE, NodeV3.sE, NodeV3.kiE, NodeV3.popE, NodeV3.isBr,
      NodeV3.tagE, NodeV3.winE, NodeV3.jIdxE, NodeV3.belowE, NodeV3.nWinE, NodeV3.chStart, NodeV3.vhStart,
      NodeV3.valStart, NodeV3.bmLo, NodeV3.bmHi, NodeV3.bmE, NodeV3.depE, NodeV3.gDigs, NodeV3.eidE,
      NodeV3.gDpost, NodeV3.bmStart, NodeV3.states, NodeV3.nodeConst, NodeV3.windowConst, $ts,*])

namespace NodeGen3

section
variable (vs : List NodeS3) (H : Nat)

/-- Integer cells of the honest table. -/
def X (q x : Nat) : Int := (cell vs H q x : Int)

/-- A group of constraints vanishes over the integers on every row. -/
def GroupOk (es : List Expr) : Prop :=
  ∀ q, q < H → ∀ (C D P : Nat → Int), (∀ x, x < 185 → C x = X vs H q x) →
    (∀ x, x < 185 → D x = X vs H ((q + 1) % H) x) →
    ∀ ex ∈ es, ev C D (if q = 0 then 1 else 0) (if q + 1 = H then 1 else 0) (if q + 1 = H then 0 else 1) P ex = 0

/-- The goal of a group on row `q`. -/
abbrev RowGoal (es : List Expr) (q : Nat) : Prop :=
  ∀ (C D P : Nat → Int), (∀ x, x < 185 → C x = X vs H q x) →
    (∀ x, x < 185 → D x = X vs H ((q + 1) % H) x) →
    ∀ ex ∈ es, ev C D (if q = 0 then 1 else 0) (if q + 1 = H then 1 else 0) (if q + 1 = H then 0 else 1) P ex = 0

theorem groupOk_append {a b : List Expr} (ha : GroupOk vs H a) (hb : GroupOk vs H b) : GroupOk vs H (a ++ b) := by
  intro q hq C D P hC hD ex hex
  rcases List.mem_append.1 hex with h | h
  · exact ha q hq C D P hC hD ex h
  · exact hb q hq C D P hC hD ex h

theorem groupOk_of {es : List Expr} (h1 : ∀ q, q < R vs → RowGoal vs H es q) (h2 : RowGoal vs H es (R vs))
    (h3 : ∀ q, R vs < q → q < H → RowGoal vs H es q) : GroupOk vs H es := by
  intro q hq
  rcases Nat.lt_trichotomy q (R vs) with h | rfl | h
  · exact h1 q h
  · exact h2
  · exact h3 q h hq

end

theorem constr_of {vs : List NodeS3} {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
    (hH : tr.height tt = H)
    (hc : ∀ q col, q < H → col < 185 → tr.cell tt q col = Fp.ofNat (cell vs H q col))
    (h : GroupOk vs H NodeV3.constraints) :
    ∀ r, r < tr.height tt → ∀ ex ∈ NodeV3.constraints, ex.eval tr tt r pub = 0 := by
  intro q hq ex hex
  rw [hH] at hq
  have hq' : (q + 1) % H < H := Nat.mod_lt _ (by omega)
  apply eval_zero_of_ev (cellsI_ok (fun x hx => hc q x hq hx))
    (by rw [hH]; exact cellsI_ok (fun x hx => hc _ x hq' hx))
  rw [hH]
  exact h q hq _ _ _ (fun x hx => by simp [cellsI, hx, X]) (fun x hx => by simp [cellsI, hx, X]) ex hex

theorem X_node {vs : List NodeS3} {H q : Nat} (hq : q < R vs) (x : Nat) :
    X vs H q x = (rowCell vs ((recsOf vs).getD q default) x : Int) := by
  simp [X, cell, hq]

theorem X_sum {vs : List NodeS3} {H : Nat} (x : Nat) : X vs H (R vs) x = (sumCell (total vs) x : Int) := by
  simp [X, cell]

theorem X_pad {vs : List NodeS3} {H q : Nat} (hq : R vs < q) (x : Nat) :
    X vs H q x = (padCell (total vs) x : Int) := by
  simp [X, cell, show ¬ q < R vs by omega, show q ≠ R vs by omega]

end NodeGen3

end ZkFormal.NearV3.Render
