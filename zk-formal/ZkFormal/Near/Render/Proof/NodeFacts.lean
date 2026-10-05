import ZkFormal.Near.Render.Proof.NodeRow0

/-!
# ZkFormal.Near.Render.Proof.NodeFacts — facts about one node row of the honest table

For node `n < N` and position `p < len`: the record is well formed with a
short key of nibbles, the row's field and index (`fmem`), the byte read off
the field (`row_b`, `row_pb`, `< 256`), the revealed-size prefix sums
(`szBefore_succ`, `total_le`), and the `node_ev` tactic that unfolds an
integer evaluation of a node-table expression.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- Unfold the integer value of a node-table expression (columns by name,
the `Dsl` builders), rewriting cells with the given equations. -/
syntax "node_ev" "[" (Lean.Parser.Tactic.simpLemma),* "]" : tactic
macro_rules
  | `(tactic| node_ev [$ts,*]) => `(tactic| simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not,
      Dsl.smul, Dsl.sum, Dsl.bits, Dsl.mid, Dsl.bool, List.map, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.map_append, ite_true, ite_false,
      Bool.false_eq_true, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, Nat.reduceLT, Int.reduceNeg,
      Node.act, Node.nf, Node.nl, Node.sumr, Node.nid, Node.pos, Node.len, Node.depth, Node.b, Node.pb, Node.tl,
      Node.te, Node.tb1, Node.tb2, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
      Node.sCH, Node.sMEM, Node.idx, Node.fs, Node.fe, Node.hplen, Node.odd, Node.nokey, Node.hbit, Node.lbit,
      Node.bm, Node.nochild, Node.jj, Node.w, Node.lastw, Node.reg, Node.preg, Node.rv, Node.cid, Node.clen,
      Node.tv, Node.dI, Node.dL, Node.gD, Node.gP, Node.gV, Node.gA, Node.aI, Node.aS, Node.aN, Node.aJ,
      Node.mA, Node.mB, Node.sz, Node.res, Node.cres, Node.xres, Node.xrv, Node.xdead, Node.xlast0, Node.eext,
      Node.gB, Node.bN, Node.bJ, Node.hiE, Node.loE, Node.sE, Node.kiE, Node.popE, Node.isBr, Node.tagE,
      Node.winE, Node.jIdxE, Node.belowE, Node.nWinE, Node.chStart, Node.vhStart, Node.valStart, Node.bmLo,
      Node.bmHi, Node.states, Node.nodeConst, Node.windowConst, $ts,*])

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e) {n : Nat} (hn : n < e.ns.length)
include hg hs hn

theorem nodeAt_wf : ((mkInfo c e).nodeAt n).wf := by
  rw [info_nodeAt hn]; exact hg.nodes_wf _ (List.getElem_mem hn)

theorem nodeAt_key : ((mkInfo c e).nodeAt n).key.length < 510 := by
  rw [info_nodeAt hn]; exact hs.keys _ (List.getElem_mem hn)

theorem nodeAt_nib : ∀ x ∈ ((mkInfo c e).nodeAt n).key, x < 16 := by
  have hw := nodeAt_wf hg hs hn
  generalize (mkInfo c e).nodeAt n = nr at hw
  have hk : nibblesOk nr.key = true := by
    cases nr with
    | leaf k v m => exact hw.1
    | ext k kid m => exact hw.1
    | branch v kids m => rfl
  intro x hx
  simp only [nibblesOk, List.all_eq_true, decide_eq_true_eq] at hk
  exact hk x hx

theorem len_eq : ((mkInfo c e).pre.getD n []).length = (NodeLay.layN (mkInfo c e) n).length := by
  rw [NodeLay.pre_layout hg hs.keys hn]; simp

variable {p : Nat} (hp : p < (NodeLay.layN (mkInfo c e) n).length)
include hp

theorem fmem : (mkR (mkInfo c e) n p).f ∈ fieldsOf (mkInfo c e) n ((mkInfo c e).nodeAt n) ∧
    (mkR (mkInfo c e) n p).idx < (mkR (mkInfo c e) n p).f.len (hplenOf ((mkInfo c e).nodeAt n)) :=
  lay_get_mem _ n p hp

theorem row_b : (mkR (mkInfo c e) n p).b =
    (NodeLay.fbytes ((mkInfo c e).nodeAt n) false (mkR (mkInfo c e) n p).f).getD (mkR (mkInfo c e) n p).idx 0 := by
  show ((mkInfo c e).pre.getD n []).getD p 0 = _
  rw [NodeLay.pre_layout hg hs.keys hn]
  simp [List.getD_eq_getElem?_getD, hp]

theorem row_pb : (mkR (mkInfo c e) n p).pb =
    (NodeLay.fbytes ((mkInfo c e).nodeAt n) true (mkR (mkInfo c e) n p).f).getD (mkR (mkInfo c e) n p).idx 0 := by
  show ((mkInfo c e).post.getD n []).getD p 0 = _
  rw [NodeLay.post_layout hg hs.keys hn]
  simp [List.getD_eq_getElem?_getD, hp]

theorem row_b8 : (mkR (mkInfo c e) n p).b < 256 := by
  show ((mkInfo c e).pre.getD n []).getD p 0 < 256
  have h1 := (pre_ok c e hg n).2
  have h2 := len_eq hg hs hn
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact h1 _ (List.getElem_mem _)

end

/-! ## Revealed size -/

theorem szBefore_succ (I : Info) (n : Nat) : szBefore I (n + 1) = szBefore I n + nodeSz I n := by
  simp [szBefore, List.range_succ]

theorem szBefore_zero (I : Info) : szBefore I 0 = 0 := rfl

theorem total_le {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e) :
    szBefore (mkInfo c e) e.ns.length ≤ 3000000 := by
  have h2 : ((List.range e.ns.length).map (nodeSz (mkInfo c e))).sum ≤
      ((List.range e.ns.length).map fun n => nodeSize (e.ns.toArray.getD n (.branch none [] 0))).sum := by
    apply sum_map_le; intro n _
    have := (pre_ok c e hg n).1
    simp only [Info.nodeAt, mkInfo_ns] at this
    unfold nodeSize nodeSz; unfold sz0 at this
    simp only [Info.nodeAt, mkInfo_ns]
    exact Nat.add_le_add_right this _
  rw [range_map_getD e.ns _ nodeSize] at h2
  have := hg.size
  simp only [revealedOf, Params.maxWitnessBytes] at this
  simp only [szBefore]; omega

end NodeRow

end ZkFormal.Near.Render
