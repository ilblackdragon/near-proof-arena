import ZkFormal.Near.Render.Proof.NodeRow0

/-!
# ZkFormal.Near.Render.Proof.NodeBool — `cBool`: boolean columns of the node table
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq

theorem b2n_le (b : Prop) [Decidable b] : b2n (decide b) ≤ 1 := by unfold b2n; split <;> omega
theorem b2n_le' (b : Bool) : b2n b ≤ 1 := by unfold b2n; split <;> omega
theorem bitOf_le (x i : Nat) : bitOf x i ≤ 1 := by unfold bitOf; omega

theorem typeOf_le (nr : NodeRec) : (typeOf nr).1 ≤ 1 ∧ (typeOf nr).2.1 ≤ 1 ∧ (typeOf nr).2.2.1 ≤ 1 ∧
    (typeOf nr).2.2.2 ≤ 1 := by
  cases nr with
  | leaf => simp [typeOf]
  | ext => simp [typeOf]
  | branch v => cases v <;> simp [typeOf]

theorem rowCell_bool (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) {x : Nat} (hx : x ∈ Node.boolCols) :
    rowCell I u r x ≤ 1 := by
  have ht := typeOf_le (I.nodeAt r.n)
  simp only [Node.boolCols, Node.states, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.append_assoc, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, Node.act, Node.nf, Node.nl, Node.sumr, Node.tl, Node.te, Node.tb1, Node.tb2, Node.sTAG, Node.sHPL,
    Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, Node.fs, Node.fe, Node.odd,
    Node.nokey, Node.hbit, Node.lbit, Node.bm, Node.nochild, Node.jj, Node.lastw, Node.rv, Node.tv, Node.gD,
    Node.gP, Node.gV, Node.gA, Node.xrv, Node.xdead, Node.xlast0, Node.eext, Node.gB, Nat.reduceAdd] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [rowCell, Nat.reduceLT, Nat.reduceSub, ite_true, ite_false, Nat.reduceEqDiff]
  all_goals first
    | omega
    | exact b2n_le _
    | exact b2n_le' _
    | exact bitOf_le _ _
    | (split <;> first | omega | exact bitOf_le _ _ | exact b2n_le _ | exact b2n_le' _)
    | (simp only [oddOf]; split <;> omega)
    | (simp only [gateCell]; split <;> omega)
    | (split <;> rename_i h <;> first | omega | (split at h <;> omega))
    | skip

theorem boolCols_range : ∀ x ∈ Node.boolCols, x ≠ 152 ∧ (x < 72 ∨ 94 ≤ x) ∧ x < 163 := by decide

theorem cell_bool (I : Info) (u : Std.HashMap Edge Nat) (recs : Array NRec) (total q : Nat) {x : Nat}
    (hx : x ∈ Node.boolCols) : cell I u recs total q x ≤ 1 := by
  have := boolCols_range x hx
  unfold cell
  split
  · exact rowCell_bool I u _ hx
  · split
    · simp only [sumCell, Node.sumr, Node.sz]
      by_cases h3 : x = 3
      · simp [h3]
      · simp only [h3, this.1, ite_false, show ¬ (72 ≤ x ∧ x < 94) by omega]; omega
    · simp only [padCell, Node.sz, this.1, ite_false]; omega

theorem cBool_ok (c : Claim) (e : Ext) : GroupOk c e Node.cBool := by
  intro q hq C D P hC hD ex hex
  simp only [Node.cBool, List.mem_map] at hex
  obtain ⟨x, hx, rfl⟩ := hex
  have hlt : x < 163 := (boolCols_range x hx).2.2
  have h1 := cell_bool (mkInfo c e) (U c e) (recsA (mkInfo c e)) (totalOf (mkInfo c e)) q hx
  simp only [Dsl.bool, Dsl.sub, Dsl.c, Dsl.k, ev, ite_false, Bool.false_eq_true, hC x hlt, X]
  generalize cell (mkInfo c e) (U c e) (recsA (mkInfo c e)) (totalOf (mkInfo c e)) q x = v at *
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> decide

end NodeRow

end ZkFormal.Near.Render
