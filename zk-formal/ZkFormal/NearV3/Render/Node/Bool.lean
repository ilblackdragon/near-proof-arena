import ZkFormal.NearV3.Render.Node.Facts

/-!
# ZkFormal.NearV3.Render.Node.Bool — `cBool`: boolean columns
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

theorem b2n_le' (b : Bool) : b2n b ≤ 1 := by unfold b2n; split <;> omega

theorem typeOf_le (v : NodeV3) : (typeOf v).1 ≤ 1 ∧ (typeOf v).2.1 ≤ 1 ∧ (typeOf v).2.2.1 ≤ 1 ∧
    (typeOf v).2.2.2 ≤ 1 := by
  cases v with
  | leaf => simp [typeOf]
  | ext => simp [typeOf]
  | branch sv => cases sv <;> simp [typeOf]

theorem oddOf_le (v : NodeV3) : oddOf v ≤ 1 := by simp only [oddOf]; split <;> omega
theorem nokeyOf_le (v : NodeV3) : nokeyOf v ≤ 1 := b2n_le' _
theorem nochildOf_le (v : NodeV3) : nochildOf v ≤ 1 := b2n_le' _

theorem gDp_le (v : NodeV3) (r : NRec) :
    (match digOf v r with | some (_, _, true) => 1 | _ => 0) +
      (match digOf v r with | some (_, _, false) => b2n (twOf v) | _ => 0) ≤ 1 := by
  have := b2n_le' (twOf v)
  rcases h : digOf v r with _ | ⟨a, b, c⟩
  · simp
  · cases c <;> simp <;> omega

theorem rowCell_bool (vs : List NodeS3) (r : NRec) {x : Nat} (hx : x ∈ NodeV3.boolCols) : rowCell vs r x ≤ 1 := by
  have ht := typeOf_le (rec vs r.n).v
  have hgdp := gDp_le (rec vs r.n).v r
  simp only [NodeV3.boolCols, NodeV3.states, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.append_assoc, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, NodeV3.act, NodeV3.nf, NodeV3.nl, NodeV3.sumr, NodeV3.tl, NodeV3.te, NodeV3.tb1, NodeV3.tb2,
    NodeV3.sTAG, NodeV3.sHPL, NodeV3.sHPF, NodeV3.sKEY, NodeV3.sVLEN, NodeV3.sVH, NodeV3.sBM, NodeV3.sCH,
    NodeV3.sMEM, NodeV3.fs, NodeV3.fe, NodeV3.odd, NodeV3.nokey, NodeV3.hbit, NodeV3.lbit, NodeV3.bm,
    NodeV3.nochild, NodeV3.jj, NodeV3.lastw, NodeV3.rv, NodeV3.tv, NodeV3.gD, NodeV3.gP, NodeV3.gV, NodeV3.gA,
    NodeV3.xrv, NodeV3.xdead, NodeV3.xlast0, NodeV3.eext, NodeV3.gB, NodeV3.dbit8, NodeV3.tw, NodeV3.dup,
    NodeV3.hd, NodeV3.gL, NodeV3.gS, NodeV3.gDp, NodeV3.gBm, Nat.reduceAdd] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_rc3 []
  all_goals first
    | omega
    | exact b2n_le _
    | exact b2n_le' _
    | exact bitOf_le _ _
    | exact oddOf_le _
    | exact nokeyOf_le _
    | exact nochildOf_le _
    | exact hgdp
    | (repeat' split) <;> first | omega | exact bitOf_le _ _ | exact b2n_le _ | exact b2n_le' _
    | (simp only [gCell]; split <;> omega)

theorem boolCols_range : ∀ x ∈ NodeV3.boolCols, x ≠ 152 ∧ x < 185 := by decide

theorem cell_bool (vs : List NodeS3) (H q : Nat) {x : Nat} (hx : x ∈ NodeV3.boolCols) : cell vs H q x ≤ 1 := by
  have := boolCols_range x hx
  unfold cell
  split
  · exact rowCell_bool vs _ hx
  · split
    · simp only [sumCell]
      by_cases h3 : x = 3
      · simp [h3]
      · simp only [h3, this.1, ite_false]; omega
    · simp only [padCell, this.1, ite_false]; omega

theorem cBool_ok (vs : List NodeS3) (H : Nat) : GroupOk vs H NodeV3.cBool := by
  intro q hq C D P hC hD ex hex
  simp only [NodeV3.cBool, List.mem_map] at hex
  obtain ⟨x, hx, rfl⟩ := hex
  have hlt : x < 185 := (boolCols_range x hx).2
  have h1 := cell_bool vs H q hx
  simp only [Dsl.bool, Dsl.sub, Dsl.c, Dsl.k, ev, ite_false, Bool.false_eq_true, hC x hlt, X]
  generalize cell vs H q x = v at *
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> decide

end NodeGen3

end ZkFormal.NearV3.Render
