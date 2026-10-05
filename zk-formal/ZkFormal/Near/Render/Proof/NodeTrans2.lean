import ZkFormal.Near.Render.Proof.NodeTrans

/-!
# ZkFormal.Near.Render.Proof.NodeTrans2 — `cTrans` on the `SUM` and padding rows; `cTrans_ok`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

set_option maxHeartbeats 4000000 in
theorem cTrans_sum : RowGoal c e Node.cTrans (RN c e) := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 163 → C x = (sumCell (totalOf (mkInfo c e)) x : Int) := by
    intro x hx; rw [hC x hx, X_sum]
  have htot := total_le hg hs
  have hRH := RN_lt (c := c) (e := e)
  simp only [Node.cTrans, Node.nodeConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  have ht : totalOf (mkInfo c e) ≤ 3000000 := by
    have : totalOf (mkInfo c e) = szBefore (mkInfo c e) e.ns.length := by simp only [totalOf, NodeInfo.info_N]
    omega
  by_cases hl : RN c e + 1 = HN c e
  · generalize HN c e = H at *
    subst hl
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC']
    all_goals simp only [sumCell, Node.sumr, Node.sz, Nat.reduceEqDiff, Nat.reduceLeDiff, ite_true, ite_false,
      and_false, false_and, and_true, true_and, Nat.reduceLT, Nat.reduceSub, Int.mul_zero, Int.zero_mul, Int.add_zero,
      Int.zero_add]
    all_goals first | (simp; done) | omega | (simp only [bitOf]; omega) | exact bool_one _ (bitOf_le1 _ _)
  · have hD' : ∀ x, x < 163 → D x = (padCell (totalOf (mkInfo c e)) x : Int) := by
      intro x hx; rw [hD x hx, Nat.mod_eq_of_lt (by omega), X_pad (by omega)]
    generalize HN c e = H at *
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals simp only [sumCell, padCell, Node.sumr, Node.sz, Nat.reduceEqDiff, Nat.reduceLeDiff, ite_true,
      ite_false, and_false, false_and, and_true, true_and, Nat.reduceLT, Nat.reduceSub, Int.mul_zero, Int.zero_mul,
      Int.add_zero, Int.zero_add, show RN c e + 1 = H ↔ False from ⟨hl, False.elim⟩]
    all_goals first | (simp; done) | omega | (simp only [bitOf]; omega) | exact bool_one _ (bitOf_le1 _ _)

set_option maxHeartbeats 4000000 in
theorem cTrans_pad {q : Nat} (hqp : RN c e < q) (hq : q < HN c e) : RowGoal c e Node.cTrans q := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 163 → C x = (padCell (totalOf (mkInfo c e)) x : Int) := by
    intro x hx; rw [hC x hx, X_pad hqp]
  simp only [Node.cTrans, Node.nodeConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  by_cases hl : q + 1 = HN c e
  · generalize HN c e = H at *
    subst hl
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC']
    all_goals simp only [padCell, Node.sz, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals first | (simp; done) | omega
  · have hD' : ∀ x, x < 163 → D x = (padCell (totalOf (mkInfo c e)) x : Int) := by
      intro x hx; rw [hD x hx, Nat.mod_eq_of_lt (by omega), X_pad (by omega)]
    generalize HN c e = H at *
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals simp only [padCell, Node.sz, Nat.reduceEqDiff, ite_true, ite_false, show q + 1 = H ↔ False from ⟨hl, False.elim⟩]
    all_goals first | (simp; done) | omega


theorem cTrans_ok : GroupOk c e Node.cTrans :=
  groupOk_of (fun _ h => cTrans_node hg hs h) (cTrans_sum hg hs) (fun _ h1 h2 => cTrans_pad hg hs h1 h2)

end

end NodeRow

end ZkFormal.Near.Render
