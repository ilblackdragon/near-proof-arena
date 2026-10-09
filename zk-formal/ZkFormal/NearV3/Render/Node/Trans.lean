import ZkFormal.NearV3.Render.Node.Rows

/-!
# ZkFormal.NearV3.Render.Node.Trans — `cTrans`: node constants, node succession, `sz`
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

theorem szBefore_succ (vs : List NodeS3) (n : Nat) :
    szBefore vs (n + 1) = szBefore vs n + (if (rec vs n).dup then 0 else ((rec vs n).v.ser false).length) := by
  simp [szBefore, List.range_succ]

section
variable {vs : List NodeS3} (ok : NodeOk vs) {H : Nat} (hHR : R vs + 1 ≤ H)
include ok hHR

set_option maxHeartbeats 4000000 in
theorem cTrans_node {q : Nat} (hqn : q < R vs) : RowGoal vs H NodeV3.cTrans q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off vs n + p + 1) % H = off vs n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hlen := len_eq ok hn
  have hsz := szBefore_succ vs n
  have hlast : off vs n + p + 1 ≠ H := by omega
  simp only [NodeV3.cTrans, NodeV3.nodeConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  simp only [mkR] at hC'
  rcases next_row hn hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · have hD' : ∀ x, x < 185 → D x = (rowCell vs (mkR vs n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    simp only [mkR] at hD'
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals node_rc3 []
    all_goals cases hdup : (rec vs n).dup <;> simp only [hdup, Bool.false_eq_true, ite_true, ite_false] at hsz ⊢
    all_goals try simp only [b2n, decide_eq_true_eq, eq_self_iff_true, ite_true, decide_true]
    all_goals (repeat' split) <;> first | omega | contradiction
  · have hD' : ∀ x, x < 185 → D x = (rowCell vs (mkR vs (n + 1) 0) x : Int) := by
      intro x hx; rw [hD x hx, X_node h3, h4]
    simp only [mkR] at hD'
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals node_rc3 []
    all_goals cases hdup : (rec vs n).dup <;> simp only [hdup, Bool.false_eq_true, ite_true, ite_false] at hsz ⊢
    all_goals try simp only [b2n, decide_eq_true_eq, eq_self_iff_true, ite_true, decide_true]
    all_goals (repeat' split) <;> first | omega | contradiction
  · have hD' : ∀ x, x < 185 → D x = (sumCell (total vs) x : Int) := by
      intro x hx; rw [hD x hx, h3, X_sum]
    have htot : total vs = szBefore vs (n + 1) := by simp only [total, h2]
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals node_rc3 []
    all_goals try simp only [sumCell, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals cases hdup : (rec vs n).dup <;> simp only [hdup, Bool.false_eq_true, ite_true, ite_false] at hsz ⊢
    all_goals try simp only [b2n, decide_eq_true_eq, eq_self_iff_true, ite_true, decide_true]
    all_goals (repeat' split) <;> first | omega | contradiction

set_option maxHeartbeats 4000000 in
theorem cTrans_sum : RowGoal vs H NodeV3.cTrans (R vs) := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 185 → C x = (sumCell (total vs) x : Int) := by
    intro x hx; rw [hC x hx, X_sum]
  simp only [NodeV3.cTrans, NodeV3.nodeConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  by_cases hl : R vs + 1 = H
  · subst hl
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals simp only [sumCell, Nat.reduceEqDiff, ite_true, ite_false, Int.mul_zero, Int.zero_mul,
      Int.add_zero, Int.zero_add]
    all_goals first | (simp; done) | omega
  · have hD' : ∀ x, x < 185 → D x = (padCell (total vs) x : Int) := by
      intro x hx; rw [hD x hx, Nat.mod_eq_of_lt (by omega), X_pad (by omega)]
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals simp only [sumCell, padCell, Nat.reduceEqDiff, ite_true, ite_false, Int.mul_zero, Int.zero_mul,
      Int.add_zero, Int.zero_add, show R vs + 1 = H ↔ False from ⟨hl, False.elim⟩]
    all_goals first | (simp; done) | omega

set_option maxHeartbeats 4000000 in
theorem cTrans_pad {q : Nat} (hqp : R vs < q) (hq : q < H) : RowGoal vs H NodeV3.cTrans q := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 185 → C x = (padCell (total vs) x : Int) := by
    intro x hx; rw [hC x hx, X_pad hqp]
  simp only [NodeV3.cTrans, NodeV3.nodeConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  by_cases hl : q + 1 = H
  · subst hl
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals simp only [padCell, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals first | (simp; done) | omega
  · have hD' : ∀ x, x < 185 → D x = (padCell (total vs) x : Int) := by
      intro x hx; rw [hD x hx, Nat.mod_eq_of_lt (by omega), X_pad (by omega)]
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC', hD']
    all_goals simp only [padCell, Nat.reduceEqDiff, ite_true, ite_false, show q + 1 = H ↔ False from ⟨hl, False.elim⟩]
    all_goals first | (simp; done) | omega

theorem cTrans_ok : GroupOk vs H NodeV3.cTrans :=
  groupOk_of vs H (fun _ h => cTrans_node ok hHR h) (cTrans_sum ok hHR) (fun _ h1 h2 => cTrans_pad ok hHR h1 h2)

end

end NodeGen3

end ZkFormal.NearV3.Render
