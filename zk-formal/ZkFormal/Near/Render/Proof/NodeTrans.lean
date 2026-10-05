import ZkFormal.Near.Render.Proof.NodeRows

/-!
# ZkFormal.Near.Render.Proof.NodeTrans — `cTrans`: node-constant columns, node succession, revealed size
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

theorem nodeSz_eq (I : Info) (n : Nat) :
    nodeSz I n = (I.pre.getD n []).length + 72 * b2n (I.nodeAt n).touched := by
  simp only [nodeSz, b2n]; split <;> simp_all

theorem bitOf_le1 (x i : Nat) : bitOf x i ≤ 1 := by unfold bitOf; omega

theorem bool_one (v : Nat) (h : v ≤ 1) : ((1 : Nat) : Int) * ((v : Int) * ((v : Int) + -((1 : Nat) : Int))) = 0 := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> rfl

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

set_option maxHeartbeats 4000000 in
theorem cTrans_node {q : Nat} (hqn : q < RN c e) : RowGoal c e Node.cTrans q := by
  intro C D P hC hD ex hex
  have hRH := RN_lt (c := c) (e := e)
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off (mkInfo c e) n + p + 1) % HN c e = off (mkInfo c e) n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hlen := len_eq hg hs hn
  have hsz := szBefore_succ (mkInfo c e) n
  have hnsz := nodeSz_eq (mkInfo c e) n
  have hlast : off (mkInfo c e) n + p + 1 ≠ HN c e := by omega
  simp only [Node.cTrans, Node.nodeConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  generalize HN c e = H at *
  rcases next_row hn hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · have hD' : ∀ x, x < 163 → D x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals node_rc []
    all_goals generalize b2n ((mkInfo c e).nodeAt n).touched = tv at *
    all_goals try simp only [b2n, decide_eq_true_eq, eq_self_iff_true, ite_true, decide_true]
    all_goals (repeat' split) <;> omega
  · have hD' : ∀ x, x < 163 → D x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) (n + 1) 0) x : Int) := by
      intro x hx; rw [hD x hx, X_node h3, h4]
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals node_rc []
    all_goals generalize b2n ((mkInfo c e).nodeAt n).touched = tv at *
    all_goals try simp only [b2n, decide_eq_true_eq, eq_self_iff_true, ite_true, decide_true]
    all_goals (repeat' split) <;> omega
  · have hD' : ∀ x, x < 163 → D x = (sumCell (totalOf (mkInfo c e)) x : Int) := by
      intro x hx; rw [hD x hx, h3, X_sum]
    have htot : totalOf (mkInfo c e) = szBefore (mkInfo c e) (n + 1) := by
      simp only [totalOf, NodeInfo.info_N, h2]
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals node_rc []
    all_goals try simp only [sumCell, Node.sumr, Node.sz, Nat.reduceEqDiff, Nat.reduceLeDiff, ite_true, ite_false,
      and_false, false_and, and_true]
    all_goals generalize b2n ((mkInfo c e).nodeAt n).touched = tv at *
    all_goals try simp only [b2n, decide_eq_true_eq, eq_self_iff_true, ite_true, decide_true]
    all_goals (repeat' split) <;> omega

theorem bits22 (v : Nat) (h : v < 2 ^ 22) :
    ((2 ^ 0 * bitOf v 0 + (2 ^ 1 * bitOf v 1 + (2 ^ 2 * bitOf v 2 + (2 ^ 3 * bitOf v 3 + (2 ^ 4 * bitOf v 4 +
      (2 ^ 5 * bitOf v 5 + (2 ^ 6 * bitOf v 6 + (2 ^ 7 * bitOf v 7 + (2 ^ 8 * bitOf v 8 + (2 ^ 9 * bitOf v 9 +
      (2 ^ 10 * bitOf v 10 + (2 ^ 11 * bitOf v 11 + (2 ^ 12 * bitOf v 12 + (2 ^ 13 * bitOf v 13 +
      (2 ^ 14 * bitOf v 14 + (2 ^ 15 * bitOf v 15 + (2 ^ 16 * bitOf v 16 + (2 ^ 17 * bitOf v 17 +
      (2 ^ 18 * bitOf v 18 + (2 ^ 19 * bitOf v 19 + (2 ^ 20 * bitOf v 20 + (2 ^ 21 * bitOf v 21 + 0)))))))))))))))))))))) : Nat) = v := by
  simp only [bitOf]; omega

end

end NodeRow

end ZkFormal.Near.Render
