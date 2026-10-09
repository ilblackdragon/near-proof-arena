import ZkFormal.NearV3.Render.Node.FieldsS
import ZkFormal.NearV3.Render.Node.FieldsA
import ZkFormal.NearV3.Render.Node.FieldsB
import ZkFormal.NearV3.Render.Node.FieldsM

/-!
# ZkFormal.NearV3.Render.Node.Fields — `cFields`: field succession, lengths, flags
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (wOf lwOf len_facts)

namespace NodeGen3

section
variable {vs : List NodeS3} (ok : NodeOk vs) {H : Nat} (hHR : R vs + 1 ≤ H)
include ok hHR

theorem cFields_node {q : Nat} (hqn : q < R vs) : RowGoal vs H NodeV3.cFields q := by
  intro C D P hC hD ex hex
  rw [cFields_split] at hex
  rcases List.mem_append.1 hex with hex | hex
  · rcases List.mem_append.1 hex with hex | hex
    · exact cfS_node ok hHR hqn C D P hC hD ex hex
    · rcases List.mem_append.1 hex with hex | hex
      · exact cfA_node ok hHR hqn C D P hC hD ex hex
      · exact cfB_node ok hHR hqn C D P hC hD ex hex
  · exact cfM_node ok hHR hqn C D P hC hD ex hex

set_option maxHeartbeats 4000000 in
theorem cFields_other {q : Nat} (hq : R vs ≤ q) (hqH : q < H) : RowGoal vs H NodeV3.cFields q := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 185 → C x = (if q = R vs then (sumCell (total vs) x : Int)
      else (padCell (total vs) x : Int)) := by
    intro x hx; rw [hC x hx]
    split
    · subst q; rw [X_sum]
    · rw [X_pad (by omega)]
  simp only [NodeV3.cFields, NodeV3.states, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  generalize total vs = T at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev3 [hC']
  all_goals split <;> simp [sumCell, padCell]

theorem cFields_ok : GroupOk vs H NodeV3.cFields :=
  groupOk_of vs H (fun _ h => cFields_node ok hHR h) (cFields_other ok hHR (Nat.le_refl _) (by omega))
    (fun _ h1 h2 => cFields_other ok hHR (by omega) h2)

end

end NodeGen3

end ZkFormal.NearV3.Render
