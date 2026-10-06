import ZkFormal.NearV3.Render.Node.FieldsDef

/-!
# ZkFormal.NearV3.Render.Node.FieldsM — `cFields`, part `cfM`, on node rows
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

set_option maxHeartbeats 16000000 in
theorem cfM_node {q : Nat} (hqn : q < R vs) : RowGoal vs H cfM q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off vs n + p + 1) % H = off vs n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hlen := len_eq ok hn
  have hfm := (fmem ok hn hp).1
  have hidx := (fmem ok hn hp).2
  have hw := rwf ok hn
  have hsr := state_range ((layN vs n).getD p default).1
  have hkf := kind_facts hfm
  have hT := typeOf_sum (rec vs n).v
  have hF := flag_facts _ hw
  have hLf := len_facts ((layN vs n).getD p default).1 (hplenOf (rec vs n).v)
  have hlast := last_iff ok hn hp
  simp only [cfM, NodeV3.states, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  simp only [mkR] at hC'
  by_cases h1 : p + 1 < (layN vs n).length
  · have h2 : off vs n + p + 1 < R vs := by
      rcases next_row hn hp with ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have h3 : (recsOf vs).getD (off vs n + p + 1) default = mkR vs n (p + 1) := by
      rcases next_row hn hp with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      all_goals omega
    have hD' : ∀ x, x < 185 → D x = (rowCell vs (mkR vs n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    simp only [mkR] at hD'
    have hadj := lay_adj hw h1
    simp only [show layout (fieldsOf (rec vs n).v) (hplenOf (rec vs n).v) = layN vs n from rfl] at hadj
    have hsr' := state_range ((layN vs n).getD (p + 1) default).1
    rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · rw [a1, a2] at hD'
      rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals node_ev3 [hC', hD']
      all_goals try simp only [rc70, rc71]
      all_goals node_rc3 []
      all_goals fall
    · have hs := succ_facts a3
      rw [a2] at hD'
      rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals node_ev3 [hC', hD']
      all_goals try simp only [rc70, rc71]
      all_goals node_rc3 []
      all_goals fall
  · rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals try simp only [rc70, rc71]
    all_goals node_rc3 []
    all_goals fall

end

end NodeGen3

end ZkFormal.NearV3.Render
