import ZkFormal.NearV3.Render.Node.Facts

/-!
# ZkFormal.NearV3.Render.Node.Rows — `cRows` and `cBool`
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

theorem state_sum (f : F) : ((b2n (decide (f.state = 14)) : Nat) : Int) + (((b2n (decide (f.state = 15)) : Nat) : Int) +
    (((b2n (decide (f.state = 16)) : Nat) : Int) + (((b2n (decide (f.state = 17)) : Nat) : Int) +
    (((b2n (decide (f.state = 18)) : Nat) : Int) + (((b2n (decide (f.state = 19)) : Nat) : Int) +
    (((b2n (decide (f.state = 20)) : Nat) : Int) + (((b2n (decide (f.state = 21)) : Nat) : Int) +
    (((b2n (decide (f.state = 22)) : Nat) : Int) + ((0 : Nat) : Int))))))))) = 1 := by
  cases f <;> rfl

section
variable {vs : List NodeS3} (ok : NodeOk vs) {H : Nat} (hHR : R vs + 1 ≤ H)
include ok hHR

theorem cRows_node {q : Nat} (hqn : q < R vs) : RowGoal vs H NodeV3.cRows q := by
  intro C D P hC hD ex hex
  simp only [NodeV3.cRows, List.mem_cons, List.not_mem_nil, or_false] at hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hT := typeOf_sum (rec vs n).v
  have htag := tag_iff ok hn hp
  have hlast := last_iff ok hn hp
  have hlen := len_eq ok hn
  have hidx := (fmem ok hn hp).2
  have hq0 : off vs n + p = 0 ↔ n = 0 ∧ p = 0 := first_row
  have hsz0 : n = 0 → szBefore vs n = 0 := fun h => by subst h; rfl
  have hp0 : p = 0 → (layN vs n).getD p default = (F.tag, 0) := first_idx ok hn hp
  have hD := rdepth ok hn
  have hb9 := bits9 ((rec vs n).depth + 112) (by omega)
  have hlt : off vs n + p < H := by omega
  simp only [mkR] at hC'
  by_cases h0 : p = 0
  · rw [hp0 h0] at hC' hidx hlast
    subst h0
    simp only [F.state, Node.sTAG, Nat.reduceEqDiff, false_and, iff_false] at hlast
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals node_rc3 []
    all_goals try simp only [F.state, Node.sTAG, F.len, NodeGen.F.nib, NodeGen.F.isTag, Bool.false_eq_true, ite_true,
      ite_false, b2n, decide_true, decide_false, Nat.reduceEqDiff, Bool.or_eq_true, beq_iff_eq, false_or, true_or]
    all_goals (repeat' split) <;> first | omega | (simp only [decide_eq_true_eq] at *; omega) | (simp only [bitOf] at *; omega)
  · have hml : ((layN vs n).getD p default).1.state = 22 →
        ((layN vs n).getD p default).1.len (hplenOf (rec vs n).v) = 8 := by
      generalize ((layN vs n).getD p default).1 = f
      cases f <;> simp [F.state, F.len, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
        Node.sCH, Node.sMEM]
    generalize hfi : (layN vs n).getD p default = fi at hC' hidx htag hlast hml
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals node_rc3 []
    · omega
    · rw [state_sum]; rfl
    all_goals try simp only [b2n, decide_eq_true_eq]
    all_goals (repeat' split) <;> omega

theorem cRows_sum : RowGoal vs H NodeV3.cRows (R vs) := by
  intro C D P hC hD ex hex
  simp only [NodeV3.cRows, List.mem_cons, List.not_mem_nil, or_false] at hex
  have hC' : ∀ x, x < 185 → C x = (sumCell (total vs) x : Int) := by
    intro x hx; rw [hC x hx, X_sum]
  have h1 := R_pos ok
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals node_ev3 [hC']
  all_goals simp only [sumCell, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals (repeat' split) <;> omega

theorem cRows_pad {q : Nat} (hqp : R vs < q) (hq : q < H) : RowGoal vs H NodeV3.cRows q := by
  intro C D P hC hD ex hex
  simp only [NodeV3.cRows, List.mem_cons, List.not_mem_nil, or_false] at hex
  have hC' : ∀ x, x < 185 → C x = (padCell (total vs) x : Int) := by
    intro x hx; rw [hC x hx, X_pad hqp]
  have h1 := R_pos ok
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals node_ev3 [hC']
  all_goals simp only [padCell, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals (repeat' split) <;> omega

theorem cRows_ok : GroupOk vs H NodeV3.cRows :=
  groupOk_of vs H (fun _ h => cRows_node ok hHR h) (cRows_sum ok hHR) (fun _ h1 h2 => cRows_pad ok hHR h1 h2)

end

end NodeGen3

end ZkFormal.NearV3.Render
