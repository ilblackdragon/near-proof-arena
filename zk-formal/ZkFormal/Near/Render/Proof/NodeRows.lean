import ZkFormal.Near.Render.Proof.NodeRc

/-!
# ZkFormal.Near.Render.Proof.NodeRows — `cRows`: row kinds, first/last rows, node start/end
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-! ## Facts about node rows -/

theorem typeOf_sum (nr : NodeRec) : (typeOf nr).1 + (typeOf nr).2.1 + (typeOf nr).2.2.1 + (typeOf nr).2.2.2 = 1 := by
  cases nr with
  | leaf => rfl
  | ext => rfl
  | branch v => cases v <;> rfl

theorem state_range (f : F) : 14 ≤ f.state ∧ f.state ≤ 22 := by
  cases f <;> simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH,
    Node.sMEM]

theorem state_sum (f : F) : ((b2n (decide (f.state = 14)) : Nat) : Int) + (((b2n (decide (f.state = 15)) : Nat) : Int) +
    (((b2n (decide (f.state = 16)) : Nat) : Int) + (((b2n (decide (f.state = 17)) : Nat) : Int) +
    (((b2n (decide (f.state = 18)) : Nat) : Int) + (((b2n (decide (f.state = 19)) : Nat) : Int) +
    (((b2n (decide (f.state = 20)) : Nat) : Int) + (((b2n (decide (f.state = 21)) : Nat) : Int) +
    (((b2n (decide (f.state = 22)) : Nat) : Int) + ((0 : Nat) : Int))))))))) = 1 := by
  cases f <;> rfl

theorem isTag_iff (f : F) : f.isTag = true ↔ f.state = 14 := by
  cases f <;> simp [F.isTag, F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
    Node.sCH, Node.sMEM]

theorem mem_len (f : F) (h : Nat) (hf : f.state = 22) : f.len h = 8 := by
  cases f <;> simp_all [F.state, F.len, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
    Node.sCH, Node.sMEM]

theorem tag_len (f : F) (h : Nat) (hf : f.state = 14) : f.len h = 1 := by
  cases f <;> simp_all [F.state, F.len, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
    Node.sCH, Node.sMEM]

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e) {n p : Nat} (hn : n < e.ns.length)
  (hp : p < (NodeLay.layN (mkInfo c e) n).length)
include hg hs hn hp

/-- Position `0` is the `TAG` byte and only it. -/
theorem tag_iff : ((NodeLay.layN (mkInfo c e) n).getD p default).1.state = 14 ↔ p = 0 := by
  rw [← isTag_iff]; exact NodeTr.lay_tag _ n p hp

/-- The last position is the last `MEM` byte and only it. -/
theorem last_iff : p + 1 = (NodeLay.layN (mkInfo c e) n).length ↔
    (((NodeLay.layN (mkInfo c e) n).getD p default).1.state = 22 ∧ ((NodeLay.layN (mkInfo c e) n).getD p default).2 = 7) :=
  lay_last_iff (nodeAt_wf hg hs hn) hp

end

theorem RN_pos {c : Claim} {e : Ext} (hg : Good c e) : 1 ≤ RN c e := by
  rw [RN_off]; exact off_pos hg.shape.nonempty

/-! ## `cRows` -/

/-- The goal of a group on row `q` (after `intro`). -/
abbrev RowGoal (c : Claim) (e : Ext) (es : List Expr) (q : Nat) : Prop :=
  ∀ (C D P : Nat → Int), (∀ x, x < 163 → C x = X c e q x) →
    (∀ x, x < 163 → D x = X c e ((q + 1) % HN c e) x) →
    ∀ ex ∈ es, ev C D (if q = 0 then 1 else 0) (if q + 1 = HN c e then 1 else 0)
      (if q + 1 = HN c e then 0 else 1) P ex = 0

theorem groupOk_of {c : Claim} {e : Ext} {es : List Expr}
    (h1 : ∀ q, q < RN c e → RowGoal c e es q) (h2 : RowGoal c e es (RN c e))
    (h3 : ∀ q, RN c e < q → q < HN c e → RowGoal c e es q) : GroupOk c e es := by
  intro q hq
  rcases Nat.lt_trichotomy q (RN c e) with h | rfl | h
  · exact h1 q h
  · exact h2
  · exact h3 q h hq

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

theorem cRows_node {q : Nat} (hqn : q < RN c e) : RowGoal c e Node.cRows q := by
  intro C D P hC hD ex hex
  simp only [Node.cRows, List.mem_cons, List.not_mem_nil, or_false] at hex
  have hRH := RN_lt (c := c) (e := e)
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hT := typeOf_sum ((mkInfo c e).nodeAt n)
  have htag := tag_iff hg hs hn hp
  have hlast := last_iff hg hs hn hp
  have hlen := len_eq hg hs hn
  have hidx := (fmem hg hs hn hp).2
  dsimp only [mkR] at hidx
  have hq0 : off (mkInfo c e) n + p = 0 ↔ n = 0 ∧ p = 0 := first_row
  have hd0 : n = 0 → (mkInfo c e).depth.getD n 0 = 0 := fun h => by subst h; exact depth_root hg.shape
  have hsz0 : n = 0 → szBefore (mkInfo c e) n = 0 := fun h => by subst h; rfl
  have hmem := mem_len ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))
  have htl := tag_len ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))
  generalize HN c e = H at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals node_ev [hC']
  all_goals node_rc []
  · omega
  · rw [state_sum]; rfl
  all_goals try simp only [b2n, decide_eq_true_eq]
  all_goals (repeat' split) <;> omega

theorem cRows_sum : RowGoal c e Node.cRows (RN c e) := by
  intro C D P hC hD ex hex
  simp only [Node.cRows, List.mem_cons, List.not_mem_nil, or_false] at hex
  have hC' : ∀ x, x < 163 → C x = (sumCell (totalOf (mkInfo c e)) x : Int) := by
    intro x hx; rw [hC x hx, X_sum]
  have h1 := RN_pos hg
  generalize HN c e = H at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals node_ev [hC']
  all_goals simp only [sumCell, Node.sumr, Node.sz, Nat.reduceEqDiff, Nat.reduceLeDiff, ite_true, ite_false,
    and_false, false_and]
  all_goals (repeat' split) <;> omega

theorem cRows_pad {q : Nat} (hqp : RN c e < q) (hq : q < HN c e) : RowGoal c e Node.cRows q := by
  intro C D P hC hD ex hex
  simp only [Node.cRows, List.mem_cons, List.not_mem_nil, or_false] at hex
  have hC' : ∀ x, x < 163 → C x = (padCell (totalOf (mkInfo c e)) x : Int) := by
    intro x hx; rw [hC x hx, X_pad hqp]
  have h1 := RN_pos hg
  generalize HN c e = H at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals node_ev [hC']
  all_goals simp only [padCell, Node.sz, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals (repeat' split) <;> omega

theorem cRows_ok : GroupOk c e Node.cRows :=
  groupOk_of (fun _ h => cRows_node hg hs h) (cRows_sum hg hs) (fun _ h1 h2 => cRows_pad hg hs h1 h2)

end

end NodeRow

end ZkFormal.Near.Render
