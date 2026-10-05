import ZkFormal.Near.Render.Proof.NodeWin2

/-!
# ZkFormal.Near.Render.Proof.NodeWin3 — `cWindows`: window constants, window index; assembly
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-- The window transitions. -/
abbrev wTr : List Expr :=
  Node.windowConst.map (fun x => mul3 (c Node.sCH) (Dsl.not (c Node.fe)) (sub (n x) (c x))) ++
  [ .mul (mul3 (c Node.fe) (Dsl.not (c Node.sCH)) (n Node.sCH)) (n Node.w),
    .mul (mul3 (c Node.fe) (c Node.sCH) (n Node.sCH)) (sub (n Node.w) (.add (c Node.w) (k 1))) ]

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

set_option maxHeartbeats 4000000 in
theorem wTr_node {q : Nat} (hqn : q < RN c e) : RowGoal c e wTr q := by
  intro C D P hC hD ex hex
  have hRH := RN_lt (c := c) (e := e)
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off (mkInfo c e) n + p + 1) % HN c e = off (mkInfo c e) n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hw := nodeAt_wf hg hs hn
  have hidx := (fmem hg hs hn hp).2
  dsimp only [mkR] at hidx
  have hsr := state_range ((NodeLay.layN (mkInfo c e) n).getD p default).1
  simp only [wTr, Node.windowConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  generalize HN c e = H at *
  rcases next_row hn hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · have hD' : ∀ x, x < 163 → D x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    have hadj := lay_adj hw h1
    have hsr' := state_range ((NodeLay.layN (mkInfo c e) n).getD (p + 1) default).1
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals try simp only [rc_w', rc_lastw']
    all_goals node_rc []
    all_goals rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    all_goals first
      | (simp only [a1, a2]; simp [Int.add_right_neg]; done)
      | (simp only [a1, a2, b2n, decide_eq_true_eq]; (repeat' split) <;> omega)
      | (obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3
         clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16
         simp only [b2n, decide_eq_true_eq]; (repeat' split) <;> omega)
  · have hD' : ∀ x, x < 163 → D x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) (n + 1) 0) x : Int) := by
      intro x hx; rw [hD x hx, X_node h3, h4]
    have hlast := (last_iff hg hs hn hp).1 h1
    have hl9 := mem_len ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n)) hlast.1
    have htag := (tag_iff hg hs h2 (p := 0) (by have := layN_pos (mkInfo c e) (n + 1); omega)).2 rfl
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals try simp only [rc_w', rc_lastw']
    all_goals node_rc []
    all_goals simp only [hlast.1, hlast.2, hl9, htag, b2n]
    all_goals simp
  · have hD' : ∀ x, x < 163 → D x = (sumCell (totalOf (mkInfo c e)) x : Int) := by
      intro x hx; rw [hD x hx, h3, X_sum]
    have hlast := (last_iff hg hs hn hp).1 h1
    have hl9 := mem_len ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n)) hlast.1
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals try simp only [rc_w', rc_lastw']
    all_goals node_rc []
    all_goals simp only [hlast.1, hlast.2, hl9, b2n]
    all_goals simp [sumCell, Node.sumr, Node.sz]

theorem wTr_other {q : Nat} (hq : RN c e ≤ q) : RowGoal c e wTr q := by
  intro C D P hC hD ex hex
  have hC' := cells_other hg hs hq hC
  simp only [wTr, Node.windowConst, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  generalize totalOf (mkInfo c e) = T at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev [hC']
  all_goals split <;> simp [sumCell, padCell, Node.sumr, Node.sz]

theorem wTr_ok : GroupOk c e wTr :=
  groupOk_of (fun _ h => wTr_node hg hs h) (wTr_other hg hs (Nat.le_refl _)) (fun _ h1 _ => wTr_other hg hs (by omega))

theorem wLoc_ok : GroupOk c e wLoc := by
  apply groupOk_of
  · intro q hqn C D P hC hD ex hex
    obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
    have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
      intro x hx; rw [hC x hx, X_node hqn, hr]
    exact wLoc_rec _ _ _ (fmem hg hs hn hp).1 (nodeAt_wf hg hs hn) (row_b hg hs hn hp) (row_pb hg hs hn hp)
      C D _ _ _ P hC' ex hex
  · intro C D P hC hD ex hex
    have hC' := cells_other hg hs (Nat.le_refl _) hC
    simp only [wLoc, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC']
    all_goals simp [sumCell, padCell, Node.sumr, Node.sz]
  · intro q hq _ C D P hC hD ex hex
    have hC' := cells_other hg hs (Nat.le_of_lt hq) hC
    simp only [wLoc, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC']
    all_goals split <;> simp [sumCell, padCell, Node.sumr, Node.sz]

/-- **`cWindows`.** -/
theorem cWindows_ok : GroupOk c e Node.cWindows := by
  intro q hq C D P hC hD ex hex
  have h : ex ∈ wLoc ∨ ex ∈ wShift ∨ ex ∈ wUnrev ∨ ex ∈ wTr := by
    simp only [Node.cWindows, List.mem_append] at hex
    rcases hex with (((h | h) | h) | h) | h
    · left; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [wLoc]
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (List.mem_append_left _ h)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (left; simp [wLoc]; done)
        | (right; right; right; simp [wTr]; done)
  rcases h with h | h | h | h
  · exact wLoc_ok hg hs q hq C D P hC hD ex h
  · exact wShift_ok hg hs q hq C D P hC hD ex h
  · exact wUnrev_ok hg hs q hq C D P hC hD ex h
  · exact wTr_ok hg hs q hq C D P hC hD ex h

end

end NodeRow

end ZkFormal.Near.Render
