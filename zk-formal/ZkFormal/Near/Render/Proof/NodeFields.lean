import ZkFormal.Near.Render.Proof.NodeRows

/-!
# ZkFormal.Near.Render.Proof.NodeFields — `cFields`: field succession, lengths, flags
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-- The window index / last-window flag cells of a field. -/
def wOf (f : F) : Nat := match f.chw with | some w => w.w | none => 0
def lwOf (f : F) : Nat := match f.chw with | some w => b2n w.lastw | none => 0

/-- `SuccOk` as linear facts on the cells. -/
theorem succ_facts {nr : NodeRec} {f g : F} (h : SuccOk nr f g) :
    g.state ≠ 14 ∧ f.state ≠ 22 ∧
    (f.state = 14 → (typeOf nr).1 + (typeOf nr).2.1 = 1 → g.state = 15) ∧
    (f.state = 14 → (typeOf nr).2.2.1 = 1 → g.state = 20) ∧
    (f.state = 14 → (typeOf nr).2.2.2 = 1 → g.state = 18) ∧
    (f.state = 15 → g.state = 16) ∧
    (f.state = 16 → nokeyOf nr = 0 → g.state = 17) ∧
    (f.state = 16 → nokeyOf nr = 1 → (typeOf nr).1 = 1 → g.state = 18) ∧
    (f.state = 16 → nokeyOf nr = 1 → (typeOf nr).1 = 0 → g.state = 21) ∧
    (f.state = 17 → (typeOf nr).1 = 1 → g.state = 18) ∧
    (f.state = 17 → (typeOf nr).1 = 0 → g.state = 21) ∧
    (f.state = 18 → g.state = 19) ∧
    (f.state = 19 → (typeOf nr).1 = 1 → g.state = 22) ∧
    (f.state = 19 → (typeOf nr).1 = 0 → g.state = 20) ∧
    (f.state = 20 → nochildOf nr = 1 → g.state = 22) ∧
    (f.state = 20 → nochildOf nr = 0 → g.state = 21) ∧
    (f.state = 21 → (g.state = 22 ∧ lwOf f = 1) ∨ (g.state = 21 ∧ lwOf f = 0 ∧ wOf g = wOf f + 1)) ∧
    (f.state ≠ 21 → g.state = 21 → wOf g = 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hw0 : f.state ≠ 21 → g.state = 21 → wOf g = 0 := by
    intro hf hg
    cases g <;> simp_all [F.state, Node.sCH, Node.sTAG, wOf, F.chw]
  cases f
  case mem => exact absurd h3 id
  case ch w =>
    simp only [nxt] at h3
    have hs : (F.ch w).state = 21 := rfl
    rw [hs]
    refine ⟨h1, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_, fun h => absurd rfl h⟩
    rcases h3 with ⟨h4, h5⟩ | ⟨h4, h5, h6⟩
    · left; exact ⟨h4, by simp [lwOf, F.chw, h5, b2n]⟩
    · right
      refine ⟨h4, by simp [lwOf, F.chw, h5, b2n], ?_⟩
      cases g <;> simp_all [F.state, Node.sCH, wOf, F.chw, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN,
        Node.sVH, Node.sBM, Node.sMEM]
  all_goals
    have hw := hw0 (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
      Node.sCH])
    simp only [nxt] at h3
    generalize g.state = s at h1 h3 hw ⊢
    simp only [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH,
      Node.sMEM] at h1 h3 ⊢
    have hk : nokeyOf nr = 0 ∨ nokeyOf nr = 1 := by unfold nokeyOf b2n; split <;> simp
    have hc : nochildOf nr = 0 ∨ nochildOf nr = 1 := by unfold nochildOf b2n; split <;> simp
    generalize nokeyOf nr = nk at *
    generalize nochildOf nr = nc at *
    cases nr with
    | leaf => rcases hk with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [typeOf, NodeLay.leafB] at h3 ⊢ <;> omega
    | ext => rcases hk with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [typeOf, NodeLay.leafB] at h3 ⊢ <;> omega
    | branch v => cases v <;> rcases hk with rfl | rfl <;> rcases hc with rfl | rfl <;>
        simp [typeOf, NodeLay.leafB] at h3 ⊢ <;> omega

/-! ## Node flags -/

theorem bmv_lt (nr : NodeRec) (hw : nr.wf) : bmvOf nr < 2 ^ 16 := by
  unfold bmvOf
  split
  · decide
  · cases nr with
    | leaf => simp [isLE] at *
    | ext => simp [isLE] at *
    | branch v kids m =>
      have := bitmap_lt kids
      rw [hw.1] at this; exact this

theorem bits_zero : ∀ (k v : Nat), v < 2 ^ k → ((List.range k).map (bitOf v)).sum = 0 → v = 0
  | 0, v, h, _ => by simp at h; omega
  | k + 1, v, h, hs => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map] at hs
    have h0 : bitOf v 0 = 0 := by omega
    have hs' : ((List.range k).map (bitOf (v / 2))).sum = 0 := by
      have : ((List.range k).map (bitOf v ∘ Nat.succ)) = (List.range k).map (bitOf (v / 2)) := by
        apply List.map_congr_left; intro i _
        simp only [Function.comp, bitOf, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
      rw [← this]; omega
    have := bits_zero k (v / 2) (by rw [Nat.pow_succ] at h; omega) hs'
    simp only [bitOf, Nat.pow_zero, Nat.div_one] at h0
    omega

theorem flag_facts (nr : NodeRec) (hw : nr.wf) :
    (nokeyOf nr = 0 ∨ hplenOf nr = 1) ∧ nokeyOf nr ≤ 1 ∧ (nochildOf nr = 0 ∨ bmvOf nr = 0) ∧
    (((typeOf nr).1 = 0 ∧ (typeOf nr).2.1 = 0) ∨ bmvOf nr = 0) ∧
    (b2n nr.touched = 0 ∨ ((typeOf nr).2.2.1 = 0 ∧ (typeOf nr).2.1 = 0)) ∧ bmvOf nr < 2 ^ 16 := by
  have hlt := bmv_lt nr hw
  refine ⟨?_, ?_, ?_, ?_, ?_, hlt⟩
  · by_cases h : (isLE nr && hplenOf nr == 1) = true
    · right
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.2
    · left
      simp only [nokeyOf, b2n, h, Bool.false_eq_true, ite_false]
  · simp only [nokeyOf, b2n]; split <;> omega
  · by_cases h : (!isLE nr && popOf nr == 0) = true
    · right
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have h2 := h.2
      unfold popOf at h2
      rw [foldl_sum, Nat.zero_add] at h2
      exact bits_zero 16 _ hlt h2
    · left
      simp only [nochildOf, b2n, h, Bool.false_eq_true, ite_false]
  · cases nr with
    | leaf => right; rfl
    | ext => right; rfl
    | branch v => cases v <;> left <;> exact ⟨rfl, rfl⟩
  · cases nr with
    | leaf k v => cases v <;> first | (left; rfl) | (right; exact ⟨rfl, rfl⟩)
    | ext => left; rfl
    | branch v => cases v with
      | none => left; rfl
      | some s => cases s <;> first | (left; rfl) | (right; exact ⟨rfl, rfl⟩)

theorem len_facts (f : F) (h : Nat) : (f.state = 14 → f.len h = 1) ∧ (f.state = 15 → f.len h = 4) ∧
    (f.state = 16 → f.len h = 1) ∧ (f.state = 17 → f.len h = h - 1) ∧ (f.state = 18 → f.len h = 4) ∧
    (f.state = 19 → f.len h = 32) ∧ (f.state = 20 → f.len h = 2) ∧ (f.state = 21 → f.len h = 32) ∧
    (f.state = 22 → f.len h = 8) := by
  cases f <;> simp [F.state, F.len, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
    Node.sCH, Node.sMEM]

theorem rc_w' (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) : rowCell I u r 70 = wOf r.f := rfl
theorem rc_lastw' (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) : rowCell I u r 71 = lwOf r.f := rfl

theorem kind_facts {I : Info} {n : Nat} {f : F} (hf : f ∈ fieldsOf I n (I.nodeAt n)) :
    (f.state = 15 ∨ f.state = 16 ∨ f.state = 17 → (typeOf (I.nodeAt n)).1 + (typeOf (I.nodeAt n)).2.1 = 1) ∧
    (f.state = 18 ∨ f.state = 19 → (typeOf (I.nodeAt n)).1 + (typeOf (I.nodeAt n)).2.2.2 = 1) ∧
    (f.state = 20 → (typeOf (I.nodeAt n)).2.2.1 + (typeOf (I.nodeAt n)).2.2.2 = 1) := by
  generalize I.nodeAt n = nr at hf
  have hb : ∀ f ∈ branchWins I nr.kids, f.state = 21 := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins hf; rfl
  cases nr with
  | leaf k v m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F.state, typeOf, Node.sTAG, Node.sHPL, Node.sHPF,
      Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]
  | ext k kid m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F.state, typeOf, Node.sTAG, Node.sHPL, Node.sHPF,
      Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]
  | branch v kids m =>
    cases v with
    | none =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | hf | rfl
      · simp [F.state, typeOf, Node.sTAG]
      · simp [F.state, typeOf, Node.sBM]
      · have := hb _ (by simpa [NodeRec.kids] using hf); simp [this]
      · simp [F.state, typeOf, Node.sMEM]
    | some sv =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | hf | rfl
      · simp [F.state, typeOf, Node.sTAG]
      · simp [F.state, typeOf, Node.sVLEN]
      · simp [F.state, typeOf, Node.sVH]
      · simp [F.state, typeOf, Node.sBM]
      · have := hb _ (by simpa [NodeRec.kids] using hf); simp [this]
      · simp [F.state, typeOf, Node.sMEM]

/-! ## `cFields` -/

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

set_option maxHeartbeats 8000000 in
theorem cFields_node {q : Nat} (hqn : q < RN c e) : RowGoal c e Node.cFields q := by
  intro C D P hC hD ex hex
  have hRH := RN_lt (c := c) (e := e)
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off (mkInfo c e) n + p + 1) % HN c e = off (mkInfo c e) n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hlen := len_eq hg hs hn
  have hfm := (fmem hg hs hn hp).1
  have hidx := (fmem hg hs hn hp).2
  dsimp only [mkR] at hidx hfm
  have hw := nodeAt_wf hg hs hn
  have hsr := state_range ((NodeLay.layN (mkInfo c e) n).getD p default).1
  simp only [Node.cFields, Node.states, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  generalize HN c e = H at *
  have hex' := hex
  clear hex
  by_cases h1 : p + 1 < (NodeLay.layN (mkInfo c e) n).length
  · have h2 : off (mkInfo c e) n + p + 1 < RN c e := by
      rcases next_row hn hp with ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have h3 : (recsOf (mkInfo c e)).getD (off (mkInfo c e) n + p + 1) default = mkR (mkInfo c e) n (p + 1) := by
      rcases next_row hn hp with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      all_goals omega
    have hD' : ∀ x, x < 163 → D x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n (p + 1)) x : Int) := by
      intro x hx; rw [hD x hx, X_node h2, h3]
    have hadj := lay_adj hw h1
    have hsr' := state_range ((NodeLay.layN (mkInfo c e) n).getD (p + 1) default).1
    rcases hex' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC', hD']
    all_goals try simp only [rc_w', rc_lastw']
    all_goals node_rc []
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s10 s11 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s10 s11 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); have hF2 := (flag_facts _ hw).2.1; rcases (show nokeyOf ((mkInfo c e).nodeAt n) = 0 ∨ nokeyOf ((mkInfo c e).nodeAt n) = 1 by omega) with h | h <;> (try simp only [h]) <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s10 s11 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); have hF2 := (flag_facts _ hw).2.1; rcases (show nokeyOf ((mkInfo c e).nodeAt n) = 0 ∨ nokeyOf ((mkInfo c e).nodeAt n) = 1 by omega) with h | h <;> (try simp only [h]) <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s12 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s13 s14 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s15 s16 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s17 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases hadj with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
       · (try simp only [a1, a2]); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega)
       · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ := succ_facts a3; clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s18; have hk := kind_facts hfm; have hT := typeOf_sum ((mkInfo c e).nodeAt n); have hF2 := (flag_facts _ hw).2.1; have hnc : nochildOf ((mkInfo c e).nodeAt n) ≤ 1 := (by unfold nochildOf b2n; split <;> omega); ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases (flag_facts _ hw).1 with h | h <;> (try simp only [h]) <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases (flag_facts _ hw).2.2.1 with h | h <;> (try simp only [h, bitOf]) <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases (flag_facts _ hw).2.2.2.2.1 with h | ⟨h, h'⟩ <;> first | simp [h, h'] | simp [h])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
  · rcases hex' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC']
    all_goals try simp only [rc_w', rc_lastw']
    all_goals node_rc []
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.1; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (have hl9 := (len_facts ((NodeLay.layN (mkInfo c e) n).getD p default).1 (hplenOf ((mkInfo c e).nodeAt n))).2.2.2.2.2.2.2.2; have hlast := last_iff hg hs hn hp; ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases (flag_facts _ hw).1 with h | h <;> (try simp only [h]) <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases (flag_facts _ hw).2.2.1 with h | h <;> (try simp only [h, bitOf]) <;> ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> omega))
    · (rcases (flag_facts _ hw).2.2.2.2.1 with h | ⟨h, h'⟩ <;> first | simp [h, h'] | simp [h])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])
    · (rcases (flag_facts _ hw).2.2.2.1 with ⟨h, h'⟩ | h <;> first | simp [h, h'] | simp [h, bitOf])

set_option maxHeartbeats 4000000 in
theorem cFields_other {q : Nat} (hq : RN c e ≤ q) (hqH : q < HN c e) : RowGoal c e Node.cFields q := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 163 → C x = (if q = RN c e then (sumCell (totalOf (mkInfo c e)) x : Int)
      else (padCell (totalOf (mkInfo c e)) x : Int)) := by
    intro x hx; rw [hC x hx]
    split
    · subst q; rw [X_sum]
    · rw [X_pad (by omega)]
  simp only [Node.cFields, Node.states, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.append_assoc] at hex
  generalize HN c e = H at *
  generalize totalOf (mkInfo c e) = T at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev [hC']
  all_goals split <;> simp [sumCell, padCell, Node.sumr, Node.sz]

theorem cFields_ok : GroupOk c e Node.cFields :=
  groupOk_of (fun _ h => cFields_node hg hs h) (cFields_other hg hs (Nat.le_refl _) (by have := RN_lt (c := c) (e := e); omega))
    (fun _ h1 h2 => cFields_other hg hs (by omega) h2)

end

end NodeRow

end ZkFormal.Near.Render
