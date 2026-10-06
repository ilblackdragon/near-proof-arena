import ZkFormal.NearV3.Render.Node.Win2

/-!
# ZkFormal.NearV3.Render.Node.Links — `cLinks`: walk targets, gates, edge contents (per field)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (wOf lwOf len_facts mem_len nib4)

namespace NodeGen3

/-- The walk target of a record. -/
def resOf (n : Nat) (v : NodeV3) : Nat := if eextOf v = true ∧ xrvOf v = true then xresOf v else n

/-- Hypotheses on a node row for the link constraints. -/
structure LinkHyp (vs : List NodeS3) (r : NRec) : Prop where
  hf : r.f ∈ fieldsOf (rec vs r.n).v
  hidx : r.idx < r.f.len (hplenOf (rec vs r.n).v)
  hw : (rec vs r.n).v.wf
  hb8 : r.f.nib = true → r.b < 256
  hres : (rec vs r.n).res = resOf r.n (rec vs r.n).v

syntax "lnk3_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| lnk3_tac) => `(tactic| (
  intro ex hex
  obtain ⟨hf, hidx, hw, hb8, hres⟩ := h
  have hn1 := nib4 (b / 16)
  have hn2 := nib4 (b % 16)
  simp only [NodeV3.cLinks, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev3 [hC]
  all_goals node_rc3 []
  all_goals clear hC
  all_goals try simp only [F.state, NodeGen.F.chw, NodeGen.F.win, NodeGen.F.nib, NodeGen.F.isTag, NodeGen.F.isVlen,
    NodeGen.F.isBm, NodeGen.F.isCh, NodeGen.F.isVh, NodeGen.F.isMem, digOf, edgeAOf, edgeBOf, gCell, eCell,
    Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, msgId,
    resOf] at hb8 hres ⊢
  all_goals try simp only [true_implies, forall_const] at hb8
  all_goals generalize hrec : rec vs rn = s at *
  all_goals obtain ⟨nv, tau', d', res', uses', ubm', dup', hd', repE'⟩ := s
  all_goals simp only at hf hidx hw hres ⊢
  all_goals rcases nv with ⟨k, ⟨l0, h0⟩ | ⟨l0, i0, vl0, pr0, po0, wr0⟩, m⟩ | ⟨k, kid, m⟩ |
    ⟨_ | ⟨⟨l0, h0⟩ | ⟨l0, i0, vl0, pr0, po0, wr0⟩⟩, kids, m⟩
  all_goals try (cases kid <;> rcases k with _ | ⟨x, _ | ⟨y, k⟩⟩)
  all_goals try (exfalso; simp [fieldsOf] at hf; done)
  all_goals try (exfalso; simp [fieldsOf] at hf; obtain ⟨_, _, _, _, _, _, he⟩ := mem_branchWins hf; cases he; done)
  all_goals try simp [F.len, b2n, typeOf, eextOf, xrvOf, xdeadOf, xlast0Of, isExt, isLeaf, isLE, nokeyOf, oddOf,
    hplenOf, xresOf, xtgtOf, xtgJOf, sOf, keyOf, tvOf, vidOf, vlenOf, twOf, NodeV3.value, valWin, kidWin, kidsOf,
    nRev] at hidx hres
  all_goals try simp [F.len, b2n, typeOf, eextOf, xrvOf, xdeadOf, xlast0Of, isExt, isLeaf, isLE, nokeyOf, oddOf,
    hplenOf, xresOf, xtgtOf, xtgJOf, sOf, keyOf, tvOf, vidOf, vlenOf, twOf, NodeV3.value, valWin, kidWin, kidsOf,
    nRev, hres, Int.add_right_neg, EK_KEY, EK_DOWN, EK_VAL, EK_LEND, SYM_END, K_NPRE, K_VPRE]
  all_goals first
    | omega
    | (simp [Int.add_right_neg]; done)
    | (by_cases hl : j + 1 = (k.length + 1 + 1) / 2 <;> simp [hl, Int.add_right_neg] <;> omega)
    | (by_cases hj : j = 0 <;> simp [hj, Int.add_right_neg] <;> omega)
    | (have hI : ((k.length : Int)) % 2 = (((k.length % 2 : Nat)) : Int) := by omega
       simp only [hI]
       rcases Nat.mod_two_eq_zero_or_one k.length with ho | ho <;> simp only [ho] <;> simp <;> omega)
    | (have hI : ((k.length : Int) + 1 + 1) % 2 = (((k.length + 1 + 1) % 2 : Nat) : Int) := by omega
       simp only [hI]
       rcases Nat.mod_two_eq_zero_or_one (k.length + 1 + 1) with ho | ho <;>
         simp only [ho, show ¬ (k.length + 1 + 1 < 2) by omega, ite_false] <;> simp <;> omega)
    | (simp [Int.add_right_neg] <;> omega)
    | (simp only [show ¬ (k.length + 1 + 1 < 2) by omega, ite_false]; simp; done)
    | (cases dup' <;> by_cases hp0 : pos = 0 <;> simp [hp0])
    | trace_state))

set_option maxHeartbeats 16000000 in
theorem lnk_tag (vs : List NodeS3) (rn pos j b pb : Nat) (h : LinkHyp vs ⟨rn, pos, .tag, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .tag, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac

set_option maxHeartbeats 16000000 in
theorem lnk_hpl (vs : List NodeS3) (rn pos j b pb : Nat) (h : LinkHyp vs ⟨rn, pos, .hpl, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .hpl, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac

set_option maxHeartbeats 16000000 in
theorem lnk_hpf (vs : List NodeS3) (rn pos j b pb : Nat) (h : LinkHyp vs ⟨rn, pos, .hpf, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .hpf, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac

set_option maxHeartbeats 16000000 in
theorem lnk_key (vs : List NodeS3) (rn pos j b pb : Nat) (h : LinkHyp vs ⟨rn, pos, .key, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .key, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac

set_option maxHeartbeats 16000000 in
theorem lnk_vlen (vs : List NodeS3) (rn pos j b pb : Nat) (h : LinkHyp vs ⟨rn, pos, .vlen, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .vlen, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac

set_option maxHeartbeats 16000000 in
theorem lnk_bm (vs : List NodeS3) (rn pos j b pb : Nat) (h : LinkHyp vs ⟨rn, pos, .bm, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .bm, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac

set_option maxHeartbeats 16000000 in
theorem lnk_mem (vs : List NodeS3) (rn pos j b pb : Nat) (h : LinkHyp vs ⟨rn, pos, .mem, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .mem, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac
syntax "lnk3ch_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| lnk3ch_tac) => `(tactic| (
  intro ex hex
  obtain ⟨hf, hidx, hw, hb8, hres⟩ := h
  have hn1 := nib4 (b / 16)
  have hn2 := nib4 (b % 16)
  simp only [NodeV3.cLinks, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev3 [hC]
  all_goals node_rc3 []
  all_goals clear hC
  all_goals try simp only [F.state, NodeGen.F.chw, NodeGen.F.win, NodeGen.F.nib, NodeGen.F.isTag, NodeGen.F.isVlen,
    NodeGen.F.isBm, NodeGen.F.isCh, NodeGen.F.isVh, NodeGen.F.isMem, digOf, edgeAOf, edgeBOf, gCell, eCell,
    Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, msgId,
    resOf] at hb8 hres ⊢
  all_goals try simp only [true_implies, forall_const] at hb8
  all_goals generalize hrec : rec vs rn = s at *
  all_goals obtain ⟨nv, tau', d', res', uses', ubm', dup', hd', repE'⟩ := s
  all_goals simp only at hf hidx hw hres ⊢
  all_goals simp only at hshape
  all_goals subst hshape
  all_goals try (rcases k with _ | ⟨x, _ | ⟨y, k⟩⟩)
  all_goals try (rcases v0 with _ | ⟨⟨l0, h0⟩ | ⟨l0, i0, vl0, pr0, po0, wr0⟩⟩)
  all_goals try (exfalso; simp [fieldsOf] at hf; done)
  all_goals try (exfalso; simp [fieldsOf] at hf; obtain ⟨_, _, _, _, _, _, he⟩ := mem_branchWins hf; cases he; done)
  all_goals try simp [F.len, b2n, typeOf, eextOf, xrvOf, xdeadOf, xlast0Of, isExt, isLeaf, isLE, nokeyOf, oddOf,
    hplenOf, xresOf, xtgtOf, xtgJOf, sOf, keyOf, tvOf, vidOf, vlenOf, twOf, NodeV3.value, valWin, kidWin, kidsOf,
    nRev] at hidx hres
  all_goals try simp [F.len, b2n, typeOf, eextOf, xrvOf, xdeadOf, xlast0Of, isExt, isLeaf, isLE, nokeyOf, oddOf,
    hplenOf, xresOf, xtgtOf, xtgJOf, sOf, keyOf, tvOf, vidOf, vlenOf, twOf, NodeV3.value, valWin, kidWin, kidsOf,
    nRev, hres, Int.add_right_neg, EK_KEY, EK_DOWN, EK_VAL, EK_LEND, SYM_END, K_NPRE, K_VPRE]
  all_goals first
    | omega
    | (simp [Int.add_right_neg]; done)
    | (by_cases hl : j + 1 = (k.length + 1 + 1) / 2 <;> simp [hl, Int.add_right_neg] <;> omega)
    | (by_cases hj : j = 0 <;> simp [hj, Int.add_right_neg] <;> omega)
    | (have hI : ((k.length : Int)) % 2 = (((k.length % 2 : Nat)) : Int) := by omega
       simp only [hI]
       rcases Nat.mod_two_eq_zero_or_one k.length with ho | ho <;> simp only [ho] <;> simp <;> omega)
    | (have hI : ((k.length : Int) + 1 + 1) % 2 = (((k.length + 1 + 1) % 2 : Nat) : Int) := by omega
       simp only [hI]
       rcases Nat.mod_two_eq_zero_or_one (k.length + 1 + 1) with ho | ho <;>
         simp only [ho, show ¬ (k.length + 1 + 1 < 2) by omega, ite_false] <;> simp <;> omega)
    | (simp [Int.add_right_neg] <;> omega)
    | (simp only [show ¬ (k.length + 1 + 1 < 2) by omega, ite_false]; simp; done)
    | (cases dup' <;> by_cases hp0 : pos = 0 <;> simp [hp0])
    | (rcases (show j0 = 0 ∨ j0 = 1 ∨ j0 = 2 ∨ j0 = 3 ∨ j0 = 4 ∨ j0 = 5 ∨ j0 = 6 ∨ j0 = 7 ∨ j0 = 8 ∨ j0 = 9 ∨
          j0 = 10 ∨ j0 = 11 ∨ j0 = 12 ∨ j0 = 13 ∨ j0 = 14 ∨ j0 = 15 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (by_cases hj : j = 0) <;> simp [hj] <;> omega)
    | trace_state))


set_option maxHeartbeats 16000000 in
theorem lnk_vh (vs : List NodeS3) (rn pos j b pb : Nat) (w : Win) (h : LinkHyp vs ⟨rn, pos, .vh w, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .vh w, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk3_tac

theorem ch_cases (v : NodeV3) (w : Win) (hf : F.ch w ∈ fieldsOf v) (hw : v.wf) :
    (∃ k kid m, v = .ext k kid m ∧ w = kidWin kid 0 true none) ∨
    (∃ sv kids m j0 kk, v = .branch sv kids m ∧ j0 < 16 ∧ kk ≠ .none ∧
      w = kidWin kk (popK (kids.take j0)) (popK (kids.take j0) + 1 = popK kids) (some j0)) := by
  cases v with
  | leaf k sv m => simp [fieldsOf] at hf
  | ext k kid m => simp [fieldsOf] at hf; exact .inl ⟨k, kid, m, rfl, hf⟩
  | branch sv kids m =>
    have hb' : F.ch w ∈ branchWins kids := by cases sv <;> simpa [fieldsOf] using hf
    obtain ⟨j0, k, hj0, _, hkn, rfl⟩ := branch_win kids w hb'
    exact .inr ⟨sv, kids, m, j0, k, rfl, by have : kids.length = 16 := hw.1; omega, hkn, rfl⟩

set_option maxHeartbeats 16000000 in
theorem lnk_ch_ext (vs : List NodeS3) (rn pos j b pb : Nat) (k : List Nat) (kid0 : NKid) (m0 : List Nat)
    (hshape : (rec vs rn).v = .ext k kid0 m0)
    (h : LinkHyp vs ⟨rn, pos, .ch (kidWin kid0 0 true none), j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .ch (kidWin kid0 0 true none), j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  cases kid0 <;> lnk3ch_tac

set_option maxHeartbeats 16000000 in
theorem lnk_ch_br (vs : List NodeS3) (rn pos j b pb : Nat) (v0 : Option NSlot3) (kids0 : List NKid) (m0 : List Nat)
    (j0 : Nat) (kk : NKid) (hshape : (rec vs rn).v = .branch v0 kids0 m0) (hj0 : j0 < 16) (hkk : kk ≠ .none)
    (h : LinkHyp vs ⟨rn, pos, .ch (kidWin kk (popK (kids0.take j0)) (popK (kids0.take j0) + 1 = popK kids0)
      (some j0)), j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .ch (kidWin kk (popK (kids0.take j0))
      (popK (kids0.take j0) + 1 = popK kids0) (some j0)), j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  cases kk
  · exact absurd rfl hkk
  all_goals lnk3ch_tac

end NodeGen3

end ZkFormal.NearV3.Render
