import ZkFormal.Near.Render.Proof.NodeWin3

/-!
# ZkFormal.Near.Render.Proof.NodeLinks — `cLinks`: walk targets, gates, edge contents
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-- The walk target of a node: its child's for an empty-key extension with a revealed child. -/
theorem res_node {c : Claim} {e : Ext} (hg : Good c e) {n : Nat} (hn : n < e.ns.length) :
    (mkInfo c e).res.getD n n =
      if eextOf' ((mkInfo c e).nodeAt n) = true ∧ xrvOf ((mkInfo c e).nodeAt n) = true
      then xresOf (mkInfo c e) ((mkInfo c e).nodeAt n) else n := by
  rw [info_res, info_nodeAt hn]
  have hget : e.ns[n]? = some e.ns[n] := List.getElem?_eq_getElem hn
  have hg2 : e.ns.toArray.getD n (.branch none [] 0) = e.ns[n] := by simp [Array.getD_eq_getD_getElem?, hn]
  generalize e.ns[n] = nr at hget hg2
  cases nr with
  | ext k kid m =>
    cases kid with
    | node c' =>
      cases k with
      | nil =>
        rw [R_eext hg.shape hget]
        simp [eextOf', isExtR, nokeyOf, isLE, hplenOf, oddOf, b2n, xrvOf, xresOf, info_res, NodeRec.key]
        exact (info_res' c').symm
      | cons x k =>
        have : ¬ (eextOf' (.ext (x :: k) (.node c') m) = true) := by
          cases k <;> simp [eextOf', isExtR, nokeyOf, isLE, hplenOf, oddOf, b2n, NodeRec.key] <;> omega
        simp only [R, resF]; rw [hg2]; simp [this]
    | _ =>
      simp only [xrvOf, Bool.false_eq_true, and_false, ite_false, R, resF]
      rw [hg2]; cases k <;> rfl
  | _ =>
    simp only [xrvOf, eextOf', isExtR, Bool.false_eq_true, false_and, and_false, ite_false, R, resF]
    rw [hg2]

theorem branchWins_state {I : Info} {kids : List Kid} {f : F} (h : f ∈ branchWins I kids) : f.state = 21 := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins h; rfl

theorem key_branch (I : Info) (n : Nat) (v : Option VSlot) (kids : List Kid) (m : Nat) :
    F.key ∉ fieldsOf I n (.branch v kids m) := by
  intro h
  cases v <;> simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, reduceCtorEq, false_or] at h <;>
    first | (have := branchWins_state h; simp [F.state, Node.sKEY, Node.sCH] at this)
          | (rcases h with h | h <;> first | cases h | (have := branchWins_state h; simp [F.state, Node.sKEY, Node.sCH] at this))

/-- Hypotheses on a node row for the link constraints. -/
structure LinkHyp (I : Info) (r : NRec) (fst : Int) : Prop where
  hf : r.f ∈ fieldsOf I r.n (I.nodeAt r.n)
  hidx : r.idx < r.f.len (hplenOf (I.nodeAt r.n))
  hw : (I.nodeAt r.n).wf
  hnib : ∀ x ∈ (I.nodeAt r.n).key, x < 16
  hb : r.b = (NodeLay.fbytes (I.nodeAt r.n) false r.f).getD r.idx 0
  hb8 : r.b < 256
  hfst : fst = if r.n = 0 ∧ r.pos = 0 then 1 else 0
  htag : r.pos = 0 ↔ r.f.state = 14
  hres : I.res.getD r.n r.n = if eextOf' (I.nodeAt r.n) = true ∧ xrvOf (I.nodeAt r.n) = true
      then xresOf I (I.nodeAt r.n) else r.n

/-- The link constraints on a row of a fixed non-window field. -/
syntax "lnk_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| lnk_tac) => `(tactic| (
  intro ex hex
  obtain ⟨hf, hidx, hw, hnib, hb, hb8, hfst, htag, hres⟩ := h
  have hn1 := nib4 (b / 16)
  have hn2 := nib4 (b % 16)
  simp only at hb8
  simp only [Node.cLinks, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev [hC]
  all_goals node_rc []
  all_goals try simp only [hfst]
  all_goals clear hC hfst
  all_goals try simp only at hres
  all_goals try simp only [F.state, F.chw, F.win, F.nib, digOf, edgeAOf, edgeBOf, gateCell, edgeCell, Node.sTAG,
    Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, msgId] at htag ⊢
  all_goals generalize hnr : I.nodeAt rn = nr at *
  all_goals rcases nr with ⟨k, _ | _, m⟩ | ⟨k, kid, m⟩ | ⟨_ | ⟨_ | _⟩, kids, m⟩
  all_goals try (cases kid <;> rcases k with _ | ⟨x, _ | ⟨y, k⟩⟩)
  all_goals try (exfalso; simp [fieldsOf] at hf; done)
  all_goals try (exfalso; simp [fieldsOf] at hf; have := branchWins_state hf; simp [F.state, Node.sHPL, Node.sHPF,
    Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM, Node.sTAG] at this; done)
  all_goals try simp [F.len, b2n, typeOf, eextOf', xrvOf, xdeadOf, xlast0Of, isExtR, isLE, nokeyOf, oddOf, hplenOf,
    xresOf, NodeRec.key, NodeRec.touched, valWin] at htag hidx hres
  all_goals try simp [F.len, b2n, typeOf, eextOf', xrvOf, xdeadOf, xlast0Of, isExtR, isLE, nokeyOf, oddOf, hplenOf,
    xresOf, NodeRec.key, NodeRec.touched, valWin, hres, htag, Int.add_right_neg]
  all_goals first
    | omega
    | (simp [Int.add_right_neg]; done)
    | (by_cases hl : j + 1 = (k.length + 1 + 1) / 2 <;> simp [hl, Int.add_right_neg] <;> omega)
    | (by_cases hr0 : rn = 0 <;> simp [hr0, Int.add_right_neg] <;> omega)
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
    | trace_state))

set_option maxHeartbeats 8000000 in
theorem lnk_tag (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (fst : Int)
    (h : LinkHyp I ⟨rn, pos, .tag, j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .tag, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk_tac

set_option maxHeartbeats 8000000 in
theorem lnk_hpl (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (fst : Int)
    (h : LinkHyp I ⟨rn, pos, .hpl, j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .hpl, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  lnk_tac

end NodeRow

end ZkFormal.Near.Render
