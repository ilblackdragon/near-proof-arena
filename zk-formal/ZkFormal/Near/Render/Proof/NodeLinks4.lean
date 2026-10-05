import ZkFormal.Near.Render.Proof.NodeLinks3

/-!
# ZkFormal.Near.Render.Proof.NodeLinks4 — `cLinks` on value-window rows
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

set_option maxHeartbeats 8000000 in
theorem lnk_vh (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (w : Win) (fst : Int)
    (h : LinkHyp I ⟨rn, pos, .vh w, j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .vh w, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  have hlook := ((win_shape I rn _ w).2 h.hf).1
  lnk_tac

theorem ch_cases (I : Info) (n : Nat) (w : Win) (hf : F.ch w ∈ fieldsOf I n (I.nodeAt n))
    (hw : (I.nodeAt n).wf) :
    (∃ k kid m, I.nodeAt n = .ext k kid m ∧ w = kidWin I kid 0 true none) ∨
    (∃ v kids m j0 kk, I.nodeAt n = .branch v kids m ∧ j0 < 16 ∧ kk ≠ .none ∧
      w = kidWin I kk (popK (kids.take j0)) (popK (kids.take j0) + 1 = popK kids) (some j0)) := by
  generalize hnr : I.nodeAt n = nr at hf hw
  cases nr with
  | leaf k v m => simp [fieldsOf] at hf
  | ext k kid m => simp [fieldsOf] at hf; exact .inl ⟨k, kid, m, rfl, hf⟩
  | branch v kids m =>
    have hb' : F.ch w ∈ branchWins I kids := by cases v <;> simpa [fieldsOf, NodeRec.kids] using hf
    obtain ⟨j0, k, hj0, _, hkn, rfl⟩ := branch_win I kids hw.1 w hb'
    exact .inr ⟨v, kids, m, j0, k, rfl, hj0, hkn, rfl⟩

set_option maxHeartbeats 8000000 in
theorem lnk_ch_ext (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (fst : Int) (k0 : List Nat) (kid0 : Kid)
    (m0 : Nat) (hshape : I.nodeAt rn = .ext k0 kid0 m0)
    (h : LinkHyp I ⟨rn, pos, .ch (kidWin I kid0 0 true none), j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .ch (kidWin I kid0 0 true none), j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  cases kid0 <;> lnk_tac

set_option maxHeartbeats 8000000 in
theorem lnk_ch_br (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (fst : Int) (v0 : Option VSlot)
    (kids0 : List Kid) (m0 j0 : Nat) (kk : Kid) (hshape : I.nodeAt rn = .branch v0 kids0 m0) (hj0 : j0 < 16)
    (hkk : kk ≠ .none)
    (h : LinkHyp I ⟨rn, pos, .ch (kidWin I kk (popK (kids0.take j0)) (popK (kids0.take j0) + 1 = popK kids0) (some j0)),
      j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .ch (kidWin I kk (popK (kids0.take j0))
      (popK (kids0.take j0) + 1 = popK kids0) (some j0)), j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  cases kk
  · exact absurd rfl hkk
  all_goals lnk_tac

theorem lnk_ch (I : Info) (u : Std.HashMap Edge Nat) (rn pos j b pb : Nat) (w : Win) (fst : Int)
    (h : LinkHyp I ⟨rn, pos, .ch w, j, b, pb⟩ fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 163 → C x = (rowCell I u ⟨rn, pos, .ch w, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  rcases ch_cases I rn w h.hf h.hw with ⟨k0, kid0, m0, hshape, rfl⟩ | ⟨v0, kids0, m0, j0, kk, hshape, hj0, hkk, rfl⟩
  · exact lnk_ch_ext I u rn pos j b pb fst k0 kid0 m0 hshape h C D lst trn P hC
  · exact lnk_ch_br I u rn pos j b pb fst v0 kids0 m0 j0 kk hshape hj0 hkk h C D lst trn P hC

theorem lnk_all (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) (fst : Int) (h : LinkHyp I r fst)
    (C D : Nat → Int) (lst trn : Int) (P : Nat → Int) (hC : ∀ x, x < 163 → C x = (rowCell I u r x : Int)) :
    ∀ ex ∈ Node.cLinks, ev C D fst lst trn P ex = 0 := by
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  cases f
  · exact lnk_tag I u rn pos j b pb fst h C D lst trn P hC
  · exact lnk_hpl I u rn pos j b pb fst h C D lst trn P hC
  · exact lnk_hpf I u rn pos j b pb fst h C D lst trn P hC
  · exact lnk_key I u rn pos j b pb fst h C D lst trn P hC
  · exact lnk_vlen I u rn pos j b pb fst h C D lst trn P hC
  · exact lnk_vh I u rn pos j b pb _ fst h C D lst trn P hC
  · exact lnk_bm I u rn pos j b pb fst h C D lst trn P hC
  · exact lnk_ch I u rn pos j b pb _ fst h C D lst trn P hC
  · exact lnk_mem I u rn pos j b pb fst h C D lst trn P hC

section
variable {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e)
include hg hs

/-- **`cLinks`.** -/
theorem cLinks_ok : GroupOk c e Node.cLinks := by
  apply groupOk_of
  · intro q hqn C D P hC hD ex hex
    obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
    have hC' : ∀ x, x < 163 → C x = (rowCell (mkInfo c e) (U c e) (mkR (mkInfo c e) n p) x : Int) := by
      intro x hx; rw [hC x hx, X_node hqn, hr]
    refine lnk_all _ _ _ _ ⟨(fmem hg hs hn hp).1, (fmem hg hs hn hp).2, nodeAt_wf hg hs hn, nodeAt_nib hg hs hn,
      row_b hg hs hn hp, row_b8 hg hs hn hp, ?_, ?_, ?_⟩ C D _ _ P hC' ex hex
    · show (if off (mkInfo c e) n + p = 0 then 1 else 0 : Int) = if n = 0 ∧ p = 0 then 1 else 0
      have := first_row (c := c) (e := e) (n := n) (p := p)
      by_cases h0 : n = 0 ∧ p = 0
      · rw [if_pos (this.2 h0), if_pos h0]
      · rw [if_neg (fun h => h0 (this.1 h)), if_neg h0]
    · exact (tag_iff hg hs hn hp).symm
    · exact res_node hg hn
  · intro C D P hC hD ex hex
    have hC' := cells_other hg hs (Nat.le_refl _) hC
    have h1 := RN_pos hg
    have hz : (if RN c e = 0 then (1:Int) else 0) = 0 := by rw [if_neg (by omega)]
    simp only [Node.cLinks, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC']
    all_goals try simp only [hz]
    all_goals simp [sumCell, padCell, Node.sumr, Node.sz]
  · intro q hq _ C D P hC hD ex hex
    have hC' := cells_other hg hs (Nat.le_of_lt hq) hC
    have h1 := RN_pos hg
    simp only [Node.cLinks, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize totalOf (mkInfo c e) = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev [hC']
    all_goals split <;> simp [sumCell, padCell, Node.sumr, Node.sz]
    all_goals omega

end

end NodeRow

end ZkFormal.Near.Render
