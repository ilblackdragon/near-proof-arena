import ZkFormal.NearV3.Render.Node.ByteFacts

/-!
# ZkFormal.NearV3.Render.Node.Bytes — `cBytes`: bytes of the non-window fields, `VLEN` accumulator
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (nib4 lo8 hi8 nib_iff len_facts)

namespace NodeGen3

theorem isVlen_iff (f : F) : f.isVlen = true ↔ f.state = 18 := by
  cases f <;> simp [NodeGen.F.isVlen, F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH,
    Node.sBM, Node.sCH, Node.sMEM]

theorem isBm_iff (f : F) : f.isBm = true ↔ f.state = 20 := by
  cases f <;> simp [NodeGen.F.isBm, F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH,
    Node.sBM, Node.sCH, Node.sMEM]

theorem win_iff (f : F) : (f.state = 19 ∨ f.state = 21) ↔ (f.isVh = true ∨ f.isCh = true) := by
  cases f <;> simp [NodeGen.F.isVh, NodeGen.F.isCh, F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY,
    Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]

macro "bclose" : tactic => `(tactic| ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> first | omega | contradiction))

section
variable {vs : List NodeS3} (ok : NodeOk vs) {H : Nat} (hHR : R vs + 1 ≤ H)
include ok hHR

set_option maxHeartbeats 8000000 in
theorem cBytes_node {q : Nat} (hqn : q < R vs) : RowGoal vs H NodeV3.cBytes q := by
  intro C D P hC hD ex hex
  obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
  have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
    intro x hx; rw [hC x hx, X_node hqn, hr]
  have hmod : (off vs n + p + 1) % H = off vs n + p + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hD
  have hw := rwf ok hn
  have hbf := byte_facts ok hn hp
  simp only at hbf
  have hfm := (fmem ok hn hp).1
  have hidx := (fmem ok hn hp).2
  have hodd : oddOf (rec vs n).v = 0 ∨ oddOf (rec vs n).v = 1 := by unfold oddOf; split <;> omega
  have hLf := len_facts ((layN vs n).getD p default).1 (hplenOf (rec vs n).v)
  have hnib := nib_iff ((layN vs n).getD p default).1
  have hvl := isVlen_iff ((layN vs n).getD p default).1
  have hwin := win_iff ((layN vs n).getD p default).1
  have hlb : ((layN vs n).getD p default).1.state = 18 → (lenBOf (rec vs n).v).length = 4 ∧
      (tvOf (rec vs n).v = true → le256 (lenBOf (rec vs n).v) = vlenOf (rec vs n).v ∧
        (lenBOf (rec vs n).v).getD 3 0 = 0) := by
    intro h
    apply lenB_facts ok hn
    have : ((layN vs n).getD p default).1 = F.vlen := by
      revert h hfm; generalize ((layN vs n).getD p default).1 = f
      cases f <;> simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
        Node.sCH, Node.sMEM]
    rw [← this]; exact hfm
  simp only [lenBOf] at hbf hlb
  simp only [mkR] at hC'
  simp only [NodeV3.cBytes, List.mem_cons, List.not_mem_nil, or_false] at hex
  -- the `VLEN` accumulator step needs the next row
  have hacc : ∀ (Dn : Nat → Int), (∀ x, x < 185 → Dn x = D x) →
      ((layN vs n).getD p default).1.state = 18 → ((layN vs n).getD p default).2 + 1 ≠ 4 →
      p + 1 < (layN vs n).length ∧ off vs n + p + 1 < R vs ∧
        (∀ x, x < 185 → D x = (rowCell vs (mkR vs n (p + 1)) x : Int)) ∧
        ((layN vs n).getD (p + 1) default).1 = ((layN vs n).getD p default).1 ∧
        ((layN vs n).getD (p + 1) default).2 = ((layN vs n).getD p default).2 + 1 := by
    intro _ _ h18 hne
    have h4 := hLf.2.2.2.2.1 h18
    have h1 : p + 1 < (layN vs n).length := by
      apply Classical.byContradiction; intro hh
      have := (last_iff ok hn hp).1 (by omega); omega
    have h2 : off vs n + p + 1 < R vs := by
      rcases next_row hn hp with ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have h3 : (recsOf vs).getD (off vs n + p + 1) default = mkR vs n (p + 1) := by
      rcases next_row hn hp with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      all_goals omega
    have hadj := lay_adj hw h1
    simp only [show layout (fieldsOf (rec vs n).v) (hplenOf (rec vs n).v) = layN vs n from rfl] at hadj
    refine ⟨h1, h2, fun x hx => by rw [hD x hx, X_node h2, h3], ?_⟩
    rcases hadj with ⟨a1, a2, _⟩ | ⟨a1, _, _⟩
    · exact ⟨a1, a2⟩
    · omega
  generalize hA : (layN vs n).getD p default = A at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · node_ev3 [hC']; node_rc3 []; have h := hbf.1; bclose
  · node_ev3 [hC']; node_rc3 []; have h := hbf.2.1; bclose
  · node_ev3 [hC']; node_rc3 []; have h := hbf.2.2.1; bclose
  · node_ev3 [hC']; node_rc3 []
    have h1 := nib4 (((rec vs n).v.ser false).getD p 0 / 16)
    have h2 := nib4 (((rec vs n).v.ser false).getD p 0 % 16)
    have h3 := hbf.2.2.2.2.2.1
    cases hnbv : A.1.nib <;> simp only [hnbv, Bool.false_eq_true, ite_false, ite_true, true_iff, false_iff] at hnib ⊢ <;>
      bclose
  · node_ev3 [hC']; node_rc3 []
    have h := hbf.2.2.2.1
    have h1 := nib4 (((rec vs n).v.ser false).getD p 0 / 16)
    cases hnbv : A.1.nib <;> simp only [hnbv, Bool.false_eq_true, ite_false, ite_true, true_iff, false_iff] at hnib ⊢ <;>
      bclose
  · node_ev3 [hC']; node_rc3 []
    have h := hbf.2.2.2.2.1
    have h2 := nib4 (((rec vs n).v.ser false).getD p 0 % 16)
    rcases hodd with ho | ho <;> simp only [ho] <;>
      cases hnbv : A.1.nib <;> simp only [hnbv, Bool.false_eq_true, ite_false, ite_true, true_iff, false_iff] at hnib ⊢ <;>
      bclose
  · -- `VLEN` start: `vacc = b`
    node_ev3 [hC']; node_rc3 []
    have h := hbf.2.2.2.2.2.2.1
    by_cases h18 : A.1.state = 18
    · have hv : A.1.isVlen = true := hvl.2 h18
      have hl := (hlb h18).1
      simp only [hv, ite_true]
      by_cases h0 : A.2 = 0
      · simp only [h0, Nat.zero_add, b2n, decide_true, ite_true]
        rw [le256_take_one _ (by intro h'; rw [h'] at hl; simp at hl)]
        have := h h18; rw [h0] at this; rw [this]; bclose
      · bclose
    · have hv : A.1.isVlen = false := by cases h' : A.1.isVlen <;> simp_all
      simp only [hv, Bool.false_eq_true, ite_false]; bclose
  · node_ev3 [hC']; node_rc3 []
    by_cases h18 : A.1.state = 18
    · have hv : A.1.isVlen = true := hvl.2 h18
      simp only [hv, ite_true]
      by_cases h0 : A.2 = 0
      · simp only [h0, Nat.pow_zero]; bclose
      · bclose
    · have hv : A.1.isVlen = false := by cases h' : A.1.isVlen <;> simp_all
      simp only [hv, Bool.false_eq_true, ite_false]; bclose
  · -- accumulator step
    by_cases hcase : A.1.state = 18 ∧ A.2 + 1 ≠ 4
    · obtain ⟨h1, h2, hD', ha1, ha2⟩ := hacc D (fun _ _ => rfl) hcase.1 hcase.2
      simp only [mkR, ha1, ha2] at hD'
      node_ev3 [hC', hD']; node_rc3 []
      have hv : A.1.isVlen = true := hvl.2 hcase.1
      have hl := (hlb hcase.1).1
      have hstep := le256_take_succ ((Option.map NSlot3.lenB (slotOf (rec vs n).v)).getD []) A.2 (by have := hidx; rw [hLf.2.2.2.2.1 hcase.1] at this; omega)
      have hbn := hbf.2.2.2.2.2.2.1
      have hbn' := byte_facts ok hn h1
      simp only at hbn'
      rw [ha1, ha2] at hbn'
      have hb1 := hbn'.2.2.2.2.2.2.1 hcase.1
      simp only [lenBOf] at hb1
      simp only [hv, ite_true] at hstep hb1 ⊢
      rw [show A.2 + 1 + 1 = A.2 + 2 by omega, hstep, ← hb1]
      simp only [b2n, decide_eq_true_eq]
      generalize 256 ^ (A.2 + 1) = P at *
      split
      · omega
      · simp only [Int.natCast_add, Int.natCast_mul]; omega
    · node_ev3 [hC']; node_rc3 []
      have hl := hLf.2.2.2.2.1
      have hvl' := hvl
      cases hvb : A.1.isVlen <;> simp only [hvb, Bool.false_eq_true, ite_true, ite_false, true_iff, false_iff] at hvl' ⊢ <;>
        bclose
  · -- `vsc` step
    by_cases hcase : A.1.state = 18 ∧ A.2 + 1 ≠ 4
    · obtain ⟨h1, h2, hD', ha1, ha2⟩ := hacc D (fun _ _ => rfl) hcase.1 hcase.2
      simp only [mkR, ha1, ha2] at hD'
      node_ev3 [hC', hD']; node_rc3 []
      have hv : A.1.isVlen = true := hvl.2 hcase.1
      simp only [hv, ite_true, Nat.pow_succ]
      generalize 256 ^ A.2 = Q at *
      simp only [Int.natCast_mul]; bclose
    · node_ev3 [hC']; node_rc3 []
      have hl := hLf.2.2.2.2.1
      have hvl' := hvl
      cases hvb : A.1.isVlen <;> simp only [hvb, Bool.false_eq_true, ite_true, ite_false, true_iff, false_iff] at hvl' ⊢ <;>
        bclose
  · -- `vacc = vlen` at the field end of a revealed value
    node_ev3 [hC']; node_rc3 []
    by_cases h18 : A.1.state = 18
    · have hv : A.1.isVlen = true := hvl.2 h18
      have hl := hLf.2.2.2.2.1 h18
      simp only [hv, ite_true]
      cases ht : tvOf (rec vs n).v
      · simp [b2n]
      · have hlen4 := (hlb h18).1
        have hv4 := ((hlb h18).2 ht).1
        by_cases h3 : A.2 + 1 = F.len (hplenOf (rec vs n).v) A.1
        · rw [show A.2 + 1 = 4 by omega, List.take_of_length_le (by omega), hv4]; bclose
        · bclose
    · simp [b2n, h18]
  · node_ev3 [hC']; node_rc3 []
    by_cases h18 : A.1.state = 18
    · have hl := hLf.2.2.2.2.1 h18
      cases ht : tvOf (rec vs n).v
      · simp [b2n]
      · have h30 := ((hlb h18).2 ht).2
        have hbb := hbf.2.2.2.2.2.2.1 h18
        by_cases h3 : A.2 + 1 = F.len (hplenOf (rec vs n).v) A.1
        · rw [hbb, show A.2 = 3 by omega, h30]; simp
        · simp [b2n, h3]
    · simp [b2n, h18]
  · node_ev3 [hC']; node_rc3 []
    have h := hbf.2.2.2.2.2.2.2.1
    have h1 := lo8 (bmvOf (rec vs n).v)
    have hbm := isBm_iff A.1
    cases hbv : A.1.isBm <;> simp only [hbv, Bool.false_eq_true, false_and, true_and, false_iff, true_iff] at hbm ⊢ <;>
      bclose
  · node_ev3 [hC']; node_rc3 []
    have h := hbf.2.2.2.2.2.2.2.2.1
    have h1 := hi8 (bmvOf (rec vs n).v)
    have h2 := (flag_facts _ hw).2.2.2.2.2.1
    have hbm := isBm_iff A.1
    cases hbv : A.1.isBm <;> simp only [hbv, Bool.false_eq_true, false_and, true_and, false_iff, true_iff] at hbm ⊢ <;>
      bclose
  · node_ev3 [hC']; node_rc3 []
    have h := hbf.2.2.2.2.2.2.2.2.2
    bclose

set_option maxHeartbeats 4000000 in
theorem cBytes_other {q : Nat} (hq : R vs ≤ q) (hqH : q < H) : RowGoal vs H NodeV3.cBytes q := by
  intro C D P hC hD ex hex
  have hC' : ∀ x, x < 185 → C x = (if q = R vs then (sumCell (total vs) x : Int)
      else (padCell (total vs) x : Int)) := by
    intro x hx; rw [hC x hx]
    split
    · subst q; rw [X_sum]
    · rw [X_pad (by omega)]
  simp only [NodeV3.cBytes, List.mem_cons, List.not_mem_nil, or_false] at hex
  generalize total vs = T at *
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals node_ev3 [hC']
  all_goals split <;> simp [sumCell, padCell]

theorem cBytes_ok : GroupOk vs H NodeV3.cBytes :=
  groupOk_of vs H (fun _ h => cBytes_node ok hHR h) (cBytes_other ok hHR (Nat.le_refl _) (by omega))
    (fun _ h1 h2 => cBytes_other ok hHR (by omega) h2)

end

end NodeGen3

end ZkFormal.NearV3.Render
