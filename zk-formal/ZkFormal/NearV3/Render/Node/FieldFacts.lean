import ZkFormal.NearV3.Render.Node.Trans
import ZkFormal.NearV3.Render.Node.Bool

/-!
# ZkFormal.NearV3.Render.Node.FieldFacts — field successions and record flags as linear facts
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (wOf lwOf len_facts bits_zero)

namespace NodeGen3

theorem rc70 (vs : List NodeS3) (r : NRec) : rowCell vs r 70 = wOf r.f := rfl
theorem rc71 (vs : List NodeS3) (r : NRec) : rowCell vs r 71 = lwOf r.f := rfl

theorem isLeaf_iff (v : NodeV3) : (typeOf v).1 = b2n (isLeaf v) := by
  cases v with
  | leaf => rfl
  | ext => rfl
  | branch sv => cases sv <;> rfl

/-- `SuccOk` as linear facts on the cells. -/
theorem succ_facts {v : NodeV3} {f g : F} (h : SuccOk v f g) :
    g.state ≠ 14 ∧ f.state ≠ 22 ∧
    (f.state = 14 → (typeOf v).1 + (typeOf v).2.1 = 1 → g.state = 15) ∧
    (f.state = 14 → (typeOf v).2.2.1 = 1 → g.state = 20) ∧
    (f.state = 14 → (typeOf v).2.2.2 = 1 → g.state = 18) ∧
    (f.state = 15 → g.state = 16) ∧
    (f.state = 16 → nokeyOf v = 0 → g.state = 17) ∧
    (f.state = 16 → nokeyOf v = 1 → (typeOf v).1 = 1 → g.state = 18) ∧
    (f.state = 16 → nokeyOf v = 1 → (typeOf v).1 = 0 → g.state = 21) ∧
    (f.state = 17 → (typeOf v).1 = 1 → g.state = 18) ∧
    (f.state = 17 → (typeOf v).1 = 0 → g.state = 21) ∧
    (f.state = 18 → g.state = 19) ∧
    (f.state = 19 → (typeOf v).1 = 1 → g.state = 22) ∧
    (f.state = 19 → (typeOf v).1 = 0 → g.state = 20) ∧
    (f.state = 20 → nochildOf v = 1 → g.state = 22) ∧
    (f.state = 20 → nochildOf v = 0 → g.state = 21) ∧
    (f.state = 21 → (g.state = 22 ∧ lwOf f = 1) ∨ (g.state = 21 ∧ lwOf f = 0 ∧ wOf g = wOf f + 1)) ∧
    (f.state ≠ 21 → g.state = 21 → wOf g = 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hw0 : f.state ≠ 21 → g.state = 21 → wOf g = 0 := by
    intro hf hg
    cases g <;> simp_all [F.state, Node.sCH, Node.sTAG, wOf, NodeGen.F.chw]
  have hl := isLeaf_iff v
  cases f
  case mem => exact absurd h3 id
  case ch w =>
    simp only [nxt] at h3
    have hs : (F.ch w).state = 21 := rfl
    rw [hs]
    refine ⟨h1, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_, fun h => absurd rfl h⟩
    rcases h3 with ⟨h4, h5⟩ | ⟨h4, h5, h6⟩
    · left; exact ⟨h4, by simp [lwOf, NodeGen.F.chw, h5, b2n]⟩
    · right
      refine ⟨h4, by simp [lwOf, NodeGen.F.chw, h5, b2n], ?_⟩
      cases g <;> simp_all [F.state, Node.sCH, wOf, NodeGen.F.chw, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY,
        Node.sVLEN, Node.sVH, Node.sBM, Node.sMEM]
  all_goals
    have hw := hw0 (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
      Node.sCH])
    simp only [nxt] at h3
    generalize g.state = s at h1 h3 hw ⊢
    simp only [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH,
      Node.sMEM] at h1 h3 ⊢
    have hk : nokeyOf v = 0 ∨ nokeyOf v = 1 := by unfold nokeyOf b2n; split <;> simp
    have hc : nochildOf v = 0 ∨ nochildOf v = 1 := by unfold nochildOf b2n; split <;> simp
    generalize nokeyOf v = nk at *
    generalize nochildOf v = nc at *
    cases v with
    | leaf => rcases hk with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [typeOf, isLeaf] at h3 ⊢ <;> omega
    | ext => rcases hk with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [typeOf, isLeaf] at h3 ⊢ <;> omega
    | branch sv => cases sv <;> rcases hk with rfl | rfl <;> rcases hc with rfl | rfl <;>
        simp [typeOf, isLeaf] at h3 ⊢ <;> omega

theorem kind_facts {v : NodeV3} {f : F} (hf : f ∈ fieldsOf v) :
    (f.state = 15 ∨ f.state = 16 ∨ f.state = 17 → (typeOf v).1 + (typeOf v).2.1 = 1) ∧
    (f.state = 18 ∨ f.state = 19 → (typeOf v).1 + (typeOf v).2.2.2 = 1) ∧
    (f.state = 20 → (typeOf v).2.2.1 + (typeOf v).2.2.2 = 1) ∧
    (f.state = 21 → (typeOf v).1 = 0) := by
  have hb : ∀ f ∈ branchWins (kidsOf v), f.state = 21 := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; rfl
  cases v with
  | leaf k sv m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F.state, typeOf, Node.sTAG, Node.sHPL, Node.sHPF,
      Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]
  | ext k kid m =>
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F.state, typeOf, Node.sTAG, Node.sHPL, Node.sHPF,
      Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]
  | branch sv kids m =>
    cases sv with
    | none =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | hf | rfl
      · simp [F.state, typeOf, Node.sTAG]
      · simp [F.state, typeOf, Node.sBM]
      · have := hb _ (by simpa [kidsOf] using hf); simp [this, typeOf]
      · simp [F.state, typeOf, Node.sMEM]
    | some s =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | hf | rfl
      · simp [F.state, typeOf, Node.sTAG]
      · simp [F.state, typeOf, Node.sVLEN]
      · simp [F.state, typeOf, Node.sVH]
      · simp [F.state, typeOf, Node.sBM]
      · have := hb _ (by simpa [kidsOf] using hf); simp [this, typeOf]
      · simp [F.state, typeOf, Node.sMEM]

theorem bmv_lt (v : NodeV3) (hw : v.wf) : bmvOf v < 2 ^ 16 := by
  unfold bmvOf
  split
  · decide
  · cases v with
    | leaf => simp [isLE] at *
    | ext => simp [isLE] at *
    | branch sv kids m =>
      have := Link.kidBitmap_lt (show kids.length = 16 from hw.1)
      simp only [kidsOf]; omega

theorem flag_facts (v : NodeV3) (hw : v.wf) :
    (nokeyOf v = 0 ∨ hplenOf v = 1) ∧ nokeyOf v ≤ 1 ∧ (nochildOf v = 0 ∨ bmvOf v = 0) ∧
    (((typeOf v).1 = 0 ∧ (typeOf v).2.1 = 0) ∨ bmvOf v = 0) ∧
    (b2n (tvOf v) = 0 ∨ ((typeOf v).2.2.1 = 0 ∧ (typeOf v).2.1 = 0)) ∧ bmvOf v < 2 ^ 16 ∧
    b2n (twOf v) ≤ b2n (tvOf v) := by
  have hlt := bmv_lt v hw
  refine ⟨?_, ?_, ?_, ?_, ?_, hlt, ?_⟩
  · by_cases h : (isLE v && hplenOf v == 1) = true
    · right
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.2
    · left
      simp only [nokeyOf, b2n, h, Bool.false_eq_true, ite_false]
  · simp only [nokeyOf, b2n]; split <;> omega
  · by_cases h : (!isLE v && popOf v == 0) = true
    · right
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have h2 := h.2
      unfold popOf at h2
      rw [NodeSeq.foldl_sum, Nat.zero_add] at h2
      exact bits_zero 16 _ hlt h2
    · left
      simp only [nochildOf, b2n, h, Bool.false_eq_true, ite_false]
  · cases v with
    | leaf => right; rfl
    | ext => right; rfl
    | branch sv => cases sv <;> left <;> exact ⟨rfl, rfl⟩
  · cases v with
    | leaf k sv => right; exact ⟨rfl, rfl⟩
    | ext => left; rfl
    | branch sv => cases sv with
      | none => left; rfl
      | some s => right; exact ⟨rfl, rfl⟩
  · cases v with
    | leaf k sv => cases sv <;> simp [twOf, tvOf, NodeV3.value, b2n] <;> exact b2n_le' _
    | ext => simp [twOf, tvOf, NodeV3.value, b2n]
    | branch sv => cases sv with
      | none => simp [twOf, tvOf, NodeV3.value, b2n]
      | some s => cases s <;> simp [twOf, tvOf, NodeV3.value, b2n] <;> exact b2n_le' _

end NodeGen3

end ZkFormal.NearV3.Render
