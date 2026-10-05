import ZkFormal.Near.Extract.NodeMain

/-!
# ZkFormal.Near.Extract.NodeWfProof — local well-formedness of the node view
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

theorem win_lt (tr : Trace Fp) (col : Nat → Nat) (r : Nat) : ∀ x ∈ win tr col r, x < P := by
  intro x hx; unfold win at hx; rw [List.mem_map] at hx; obtain ⟨i, -, rfl⟩ := hx; exact cv_lt _ _ _ _

theorem rowsB_lt (tr : Trace Fp) (c r n : Nat) : ∀ x ∈ rowsB tr c r n, x < P := by
  intro x hx; unfold rowsB at hx; rw [List.mem_map] at hx; obtain ⟨i, -, rfl⟩ := hx; exact cv_lt _ _ _ _

theorem slotOf_wf (tr : Trace Fp) (s rV rH : Nat) : (slotOf tr s rV rH).wf ∧ ∀ x ∈ (slotOf tr s rV rH).raw, x < P := by
  unfold slotOf; split
  · refine ⟨⟨win_length _ _ _, win_length _ _ _⟩, ?_⟩
    intro x hx; simp only [NSlot.raw, List.mem_append] at hx
    rcases hx with h | h <;> exact win_lt _ _ _ x h
  · refine ⟨⟨rowsB_length _ _ _ _, win_length _ _ _⟩, ?_⟩
    intro x hx; simp only [NSlot.raw, List.mem_append] at hx
    rcases hx with h | h
    · exact rowsB_lt _ _ _ _ x h
    · exact win_lt _ _ _ x h

theorem kidOf_wf (tr : Trace Fp) (r : Nat) :
    kidOf tr r ≠ .none ∧ (kidOf tr r).wf ∧ ∀ x ∈ (kidOf tr r).raw, x < P := by
  unfold kidOf; split
  · refine ⟨by simp, ⟨win_length _ _ _, win_length _ _ _⟩, ?_⟩
    intro x hx; simp only [NKid.raw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((h | h | h) | h) | h
    · subst h; exact cv_lt _ _ _ _
    · subst h; exact cv_lt _ _ _ _
    · subst h; exact cv_lt _ _ _ _
    · exact win_lt _ _ _ x h
    · exact win_lt _ _ _ x h
  · exact ⟨by simp, win_length _ _ _, fun x hx => win_lt _ _ _ x hx⟩

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem keyNibs_lt (hC : NodeCtx tr s ℓ fl) (hlt : tr.cell T_NODE s tl + tr.cell T_NODE s te = 1) :
    ∀ x ∈ keyNibs tr s, x < 16 := by
  have hkp := keyPart hL hC hlt
  obtain ⟨hh1, -, -⟩ := hkp
  have hℓ : 6 + cv tr T_NODE s hplen ≤ ℓ := by
    rcases (show tr.cell T_NODE s tl = 1 ∨ tr.cell T_NODE s te = 1 by
      obtain ⟨hr0, ha0⟩ := nodeStart hL hC
      rcases isBool hL hr0 (x := tl) (by simp [boolCols]) with h | h
      · rw [h] at hlt; right; grind
      · left; exact h) with h | h
    · have := (leafFields hL hC h).2.2.2.1; omega
    · have := (extFields hL hC h).2.2.2.1; omega
  have nb : ∀ r, s ≤ r → r < s + ℓ → hiN tr r < 16 ∧ loN tr r < 16 := fun r h1 h2 => by
    obtain ⟨a, b', -, -⟩ := nibs hL (r := r) (pub := pub) (by have := hC.bound; omega); exact ⟨a, b'⟩
  intro x hx
  unfold keyNibs at hx; rw [List.mem_append] at hx
  rcases hx with hx | hx
  · split at hx
    · simp at hx; subst hx; exact (nb (s + 5) (by omega) (by omega)).2
    · simp at hx
  · rw [List.mem_flatMap] at hx; obtain ⟨p, hp, hx⟩ := hx
    unfold keyPairs at hp; rw [List.mem_map] at hp; obtain ⟨m, hm, rfl⟩ := hp
    rw [List.mem_range'] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact (nb (s + 6 + m) (by omega) (by omega)).1
    · exact (nb (s + 6 + m) (by omega) (by omega)).2

theorem nodeV_wf (hC : NodeCtx tr s ℓ fl) : (nodeVOf tr s).wf ∧ ∀ x ∈ (nodeVOf tr s).raw, x < P := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  unfold nodeVOf
  by_cases h1 : cv tr T_NODE s tl = 1
  · rw [if_pos h1]
    have hte := typeZeros hL hC (x := tl) (y := te) (by simp) (of_cv_one h1) (by simp) (by decide)
    have K := keyNibs_lt hL hC (by rw [of_cv_one h1, hte]; exact fp_add_zero' rfl)
    obtain ⟨sw, sr⟩ := slotOf_wf tr s (s + (5 + cv tr T_NODE s hplen)) (s + (9 + cv tr T_NODE s hplen))
    refine ⟨⟨K, sw, rowsB_length _ _ _ _⟩, ?_⟩
    intro x hx; simp only [NodeV.raw, List.mem_append] at hx
    rcases hx with (h | h) | h
    · have := K x h; unfold P; omega
    · exact sr x h
    · exact rowsB_lt _ _ _ _ x h
  rw [if_neg h1]
  by_cases h2 : cv tr T_NODE s te = 1
  · rw [if_pos h2]
    have htl0 : tr.cell T_NODE s tl = 0 := of_cv_zero (show cv tr T_NODE s tl = 0 by omega)
    have K := keyNibs_lt hL hC (by rw [of_cv_one h2, htl0]; exact fp_zero_add' rfl)
    obtain ⟨kn, kw, kr⟩ := kidOf_wf tr (s + (5 + cv tr T_NODE s hplen))
    refine ⟨⟨K, kn, kw, rowsB_length _ _ _ _⟩, ?_⟩
    intro x hx; simp only [NodeV.raw, List.mem_append] at hx
    rcases hx with (h | h) | h
    · have := K x h; unfold P; omega
    · exact kr x h
    · exact rowsB_lt _ _ _ _ x h
  rw [if_neg h2]
  have kidsW : ∀ kd ∈ kidsOf tr s (brOff tr s), kd.wf ∧ ∀ x ∈ kd.raw, x < P := by
    intro kd hkd; unfold kidsOf at hkd; rw [List.mem_map] at hkd; obtain ⟨j, -, rfl⟩ := hkd
    split
    · exact ⟨(kidOf_wf tr _).2.1, (kidOf_wf tr _).2.2⟩
    · exact ⟨trivial, by simp [NKid.raw]⟩
  refine ⟨⟨by simp [kidsOf], fun sl hsl => ?_, fun kd hkd => (kidsW kd hkd).1, rowsB_length _ _ _ _⟩, ?_⟩
  · split at hsl
    · simp at hsl; subst hsl; exact (slotOf_wf tr _ _ _).1
    · simp at hsl
  · intro x hx; simp only [NodeV.raw, List.mem_append] at hx
    rcases hx with (h | h) | h
    · split at h
      · simp at h; exact (slotOf_wf tr _ _ _).2 x h
      · simp at h
    · rw [List.mem_flatMap] at h; obtain ⟨kd, hkd, h⟩ := h; exact (kidsW kd hkd).2 x h
    · exact rowsB_lt _ _ _ _ x h

end ZkFormal.Near.NodeProof
