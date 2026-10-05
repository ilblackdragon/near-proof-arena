import ZkFormal.Near.Link.WalkChain

/-!
# ZkFormal.Near.Link.WalkKey — each receipt has a walk along its key symbols

`KEYNIB` matches the walk's symbols with the receipt's key symbols
(`keySyms`), `FINAL` its last target with the receipt's slot.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem walkSends_final (ws : List WalkV) : walkSends ws B_FINAL =
    ws.map fun w => [w.r, (w.edge (w.steps.length - 1)).getD 3 0] := by
  simp [walkSends, B_FINAL, B_EDGE]

theorem rcptRecvs_final (pub : List Fp) (rs : RcptVs) : rcptRecvs pub rs B_FINAL =
    (rs.zip (List.range rs.length)).map fun p => [p.2, p.1.kslot] := by
  simp [rcptRecvs, B_FINAL, B_DIGEST]

theorem keySyms_lt (x : RcptV) (hv : ∀ y ∈ x.v, y < P) : ∀ y ∈ x.keySyms, y < P := by
  intro y hy
  simp only [RcptV.keySyms, List.mem_append, List.mem_flatMap] at hy
  rcases hy with (hy | ⟨ch, hch, hy⟩) | hy
  · simp at hy; unfold P; omega
  · have := hv ch hch
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> omega
  · simp at hy; subst hy; unfold SYM_END P; omega

theorem getD_canon {l : List Nat} (h : ∀ x ∈ l, x < P) (i : Nat) : l.getD i 0 < P := getD_lt h i

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem edge_canon {w : WalkV} (hw : w ∈ ws) (i : Nat) : ∀ x ∈ w.edge i, x < P := by
  intro x hx
  unfold WalkV.edge at hx
  rw [List.getD_eq_getElem?_getD] at hx
  cases hi : w.steps[i]? with
  | none => rw [hi] at hx; simp at hx
  | some st => rw [hi] at hx; exact h.walk.canon w hw st (List.mem_of_getElem? hi) x hx

theorem keynib_perm : (rcptSends (publicOf c) rs B_KEYNIB).Perm (walkRecvs ws B_KEYNIB) := by
  have hrl := rs_length_le h
  have hT := walk_steps_lt h
  have hp := perm h (b := B_KEYNIB) (by decide) (by decide)
  rw [nearSends_keynib, nearRecvs_keynib] at hp
  apply perm_nat _ _ hp
  · intro m hm
    rw [rcptSends_keynib] at hm
    obtain ⟨⟨x, r⟩, hpr, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hr, rfl⟩ := mem_zip_range.mp hpr
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
    have hv := (idLens w).2.1
    have hks := keySyms_length rs[r]
    have hvc : ∀ y ∈ rs[r].v, y < P := fun y hy => h.rcpt.canon _ (List.getElem_mem hr) y (by simp [RcptV.raw, hy])
    simp only [List.mem_range] at ht
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · unfold P; omega
    · unfold P; omega
    · exact getD_canon (keySyms_lt _ hvc) t
    · split <;> (unfold P; omega)
  · intro m hm
    rw [walkRecvs_keynib] at hm
    obtain ⟨w, hw, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    simp only [List.mem_range] at ht
    have hwl : w.steps.length ≤ (ws.flatMap (·.steps)).length := by
      rw [List.length_flatMap]; exact le_sum_of_mem (fun w : WalkV => w.steps.length) hw
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (h.walk.steps w hw).2.2
    · omega
    · exact getD_canon (edge_canon h hw _) 2
    · split <;> (unfold P; omega)

/-- **The walk of receipt `r`.** -/
theorem walk_of {r : Nat} (hr : r < rs.length) :
    ∃ w ∈ ws, w.r = r ∧ w.steps.length = rs[r].keySyms.length + 1 ∧
      (∀ t, t < rs[r].keySyms.length → (w.edge (t + 1)).getD 2 0 = rs[r].keySyms.getD t 0) ∧
      (w.edge rs[r].keySyms.length).getD 3 0 = rs[r].kslot := by
  have hp := keynib_perm h
  have hS : ∀ t, t < rs[r].keySyms.length →
      [r, t, rs[r].keySyms.getD t 0, if t + 1 = rs[r].keySyms.length then 1 else 0] ∈
        rcptSends (publicOf c) rs B_KEYNIB := by
    intro t ht
    rw [rcptSends_keynib]
    exact List.mem_flatMap.mpr ⟨(rs[r], r), mem_zip_range.mpr ⟨hr, rfl⟩,
      List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩⟩
  have hks := keySyms_length rs[r]
  obtain ⟨w, hw, hm⟩ := List.mem_flatMap.mp (by rw [← walkRecvs_keynib]; exact hp.mem_iff.mp (hS 0 (by omega)))
  obtain ⟨t0, ht0, he0⟩ := List.mem_map.mp hm
  simp only [List.cons.injEq] at he0
  have hwr : w.r = r := he0.1
  -- every walk message matches the receipt's
  have hmatch : ∀ t, t + 1 < w.steps.length → t < rs[r].keySyms.length ∧
      (w.edge (t + 1)).getD 2 0 = rs[r].keySyms.getD t 0 ∧
      ((t + 2 = w.steps.length) ↔ (t + 1 = rs[r].keySyms.length)) := by
    intro t ht
    have hR : [w.r, t, (w.edge (t + 1)).getD 2 0, if t + 2 = w.steps.length then 1 else 0] ∈
        walkRecvs ws B_KEYNIB := by
      rw [walkRecvs_keynib]
      exact List.mem_flatMap.mpr ⟨w, hw, List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩⟩
    have hS' := hp.mem_iff.mpr hR
    rw [rcptSends_keynib] at hS'
    obtain ⟨⟨x, r'⟩, hpr, hm'⟩ := List.mem_flatMap.mp hS'
    obtain ⟨hr', rfl⟩ := mem_zip_range.mp hpr
    obtain ⟨t', ht', he'⟩ := List.mem_map.mp hm'
    simp only [List.cons.injEq, and_true] at he'
    obtain ⟨e1, rfl, e3, e4⟩ := he'
    rw [hwr] at e1; subst e1
    simp only [List.mem_range] at ht'
    refine ⟨ht', e3.symm, ?_⟩
    constructor
    · intro h1; rw [if_pos h1] at e4; split at e4 <;> simp_all
    · intro h1; rw [if_pos h1] at e4; split at e4 <;> simp_all
  have h2 := (h.walk.steps w hw).1
  have hlast := hmatch (w.steps.length - 2) (by omega)
  have hlen : w.steps.length = rs[r].keySyms.length + 1 := by
    have := hlast.2.2.mp (by omega); omega
  refine ⟨w, hw, hwr, hlen, fun t ht => (hmatch t (by omega)).2.1, ?_⟩
  -- FINAL
  have hpf := perm h (b := B_FINAL) (by decide) (by decide)
  rw [nearSends_final, nearRecvs_final] at hpf
  have hFs : [w.r, (w.edge (w.steps.length - 1)).getD 3 0] ∈ walkSends ws B_FINAL := by
    rw [walkSends_final]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨y, hy, he⟩ := List.mem_map.mp ((hpf.mem_iff).mp (List.mem_map.mpr ⟨_, hFs, rfl⟩))
  rw [rcptRecvs_final] at hy
  obtain ⟨⟨x, r'⟩, hpr, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hr', rfl⟩ := mem_zip_range.mp hpr
  obtain ⟨_, _, _, w'⟩ := rcpt_wf_at h hr'
  have hrl := rs_length_le h
  have := toFp_inj (a := [r', rs[r'].kslot]) (b := [w.r, (w.edge (w.steps.length - 1)).getD 3 0])
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · unfold P; omega
      · exact w'.small.1)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (h.walk.steps w hw).2.2
      · exact getD_canon (edge_canon h hw _) 3) he
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨e1, e2⟩ := this
  rw [hwr] at e1; subst e1
  rw [hlen, Nat.add_sub_cancel] at e2
  exact e2.symm

end Hyp

end Link

end ZkFormal.Near
