import ZkFormal.Udr.Np.SchedFri

/-!
# ZkFormal.Udr.Np.Avail — committed FRI oracles are present once their fold is drawn

If the FRI challenge at index `q` of `friChals` has been drawn and the commit
`j` sits at a layer `c_j` with `2 c_j + 1 ≤ key(kind q)` (so its fold `β_{c_j}`
comes no later), then the commit's oracle (number `3 + j`) is in the
transcript.  Proof: count oracle parts and challenges of the schedule prefix
`preSlots ++ layers 0 … c_j`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable (A : Air) (prm : Params) (hdr : List Nat)

/-- The kinds of layer `i`. -/
def gK (i : Nat) : List (Bool × Nat) := (if rollInAt A prm hdr i then [(true, i)] else []) ++ [(false, i)]

/-- The slots of layer `i`. -/
def layerS (i : Nat) : List Slot :=
  (if rollInAt A prm hdr i then [.msg [], .chal false] else []) ++
    (match (friCommits A prm hdr).lookup i with
     | some a => [.msg [.oracle [(queryLog A prm hdr - i - a, 8 * 2 ^ a)]], .chal false]
     | none => [.msg [], .chal false])

theorem friSchedule_eq : friSchedule A prm hdr =
    (List.range (finalLayer A prm hdr)).flatMap (layerS A prm hdr) ++
    ((if rollInAt A prm hdr (finalLayer A prm hdr) then [.msg [], .chal false] else []) ++
      [.msg [.elems 2]]) := by
  simp only [friSchedule, List.append_assoc]; rfl

theorem friChalKinds_eq : friChalKinds A prm hdr =
    (List.range (finalLayer A prm hdr)).flatMap (gK A prm hdr) ++
    (if rollInAt A prm hdr (finalLayer A prm hdr) then [(true, finalLayer A prm hdr)] else []) := rfl

theorem layerS_length (i : Nat) : (layerS A prm hdr i).length = 2 * (gK A prm hdr i).length := by
  simp only [layerS, gK]
  by_cases hr : rollInAt A prm hdr i = true <;>
    cases (friCommits A prm hdr).lookup i <;> simp [hr]

theorem layerS_or (i : Nat) : ((layerS A prm hdr i).flatMap slotOr).length =
    if ((friCommits A prm hdr).lookup i).isSome then 1 else 0 := by
  simp only [layerS]
  by_cases hr : rollInAt A prm hdr i = true <;>
    cases (friCommits A prm hdr).lookup i <;> simp [hr, slotOr, partOr]

theorem flat_layer_length (N : Nat) : ((List.range N).flatMap (layerS A prm hdr)).length =
    2 * ((List.range N).flatMap (gK A prm hdr)).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.length_append,
      List.length_append, ih, List.flatMap_singleton, List.flatMap_singleton, layerS_length]
    omega

theorem flat_layer_or (N : Nat) : (((List.range N).flatMap (layerS A prm hdr)).flatMap slotOr).length =
    ((List.range N).filter fun i => ((friCommits A prm hdr).lookup i).isSome).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.length_append, ih,
      List.flatMap_singleton, layerS_or, List.filter_append, List.length_append]
    by_cases h : ((friCommits A prm hdr).lookup N).isSome = true <;> simp [h]

theorem flat_gK_last (c : Nat) : ∃ Y, (List.range (c + 1)).flatMap (gK A prm hdr) = Y ++ [(false, c)] := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  exact ⟨(List.range c).flatMap (gK A prm hdr) ++ (if rollInAt A prm hdr c then [(true, c)] else []),
    by simp [gK]⟩

theorem take_flatMap_slotOr_mono (l : List Slot) (a b : Nat) (h : a ≤ b) :
    ((l.take a).flatMap slotOr).length ≤ ((l.take b).flatMap slotOr).length := by
  obtain ⟨t, ht⟩ : ∃ t, l.take b = l.take a ++ t :=
    ⟨(l.take b).drop a, by
      conv => lhs; rw [← List.take_append_drop a (l.take b)]
      rw [List.take_take, Nat.min_eq_left h]⟩
  rw [ht, List.flatMap_append, List.length_append]; omega

end

section
variable (A : Air) (prm : Params)

theorem lookup_isSome_of_mem {β : Type} (l : List (Nat × β)) (x : Nat × β) (h : x ∈ l) :
    (l.lookup x.1).isSome := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases y with ⟨a, b⟩
    by_cases hx : x.1 = a
    · simp [List.lookup, hx]
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hx
      · simp only [List.lookup, show (x.1 == a) = false by simp [hx]]; exact ih h

/-- **Oracle availability.** -/
theorem oracle_avail (τ : PTn) (hs : Shaped (Vnp A prm) τ) (hE : 1 ≤ τ.entries.length)
    (q : Nat) (hq : q < (friChals A prm τ).length) (j : Nat) (hj : j < (commitsOf A prm τ).length)
    (hkey : 2 * ((commitsOf A prm τ)[j]).1 + 1 ≤ keyOf ((friChals A prm τ)[q]).1) :
    3 + j < τ.oracles.length := by
  obtain ⟨hdr, hh, hok, hsl⟩ := sh_header A prm τ hs hE
  have hhdr : hdrOf τ = hdr := by simp [hdrOf, hh]
  have hcm : commitsOf A prm τ = friCommits A prm hdr := by simp [commitsOf, hhdr]
  have hnb : nBatch A prm τ = batchRounds (layout A prm hdr) := by simp [nBatch, layOf, hhdr]
  generalize hcj : (commitsOf A prm τ)[j] = x at hkey
  have hxm : x ∈ friCommits A prm hdr := by rw [← hcm, ← hcj]; exact List.getElem_mem _
  obtain ⟨hxl, -, -⟩ := commits_mem A prm hdr x hxm
  -- the kinds up to layer `c = x.1`
  obtain ⟨Y, hY⟩ := flat_gK_last A prm hdr x.1
  have hkinds : friChalKinds A prm hdr = Y ++ (false, x.1) ::
      ((((List.range (finalLayer A prm hdr - (x.1 + 1))).map (x.1 + 1 + ·)).flatMap (gK A prm hdr)) ++
        (if rollInAt A prm hdr (finalLayer A prm hdr) then [(true, finalLayer A prm hdr)] else [])) := by
    rw [friChalKinds_eq, show finalLayer A prm hdr = (x.1 + 1) + (finalLayer A prm hdr - (x.1 + 1)) by omega,
      List.range_add, List.flatMap_append, hY]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [show x.1 + 1 + (finalLayer A prm hdr - (x.1 + 1)) = finalLayer A prm hdr by omega]
  have hfc : friChals A prm τ = (friChalKinds A prm hdr).zip (τ.chals.drop (4 + nBatch A prm τ)) := by
    simp [friChals, hhdr]
  -- the drawn kind `q` comes after `(false, c)`
  have hYq : Y.length ≤ q := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have hq' : q < (friChalKinds A prm hdr).length := by
      have := hq; rw [hfc, List.length_zip] at this; omega
    have hsort := List.pairwise_iff_getElem.mp (kinds_sorted A prm hdr) q Y.length hq'
      (by rw [hkinds]; simp) hlt
    have e1 : (friChalKinds A prm hdr)[Y.length]'(by rw [hkinds]; simp) = (false, x.1) := by
      simp only [hkinds, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    have e2 : ((friChals A prm τ)[q]).1 = (friChalKinds A prm hdr)[q] := by
      simp only [hfc, List.getElem_zip]
    rw [e1] at hsort
    rw [e2] at hkey
    simp only [keyOf_false] at hsort
    omega
  -- the transcript is long enough to contain layers `0 … c`
  have hchal : τ.chals.length = τ.entries.length / 2 := shaped_chals_length hs
  have hfl : (friChals A prm τ).length ≤ τ.chals.length - (4 + nBatch A prm τ) := by
    rw [hfc, List.length_zip, List.length_drop]; omega
  have hlen : (preSlots A prm hdr).length + ((List.range (x.1 + 1)).flatMap (layerS A prm hdr)).length ≤
      τ.entries.length := by
    rw [preSlots_length, flat_layer_length, hY, List.length_append, List.length_singleton, ← hnb]
    omega
  -- count oracle parts
  have hfit := (sh_fit A prm τ hs).1.length_eq
  rw [hsl, schedule_eq, friSchedule_eq,
    show finalLayer A prm hdr = (x.1 + 1) + (finalLayer A prm hdr - (x.1 + 1)) by omega,
    List.range_add, List.flatMap_append] at hfit
  rw [hfit]
  refine Nat.lt_of_lt_of_le ?_ (take_flatMap_slotOr_mono _ _ _ hlen)
  rw [← List.length_append, show ∀ (a b c d : List Slot), a ++ ((b ++ c) ++ d) = (a ++ b) ++ (c ++ d) by
    intros; simp, List.take_left, List.flatMap_append,
    List.length_append, preSlots_or, flat_layer_or]
  -- the commits `0 … j` are at distinct layers `≤ c`
  have hsub : ((friCommits A prm hdr).take (j + 1)).map Prod.fst ⊆
      (List.range (x.1 + 1)).filter fun i => ((friCommits A prm hdr).lookup i).isSome := by
    intro i hi
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hi
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hy
    rw [List.length_take] at hp
    have hp' : p < (friCommits A prm hdr).length := by omega
    rw [List.getElem_take]
    refine List.mem_filter.mpr ⟨List.mem_range.mpr ?_, lookup_isSome_of_mem _ _ (List.getElem_mem hp')⟩
    have hjl : j < (friCommits A prm hdr).length := by rw [← hcm]; exact hj
    have hxj : x = (friCommits A prm hdr)[j] := by rw [← hcj]; simp [hcm]
    by_cases hpj : p = j
    · subst hpj; rw [hxj]; omega
    · have := List.pairwise_iff_getElem.mp (commits_sorted A prm hdr) p j hp' hjl (by omega)
      rw [hxj]; omega
  have hnd : (((friCommits A prm hdr).take (j + 1)).map Prod.fst).Nodup := by
    have h1 := List.Pairwise.sublist (List.take_sublist (j + 1) (friCommits A prm hdr))
      (commits_sorted A prm hdr)
    have hs' : (((friCommits A prm hdr).take (j + 1)).map Prod.fst).Pairwise (· < ·) :=
      List.pairwise_map.mpr h1
    exact hs'.imp (fun h => Nat.ne_of_lt h)
  have := List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_map, List.length_take] at this
  have hjl : j < (friCommits A prm hdr).length := by rw [← hcm]; exact hj
  omega

end
end ZkFormal.Udr.Np
