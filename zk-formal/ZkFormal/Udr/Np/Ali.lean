import ZkFormal.Udr.Np.Early
import ZkFormal.Udr.GrandProduct

/-!
# ZkFormal.Udr.Np.Ali — the constraint-combination round `Chal5`

A nonzero constraint value `c_j(ω^r)` makes `α ↦ Σ_j α^j c_j(ω^r)` a nonzero
polynomial of length `|cs| ≤ 2^20` (`NpOk`), which has fewer than `|cs|` roots.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Generic challenge-round helpers -/

theorem count_doom_le {A : Air} {prm : Params} {τ : PTn} {S : PTn → Prop} (Bad : Fp8 → Prop)
    (h : ∀ c, ¬ Bad c → S (τ.pushChal c)) :
    count Fp8.all (fun c => Shaped (Vnp A prm) (τ.pushChal c) ∧ ¬ S (τ.pushChal c)) ≤
      count Fp8.all Bad :=
  count_mono _ fun c hc => Classical.byContradiction fun hb => hc.2 (h c hb)

theorem count_false_le (l : List Fp8) (n : Nat) : count l (fun _ => False) ≤ n := by
  rw [count_const]; simp

theorem combine_eq_ev (α : Fp8) (cs : List Fp8) :
    combine α cs = ev cs.length (fun k => cs.getD k 0) α := fp_eq_ev α cs

theorem count_combine_lt {cs : List Fp8} {v : Fp8} (hv : v ∈ cs) (hv0 : v ≠ 0) :
    count Fp8.all (fun α => combine α cs = 0) < cs.length := by
  have hc : ∃ k, k < cs.length ∧ cs.getD k 0 ≠ 0 := by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    exact ⟨k, hk, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact hv0⟩
  refine Nat.lt_of_le_of_lt (count_mono _ fun α h => ?_) (count_roots_lt hc Fp8.all Fp8.nodup_all)
  rw [← combine_eq_ev]; exact h

/-! ## Number of constraints -/

section
variable {K : Type} [Field K] [DecidableEq K]

theorem interactionAux_length (env : Env K) (α γ : K) (i : Interaction) (aux : List K) :
    (interactionAux env α γ i aux).1.length ≤ 2 * (i.mult.length - 1) := by
  unfold interactionAux
  generalize hb : i.mult.map (·.evalWith env) = bits
  have hl : bits.length = i.mult.length := by rw [← hb, List.length_map]
  match bits, hl with
  | [], _ => simp
  | [_], _ => simp
  | b0 :: b1 :: bs, hl =>
    simp only [List.length_append, List.length_map, List.length_zip, List.length_take,
      List.length_cons] at hl ⊢
    omega

theorem auxFold_length (env : Env K) (α γ : K) : ∀ (l : List Interaction)
    (acc : List K × List (Interaction × K) × List K),
    (l.foldl (fun (acc : List K × List (Interaction × K) × List K) (i : Interaction) =>
      let (cs, phi, rest) := interactionAux env α γ i acc.2.2
      (acc.1 ++ cs, acc.2.1 ++ [(i, phi)], rest)) acc).1.length ≤
      acc.1.length + (l.map fun i => 2 * (i.mult.length - 1)).sum
  | [], acc => by simp
  | i :: l, acc => by
    rw [List.foldl_cons]
    refine Nat.le_trans (auxFold_length env α γ l _) ?_
    have := interactionAux_length env α γ i acc.2.2
    simp only [List.length_append, List.map_cons, List.sum_cons]
    omega

theorem flatMap_length3 {β : Type} (l : List β) (f : β → List K) (hf : ∀ x, (f x).length = 3) :
    (l.flatMap f).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.length_append, ih, hf, List.length_cons]; omega

/-- The interaction-chain fold of `auxConstraints`. -/
def auxFold (env : Env K) (α γ : K) (l : List Interaction) (auxZ : List K) :
    List K × List (Interaction × K) × List K :=
  l.foldl (fun (acc : List K × List (Interaction × K) × List K) (i : Interaction) =>
      let (cs, phi, rest) := interactionAux env α γ i acc.2.2
      (acc.1 ++ cs, acc.2.1 ++ [(i, phi)], rest)) ([], [], auxZ)

theorem auxConstraints_length (T : Air.Table) (g : Nat) (env : Env K) (α γ : K)
    (auxZ auxG fins : List K) :
    (auxConstraints T g env α γ auxZ auxG fins).length ≤
      (T.interactions.map fun i => 2 * (i.mult.length - 1)).sum + 3 * fins.length := by
  unfold auxConstraints
  simp only [List.length_append]
  refine Nat.add_le_add ?_ ?_
  · have := auxFold_length env α γ T.interactions ([], [], auxZ)
    simpa using this
  · rw [flatMap_length3 _ _ (fun ⟨⟨_, _, _⟩, _⟩ => rfl), List.length_zip]
    have := Nat.min_le_right ((chunksOf (max g 1) ((auxFold env α γ T.interactions auxZ).2.1.filter (·.1.send)) ++
      chunksOf (max g 1) ((auxFold env α γ T.interactions auxZ).2.1.filter (! ·.1.send))).zip
      ((auxFold env α γ T.interactions auxZ).2.2.zip (auxG.drop (auxZ.length - (auxFold env α γ T.interactions auxZ).2.2.length)))).length fins.length
    omega

end

theorem length_filter_send (l : List Interaction) :
    (l.filter fun i => i.send == true).length + (l.filter fun i => i.send == false).length =
      l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    cases h : i.send
    · rw [List.filter_cons_of_neg (by simp [h]), List.filter_cons_of_pos (by simp [h])]
      simp only [List.length_cons]; omega
    · rw [List.filter_cons_of_pos (by simp [h]), List.filter_cons_of_neg (by simp [h])]
      simp only [List.length_cons]; omega

theorem numGroups_one (n : Nat) : numGroups n 1 = n := by simp [numGroups]

theorem csAt_length {A : Air} {prm : Params} (hok : NpOk A prm) (τ : PTn) (t : Nat)
    (ht : t < A.tables.length) (αfp γ x : Fp8) :
    (csAt A prm τ t αfp γ x).length ≤ 2 ^ 20 := by
  obtain ⟨hprm, hb⟩ := hok
  subst hprm
  have hT : tableOf A t = A.tables[t] := by
    unfold tableOf; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
  unfold csAt
  rw [List.length_append, List.length_map, hT]
  have h1 := auxConstraints_length A.tables[t] Params.default.auxGroup (polyEnv A Params.default τ t x)
    αfp γ ((List.range (tl A Params.default τ t).aux).map fun a =>
      colAt A Params.default τ ⟨t, 1, a⟩ x)
    ((List.range (tl A Params.default τ t).aux).map fun a =>
      colAt A Params.default τ ⟨t, 1, a⟩ (omg (tl A Params.default τ t).log * x))
    (finsOf A Params.default τ t)
  have h2 : (finsOf A Params.default τ t).length ≤ A.tables[t].interactions.length := by
    unfold finsOf
    rw [List.length_take]
    refine Nat.le_trans (Nat.min_le_left _ _) ?_
    unfold tl layOf
    by_cases hl : t < (layout A Params.default (hdrOf τ)).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
      simp only [Option.getD_some, layout, List.getElem_map, List.getElem_zip]
      show numGroups _ 1 + numGroups _ 1 ≤ _
      rw [numGroups_one, numGroups_one]
      unfold Air.Table.numSide
      rw [length_filter_send]
      exact Nat.le_refl _
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp only [Option.getD_none]
      exact Nat.zero_le _
  have h3 := hb _ (List.getElem_mem ht)
  have h4 : (A.tables[t].interactions.map fun i => 2 * (i.mult.length - 1)).sum ≤
      A.tables[t].auxCount Params.default.auxGroup := by
    unfold Air.Table.auxCount; omega
  omega

/-! ## `Chal5` -/

theorem chal5 : Chal5Stmt := by
  intro A prm hok τ hs _ hE hst
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hcl : τ.chals.length = 2 := by rw [shaped_chals_length hs, hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have h0 : ∀ c, (τ.pushChal c).chals.getD 0 0 = τ.chals.getD 0 0 := fun c =>
    chals_getD_pushChal τ c 0 (by omega)
  have h1 : ∀ c, (τ.pushChal c).chals.getD 1 0 = τ.chals.getD 1 0 := fun c =>
    chals_getD_pushChal τ c 1 (by omega)
  have hE' : ∀ c, (τ.pushChal c).entries.length = 6 := fun c => by rw [len_pushChal, hE]
  simp only [Stage, hE] at hst
  have hstage : ∀ c, Stage A prm (τ.pushChal c) ↔ (¬ AllClose A prm τ 2 ∨
      (∃ t, t < A.tables.length ∧ ∃ r, r < 2 ^ (tl A prm τ t).log ∧
        Ct A prm τ t (τ.chals.getD 0 0) (τ.chals.getD 1 0) c (omg (tl A prm τ t).log ^ r) ≠ 0) ∨
      BusFinalsFail A prm τ) := fun c => by
    have hO := oAgree_pushChal τ c hne 2
    simp only [Stage, hE' c, h0, h1, hlast]
    rw [allClose_congr hO (by omega), busFinalsFail_congr (header?_pushChal τ c hne) (finalsOf_pushChal τ c)]
    simp only [tl_congr A prm (header?_pushChal τ c hne), Ct_congr hO (Nat.le_refl 2) (finalsOf_pushChal τ c)]
  rcases hst with h | ⟨t, ht, r, hr, v, hv, hv0⟩ | h
  · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inl h)) (count_false_le _ _)
  · refine Nat.le_trans (count_doom_le (A := A) (prm := prm)
      (fun c => combine c (csAt A prm τ t (τ.chals.getD 0 0) (τ.chals.getD 1 0)
        (omg (tl A prm τ t).log ^ r)) = 0)
      fun c hc => (hstage c).mpr (Or.inr (Or.inl ⟨t, ht, r, hr, hc⟩))) ?_
    have := count_combine_lt hv hv0
    have := csAt_length hok τ t ht (τ.chals.getD 0 0) (τ.chals.getD 1 0) (omg (tl A prm τ t).log ^ r)
    unfold badBudget; omega
  · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inr (Or.inr h))) (count_false_le _ _)

end ZkFormal.Udr.Np
