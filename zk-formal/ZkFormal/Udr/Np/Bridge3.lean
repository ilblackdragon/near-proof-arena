import ZkFormal.Udr.Np.Bridge2

/-!
# ZkFormal.Udr.Np.Bridge3 — the verifier context and the oracles at the query phase

Under `global (prep τ.erase) = true`:
* the fields of `prep τ.erase` in terms of `τ` (`prepF_*`);
* `rollIn` of `checkAt` is the roll-in `+ γ_i · G` of the FRI run;
* the oracles are `main :: aux :: quot :: fri` with the scheduled shapes
  (`query_oracles`).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable (A : Air) (prm : Params)

/-- The data `prep_inv` exposes, bundled. -/
structure QData (τ : PTn) where
  hdr : List Nat
  αfp : Fp8
  γ : Fp8
  αc : Fp8
  z : Fp8
  rest : List Fp8
  finals : List Fp8
  ood : List Fp8
  fp : List Fp8
  hh : τ.header? = some hdr
  hc : τ.chals = αfp :: γ :: αc :: z :: rest
  he : τ.elems = [finals, ood, fp]
  hrest : rest.length = batchRounds (layout A prm hdr) + (friChalKinds A prm hdr).length
  hfp : fp.length = 2

theorem qdata (τ : PTn) (h : (Vnp A prm).global ((Vnp A prm).prep τ.erase) = true) :
    Nonempty (QData A prm τ) := by
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp, -⟩ := prep_inv A prm τ h
  exact ⟨⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp⟩⟩

variable {A prm}
variable {τ : PTn}

theorem QData.hhdr (Q : QData A prm τ) : hdrOf τ = Q.hdr := by simp [hdrOf, Q.hh]
theorem QData.n0 (Q : QData A prm τ) : n0Of A prm τ = queryLog A prm Q.hdr := by simp [n0Of, Q.hhdr]
theorem QData.ell (Q : QData A prm τ) : ellOf A prm τ = finalLayer A prm Q.hdr := by simp [ellOf, Q.hhdr]
theorem QData.lay (Q : QData A prm τ) : layOf A prm τ = layout A prm Q.hdr := by simp [layOf, Q.hhdr]
theorem QData.commits (Q : QData A prm τ) : commitsOf A prm τ = friCommits A prm Q.hdr := by simp [commitsOf, Q.hhdr]
theorem QData.fc (Q : QData A prm τ) : friChals A prm τ = (friChalKinds A prm Q.hdr).zip (Q.rest.drop (batchRounds (layout A prm Q.hdr))) := by
  simp only [friChals, Q.hhdr, Q.hc, nBatch, Q.lay]
  rw [show 4 + batchRounds (layout A prm Q.hdr) = batchRounds (layout A prm Q.hdr) + 1 + 1 + 1 + 1 by
    omega]; rfl

theorem prepF_n0 (Q : QData A prm τ) : (Stark.prep (F := Fp) A prm τ.erase).n0 = n0Of A prm τ := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he, Q.n0]
theorem prepF_ell (Q : QData A prm τ) : (Stark.prep (F := Fp) A prm τ.erase).ℓ = ellOf A prm τ := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he, Q.ell]
theorem prepF_commits (Q : QData A prm τ) : (Stark.prep (F := Fp) A prm τ.erase).commits = commitsOf A prm τ := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he, Q.commits]
theorem prepF_fp (Q : QData A prm τ) : (Stark.prep (F := Fp) A prm τ.erase).finalPoly = Q.fp := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he]
theorem prepF_z (Q : QData A prm τ) : (Stark.prep (F := Fp) A prm τ.erase).z = zOf τ := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he]
  simp [zOf, Q.hc]
theorem prepF_lay (Q : QData A prm τ) : (Stark.prep (F := Fp) A prm τ.erase).lay = layOf A prm τ := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he, Q.lay]

theorem prepF_gammas (Q : QData A prm τ) (i : Nat) :
    (Stark.prep (F := Fp) A prm τ.erase).gammas.lookup i = (friChals A prm τ).lookup (true, i) := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he, Q.fc]
  exact lookup_filter_true _ i

theorem prepF_betas (Q : QData A prm τ) (i : Nat) (hi : i < finalLayer A prm Q.hdr) :
    (Stark.prep (F := Fp) A prm τ.erase).betas.getD i 0 = betaOf A prm τ i := by
  simp only [Stark.prep, erase_header, erase_chals, erase_elems, Q.hh, Q.hc, Q.he, betaOf, Q.fc]
  rw [getD_of_keys 0 (finalLayer A prm Q.hdr) 0 _ ?_ i hi, Nat.zero_add, lookup_filter_false]
  rw [show (fun x : (Bool × Nat) × Fp8 => !x.1.1) = (fun k : Bool × Nat => !k.1) ∘ Prod.fst from rfl,
    ← List.filter_map, List.map_fst_zip (by rw [List.length_drop, Q.hrest]; omega), kinds_filter_false]

theorem gammaOf_of_not (Q : QData A prm τ) (i : Nat) (h : (true, i) ∉ friChalKinds A prm Q.hdr) :
    (friChals A prm τ).lookup (true, i) = none := by
  rw [Q.fc]
  generalize Q.rest.drop (batchRounds (layout A prm Q.hdr)) = D
  generalize friChalKinds A prm Q.hdr = ks at h
  induction ks generalizing D with
  | nil => rfl
  | cons k ks ih =>
    cases D with
    | nil => rfl
    | cons d D =>
      simp only [List.zip_cons_cons, List.lookup]
      have : ((true, i) == k) = false := by
        simp only [beq_eq_false_iff_ne]; exact fun e => h (e ▸ List.mem_cons_self ..)
      rw [this]; exact ih D (fun hm => h (List.mem_cons_of_mem _ hm))

/-- The verifier's roll-in is the FRI run's roll-in. -/
theorem rollIn_eq (Q : QData A prm τ) (i : Nat) (hi1 : 1 ≤ i) (hiℓ : i ≤ finalLayer A prm Q.hdr) (v D : Fp8) :
    (match (Stark.prep (F := Fp) A prm τ.erase).gammas.lookup i with
     | some γ => v + γ * D
     | none => v) =
    v + gammaOf A prm τ i * (if rollInAt A prm Q.hdr i then D else 0) := by
  rw [prepF_gammas Q]
  by_cases hr : rollInAt A prm Q.hdr i = true
  · obtain ⟨w, hw, -⟩ := friChals_lookup A prm τ Q.hdr Q.hhdr Q.rest _ _ _ _ Q.hc
      (by simp only [nBatch, Q.lay]; exact Q.hrest) (true, i) (kinds_roll A prm Q.hdr i hiℓ hr)
    simp [hw, gammaOf, hr]
  · have hn : (true, i) ∉ friChalKinds A prm Q.hdr := by
      intro hm
      simp only [friChalKinds, List.mem_append, List.mem_flatMap, List.mem_range] at hm
      rcases hm with ⟨i', _, hk⟩ | hk
      · rcases hk with hk | hk
        · by_cases hr' : rollInAt A prm Q.hdr i' = true
          · simp only [hr', ↓reduceIte, List.mem_singleton, Prod.mk.injEq, true_and] at hk
            subst hk; exact hr hr'
          · simp [hr'] at hk
        · simp at hk
      · by_cases hr' : rollInAt A prm Q.hdr (finalLayer A prm Q.hdr) = true
        · simp only [hr', ↓reduceIte, List.mem_singleton, Prod.mk.injEq, true_and] at hk
          subst hk; exact hr hr'
        · simp [hr'] at hk
    simp only [gammaOf_of_not Q i hn, hr, Bool.false_eq_true, ↓reduceIte]
    simp [gammaOf, gammaOf_of_not Q i hn]
    grind

end

/-! ## Oracle shapes at the query phase -/

section
variable (A : Air) (prm : Params) (hdr : List Nat)

theorem lookup_none_of_lt {β : Type} : ∀ (l : List (Nat × β)) (N : Nat), (∀ x ∈ l, N < x.1) →
    l.lookup N = none
  | [], _, _ => rfl
  | (c, a) :: l, N, h => by
    have h1 := h (c, a) (List.mem_cons_self ..)
    simp only [List.lookup, show (N == c) = false by simp; omega]
    exact lookup_none_of_lt l N fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem filter_lt_succ {β : Type} : ∀ (l : List (Nat × β)), l.Pairwise (fun x y => x.1 < y.1) → ∀ N,
    l.filter (fun x => decide (x.1 < N + 1)) = l.filter (fun x => decide (x.1 < N)) ++
      (match l.lookup N with | some a => [(N, a)] | none => [])
  | [], _, _ => by simp [List.lookup]
  | (c, a) :: l, hs, N => by
    rw [List.pairwise_cons] at hs
    have ih := filter_lt_succ l hs.2 N
    by_cases h1 : c < N
    · simp only [List.filter_cons, show decide (c < N + 1) = true by simp; omega,
        show decide (c < N) = true by simp; omega, ↓reduceIte, List.lookup,
        show (N == c) = false by simp; omega, ih, List.cons_append]
    · by_cases h2 : c = N
      · subst h2
        have hl : ∀ x ∈ l, c < x.1 := fun x hx => hs.1 x hx
        have e1 : l.filter (fun x => decide (x.1 < c + 1)) = [] :=
          List.filter_eq_nil_iff.mpr fun x hx => by have := hl x hx; simp; omega
        have e2 : l.filter (fun x => decide (x.1 < c)) = [] :=
          List.filter_eq_nil_iff.mpr fun x hx => by have := hl x hx; simp; omega
        simp [List.filter_cons, List.lookup, e1, e2]
      · have hl : ∀ x ∈ l, N < x.1 := fun x hx => by have := hs.1 x hx; omega
        have e1 : l.filter (fun x => decide (x.1 < N + 1)) = [] :=
          List.filter_eq_nil_iff.mpr fun x hx => by have := hl x hx; simp; omega
        have e2 : l.filter (fun x => decide (x.1 < N)) = [] :=
          List.filter_eq_nil_iff.mpr fun x hx => by have := hl x hx; simp; omega
        simp only [List.filter_cons, show decide (c < N + 1) = false by simp; omega,
          show decide (c < N) = false by simp; omega, Bool.false_eq_true, ↓reduceIte, e1, e2,
          List.lookup, show (N == c) = false by simp; omega, lookup_none_of_lt l N hl, List.append_nil]

/-- Shape of the oracle of a commit. -/
def commitShape (c : Nat × Nat) : List (Nat × Nat) :=
  [(queryLog A prm hdr - c.1 - c.2, 8 * 2 ^ c.2)]

theorem flat_layer_shapes (N : Nat) :
    ((List.range N).flatMap (layerS A prm hdr)).flatMap slotOr =
      ((friCommits A prm hdr).filter (fun x => decide (x.1 < N))).map (commitShape A prm hdr) := by
  induction N with
  | zero => simp [List.filter_eq_nil_iff]
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih,
      filter_lt_succ _ (commits_sorted A prm hdr) N, List.map_append, List.flatMap_singleton]
    congr 1
    simp only [layerS]
    by_cases hr : rollInAt A prm hdr N = true <;>
      cases (friCommits A prm hdr).lookup N <;> simp [hr, slotOr, partOr, commitShape]

theorem schedule_shapes :
    (schedule A prm hdr).flatMap slotOr =
      [(layout A prm hdr).map (fun L => (L.lde, L.width)),
       (layout A prm hdr).map (fun L => (L.lde, 8 * L.aux)),
       (layout A prm hdr).map (fun L => (L.lde, 8 * L.quot))] ++
      (friCommits A prm hdr).map (commitShape A prm hdr) := by
  rw [schedule_eq, friSchedule_eq, List.flatMap_append, List.flatMap_append, flat_layer_shapes]
  have hf : (friCommits A prm hdr).filter (fun x => decide (x.1 < finalLayer A prm hdr)) =
      friCommits A prm hdr :=
    List.filter_eq_self.mpr fun x hx => by simp; exact (commits_mem A prm hdr x hx).1
  rw [hf]
  have ht : ((if rollInAt A prm hdr (finalLayer A prm hdr) then [Slot.msg [], .chal false] else []) ++
      [Slot.msg [.elems 2]]).flatMap slotOr = [] := by
    split <;> rfl
  rw [ht, List.append_nil]
  simp only [preSlots, List.flatMap_append, pairs_or, List.append_nil]
  rfl

/-- **The oracles at the query phase.** -/
theorem query_oracles (τ : PTn) (hs : Shaped (Vnp A prm) τ) (hq : (Vnp A prm).AtQuery τ)
    (hh : τ.header? = some hdr) :
    ∃ o0 o1 o2 fris, τ.oracles = o0 :: o1 :: o2 :: fris ∧
      OFit o0 ((layout A prm hdr).map (fun L => (L.lde, L.width))) ∧
      OFit o1 ((layout A prm hdr).map (fun L => (L.lde, 8 * L.aux))) ∧
      OFit o2 ((layout A prm hdr).map (fun L => (L.lde, 8 * L.quot))) ∧
      F2 OFit fris ((friCommits A prm hdr).map (commitShape A prm hdr)) := by
  have hfit := (sh_fit A prm τ hs).1
  have hsl : (Vnp A prm).slots τ = schedule A prm hdr := by
    simp [IopSpec.slots, hh, Vnp, Iop.verifier]
  rw [hq.2, List.take_length, hsl, schedule_shapes] at hfit
  simp only [List.cons_append, List.nil_append] at hfit
  generalize τ.oracles = os at hfit ⊢
  cases hfit with
  | cons h0 t1 =>
    cases t1 with
    | cons h1 t2 =>
      cases t2 with
      | cons h2 t => exact ⟨_, _, _, _, rfl, h0, h1, h2, t⟩

end
end ZkFormal.Udr.Np
