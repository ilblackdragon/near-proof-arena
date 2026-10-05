import ZkFormal.Udr.Np.QueryParts

/-!
# ZkFormal.Udr.Np.QueryFacts — what the verifier's context says about a transcript

* erasure commutes with `header?`, `chals`, `elems`, `oracles` (lengths);
* `prep_inv`: if `global (prep τ.erase)` holds, the transcript has the
  expected challenges and clear-text parts, all lengths check, and the
  global checks hold on them (so `GlobalFail` is false);
* header facts (`lay_facts`): every table class has `5 ≤ lde ≤ 26`, `lde = log + 4`;
* class sizes: `(deepCols lay m).length ≤ 2 ^ batchRounds lay`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Erasure -/

section
variable {K O : Type}

theorem erase_header (τ : PT K O) : τ.erase.header? = τ.header? := by
  rcases τ with ⟨cb, es⟩
  simp only [PT.erase, PT.header?]
  rcases es with _ | ⟨e, es⟩
  · rfl
  · rcases e with ps | c
    · rcases ps with _ | ⟨p, ps⟩
      · rfl
      · rcases p <;> rfl
    · rfl

theorem erase_chals (τ : PT K O) : τ.erase.chals = τ.chals := by
  rcases τ with ⟨cb, es⟩
  simp only [PT.erase, PT.chals]
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, ih]
    rcases e <;> rfl

theorem erase_elems (τ : PT K O) : τ.erase.elems = τ.elems := by
  rcases τ with ⟨cb, es⟩
  simp only [PT.erase, PT.elems]
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]
    rcases e with ps | c
    · congr 1
      simp only [PT.Entry.erase]
      induction ps with
      | nil => rfl
      | cons p ps ihp =>
        rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, ihp]
        rcases p <;> rfl
    · rfl

end

/-! ## Inverting `prep` -/

section
variable (A : Air) (prm : Params)

/-- What `global (prep τ.erase) = true` says. -/
theorem prep_inv (τ : PTn) (h : (Vnp A prm).global ((Vnp A prm).prep τ.erase) = true) :
    ∃ hdr αfp γ αc z rest finals ood fp, τ.header? = some hdr ∧
      τ.chals = αfp :: γ :: αc :: z :: rest ∧ τ.elems = [finals, ood, fp] ∧
      rest.length = batchRounds (layout A prm hdr) + (friChalKinds A prm hdr).length ∧
      fp.length = 2 ∧
      globalChecks (F := Fp) A prm (pubOf Fp τ.cb) (layout A prm hdr)
        (splitOod (layout A prm hdr) ood).1 finals αfp γ αc z = true := by
  simp only [Vnp, Iop.verifier, Stark.prep, erase_header, erase_chals, erase_elems] at h
  split at h
  · simp [Ctx.bad] at h
  · rename_i hdr hh
    split at h
    · rename_i αfp γ αc z rest finals ood fp hc he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, h.1.1.1.1, h.1.1.1.2, h.2⟩
    · simp [Ctx.bad] at h

/-- With `global` accepting, the clear-text checks do not fail. -/
theorem not_globalFail (τ : PTn) (h : (Vnp A prm).global ((Vnp A prm).prep τ.erase) = true) :
    ¬ GlobalFail A prm τ := by
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, -, -, hg⟩ := prep_inv A prm τ h
  simp only [GlobalFail, hc, he]
  have : layOf A prm τ = layout A prm hdr := by simp [layOf, hdrOf, hh]
  rw [this, hg]; simp

end

/-! ## Header facts (deployed parameters) -/

section
variable (A : Air)

theorem lay_facts (hdr : List Nat) (h : headerOk A Params.default hdr = true) :
    ∀ L ∈ layout A Params.default hdr, 5 ≤ L.lde ∧ L.lde ≤ 26 ∧ L.lde = L.log + 4 := by
  simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro L hL
  simp only [layout, List.mem_map] at hL
  obtain ⟨⟨T, l⟩, hm, rfl⟩ := hL
  have := h.1.1.2 _ hm
  simp only [Params.default] at this
  show 5 ≤ l + 4 ∧ l + 4 ≤ 26 ∧ l + 4 = l + 4
  omega

theorem foldr_max_le (l : List Nat) (b c : Nat) (hb : b ≤ c) (h : ∀ x ∈ l, x ≤ c) :
    l.foldr max b ≤ c := by
  induction l with
  | nil => exact hb
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem le_foldr_max (l : List Nat) (b x : Nat) (hx : x ∈ l) : x ≤ l.foldr max b := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem queryLog_le (hdr : List Nat) (h : headerOk A Params.default hdr = true) :
    queryLog A Params.default hdr ≤ 26 :=
  foldr_max_le _ _ _ (by omega) fun x hx => by
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hx
    exact (lay_facts A hdr h L hL).2.1

theorem lde_le_queryLog (prm : Params) (hdr : List Nat) (L : TLayout) (hL : L ∈ layout A prm hdr) :
    L.lde ≤ queryLog A prm hdr :=
  le_foldr_max _ _ _ (List.mem_map.mpr ⟨L, hL, rfl⟩)

end

/-! ## Class sizes -/

theorem sum_filter_zipIdx {α : Type} (P : α → Bool) (g : α → Nat) :
    ∀ (lay : List α) (s : Nat),
      (((lay.zipIdx s).filter (fun x => P x.1)).map (fun a => g a.1)).sum = ((lay.filter P).map g).sum
  | [], _ => rfl
  | L :: lay, s => by
    simp only [List.zipIdx_cons, List.filter_cons]
    by_cases hL : P L = true
    · simp only [hL, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [sum_filter_zipIdx P g lay (s + 1)]
    · simp only [hL, Bool.false_eq_true, ↓reduceIte]
      exact sum_filter_zipIdx P g lay (s + 1)

theorem deepCols_length (lay : List TLayout) (m : Nat) :
    (deepCols lay m).length = classCount lay m := by
  simp only [deepCols, classCount, List.length_flatMap, List.length_append, List.length_map,
    List.length_range]
  refine (sum_filter_zipIdx (fun L => L.lde == m)
    (fun L => L.width + L.width + L.aux + L.aux + L.quot) lay 0).trans ?_
  congr 1
  apply List.map_congr_left
  intro L _; omega

theorem classCount_le_pow (lay : List TLayout) (L : TLayout) (hL : L ∈ lay) :
    classCount lay L.lde ≤ 2 ^ batchRounds lay := by
  simp only [batchRounds]
  generalize hc : (lay.map fun L => classCount lay L.lde).foldr max 2 = c
  have h1 : classCount lay L.lde ≤ c :=
    hc ▸ le_foldr_max _ _ _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
  have h2 : 2 ≤ c := by
    rw [← hc]
    clear hc h1 hL
    induction lay.map fun L => classCount lay L.lde with
    | nil => exact Nat.le_refl _
    | cons a l ih => simp only [List.foldr_cons]; exact Nat.le_trans ih (Nat.le_max_right _ _)
  have h3 := @Nat.lt_log2_self (2 * c - 1)
  rw [Nat.pow_succ] at h3
  have h4 : 2 ^ Nat.log2 (2 * c - 1) ≤ 2 ^ max 1 (Nat.log2 (2 * c - 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  omega

theorem deepCols_length_le (lay : List TLayout) (L : TLayout) (hL : L ∈ lay) :
    (deepCols lay L.lde).length ≤ 2 ^ batchRounds lay := by
  rw [deepCols_length]; exact classCount_le_pow lay L hL

end ZkFormal.Udr.Np
