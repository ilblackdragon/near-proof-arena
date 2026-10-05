import ZkFormal.Udr.Np.Query

/-!
# ZkFormal.Udr.Np.Good — `GoodStmt`: the drawn FRI challenges are good

At the query phase all FRI challenges have been drawn (`prep_inv`), so for
every layer `i < ℓ` the fold challenge `β_i` (kind `(false, i)`) and, when a
class rolls in at `i + 1`, the roll-in challenge `γ_{i+1}` (kind
`(true, i+1)`) occur in `friChals`; `FriGoodSoFar` gives their strong-line
conditions, which are `Fri.GoodChallenges` of `mkSetup`/`mkRun`.  Without a
roll-in the roll-in word is zero and the condition is trivial.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

theorem strong_zero {K ι : Type} [Field K] {n d : Nat} (C : LinCode ι K n d) (e : Nat)
    (u0 : Word ι K) (z : K) : Strong C e u0 (fun _ _ => 0) z := by
  intro w hw _
  refine ⟨w, fun _ _ => 0, hw, C.zero, fun i _ h => ⟨?_, rfl⟩⟩
  rw [← h]; funext c; simp only [line]; grind

theorem lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] (k : α) :
    ∀ (l : List (α × β)), k ∈ l.map Prod.fst → ∃ v, l.lookup k = some v ∧ (k, v) ∈ l
  | [], h => by simp at h
  | (a, b) :: l, h => by
    by_cases hk : k = a
    · subst hk; exact ⟨b, by simp [List.lookup], List.mem_cons_self ..⟩
    · have hm : k ∈ l.map Prod.fst := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hk
        · exact h
      obtain ⟨v, h1, h2⟩ := lookup_of_mem k l hm
      refine ⟨v, ?_, List.mem_cons_of_mem _ h2⟩
      have : (k == a) = false := by simp [hk]
      simp [List.lookup, this, h1]

theorem mem_zip_fst {α β : Type} (k : α) :
    ∀ (ks : List α) (cs : List β), ks.length ≤ cs.length → k ∈ ks → k ∈ (ks.zip cs).map Prod.fst
  | [], _, _, h => by simp at h
  | a :: ks, [], hl, _ => by simp at hl
  | a :: ks, c :: cs, hl, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · simp only [List.zip_cons_cons, List.map_cons, List.mem_cons]
      exact Or.inr (mem_zip_fst k ks cs (by simp at hl; omega) h)

section
variable (A : Air) (prm : Params)

theorem kinds_fold (hdr : List Nat) (i : Nat) (hi : i < finalLayer A prm hdr) :
    (false, i) ∈ friChalKinds A prm hdr := by
  simp only [friChalKinds, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl ⟨i, hi, by simp⟩

theorem kinds_roll (hdr : List Nat) (i : Nat) (hi : i ≤ finalLayer A prm hdr)
    (hr : rollInAt A prm hdr i = true) : (true, i) ∈ friChalKinds A prm hdr := by
  simp only [friChalKinds, List.mem_append, List.mem_flatMap, List.mem_range]
  by_cases h : i < finalLayer A prm hdr
  · exact Or.inl ⟨i, h, by simp [hr]⟩
  · have : i = finalLayer A prm hdr := by omega
    subst this
    exact Or.inr (by simp [hr])

/-- A drawn challenge of a kind that occurs. -/
theorem friChals_lookup (τ : PTn) (hdr : List Nat) (hh : hdrOf τ = hdr) (rest : List Fp8)
    (a b c d : Fp8) (hc : τ.chals = a :: b :: c :: d :: rest)
    (hrest : rest.length = nBatch A prm τ + (friChalKinds A prm hdr).length)
    (k : Bool × Nat) (hk : k ∈ friChalKinds A prm hdr) :
    ∃ v, (friChals A prm τ).lookup k = some v ∧ (k, v) ∈ friChals A prm τ := by
  apply lookup_of_mem
  simp only [friChals, hh, hc]
  refine mem_zip_fst k _ _ ?_ hk
  rw [List.length_drop]; simp only [List.length_cons]; omega

theorem good_of_mem (τ : PTn) (hg : FriGoodSoFar A prm τ) (k : Bool × Nat) (v : Fp8)
    (h : (k, v) ∈ friChals A prm τ) : FriChalGood A prm τ k.1 k.2 v := by
  obtain ⟨q, hq, he⟩ := List.getElem_of_mem h
  have := hg q hq
  rw [he] at this
  exact this

end

theorem good : GoodStmt := by
  intro A prm hok τ hn0 hs hq hglob hgood
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp, hgc⟩ :=
    prep_inv A prm τ hglob
  have hhdr : hdrOf τ = hdr := by simp [hdrOf, hh]
  have hrest' : rest.length = nBatch A prm τ + (friChalKinds A prm hdr).length := by
    simp only [nBatch, layOf, hhdr]; exact hrest
  have hℓ : ellOf A prm τ = finalLayer A prm hdr := by simp [ellOf, hhdr]
  intro i hi
  have hi' : i < finalLayer A prm hdr := by rw [← hℓ]; exact hi
  constructor
  · -- fold challenge
    obtain ⟨v, hv, hmem⟩ := friChals_lookup A prm τ hdr hhdr rest _ _ _ _ hc hrest' _
      (kinds_fold A prm hdr i hi')
    have hb : betaOf A prm τ i = v := by simp [betaOf, hv]
    have := good_of_mem A prm τ hgood _ _ hmem
    simp only [FriChalGood, Bool.false_eq_true, ↓reduceIte] at this
    show Strong _ _ (evenF A prm τ i) (oddF A prm τ i) (betaOf A prm τ i)
    rw [hb]; exact this
  · -- roll-in challenge
    by_cases hr : rollInAt A prm hdr (i + 1) = true
    · obtain ⟨v, hv, hmem⟩ := friChals_lookup A prm τ hdr hhdr rest _ _ _ _ hc hrest' _
        (kinds_roll A prm hdr (i + 1) hi' hr)
      have hb : gammaOf A prm τ (i + 1) = v := by simp [gammaOf, hv]
      have := good_of_mem A prm τ hgood _ _ hmem
      simp only [FriChalGood, ↓reduceIte, Nat.add_sub_cancel] at this
      show Strong _ _ (foldF A prm τ i) (rollG A prm τ i) (gammaOf A prm τ (i + 1))
      rw [hb]; exact this
    · have hz : rollG A prm τ i = fun _ _ => 0 := by
        funext j u
        simp only [rollG, hhdr]
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
      show Strong _ _ _ (rollG A prm τ i) _
      rw [hz]; exact strong_zero _ _ _ _

/-- `QueryStmt` from the local bridge alone. -/
theorem query_of_bridge (hLB : LocalBridgeStmt) : QueryStmt := query_of hLB good

end ZkFormal.Udr.Np
