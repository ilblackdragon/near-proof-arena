import ZkFormal.Udr.Np.Bridge4

/-!
# ZkFormal.Udr.Np.Bridge5 — FRI layer words at committed and virtual layers

* `friF_committed`: at the layer of commit `k` the FRI word is the committed oracle;
* `friF_virtual`: at a layer `i + 1` without commitment it is the fold of
  layer `i` plus the roll-in (definitionally the run's `rollW`);
* `DeepSemStmt`: the verifier's batched DEEP value from the true openings is
  the batched DEEP word (open; see `Bridge6` for its use).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- **DEEP semantics** (open sublemma): at the query phase the verifier's
`deepAt` of class `m` from the true openings at position `x` is the batched
DEEP word of class `m` at the class position `x >>> (n0 - m)`. -/
def DeepSemStmt : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ (τ : PTn),
    Shaped (Vnp A prm) τ → (Vnp A prm).AtQuery τ →
    (Vnp A prm).global ((Vnp A prm).prep τ.erase) = true →
    ∀ x, x < 2 ^ n0Of A prm τ → ∀ m, m ≤ n0Of A prm τ →
      deepAt (F := Fp) (Stark.prep (F := Fp) A prm τ.erase) ((Vnp A prm).trueOpenings τ x) m x =
        deepAtPos A prm τ m (x >>> (n0Of A prm τ - m))

section
variable (A : Air) (prm : Params)

/-- Distinct commits sit at distinct layers. -/
theorem commits_layer_inj (hdr : List Nat) (k k' : Nat) (hk : k < (friCommits A prm hdr).length)
    (hk' : k' < (friCommits A prm hdr).length)
    (h : ((friCommits A prm hdr)[k]).1 = ((friCommits A prm hdr)[k']).1) : k = k' := by
  have hs := List.pairwise_iff_getElem.mp (commits_sorted A prm hdr)
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := hs k k' hk hk' hlt; omega
  · exact heq
  · have := hs k' k hk' hk hgt; omega

theorem commits_zero (hdr : List Nat) (hk : 0 < (friCommits A prm hdr).length) :
    ((friCommits A prm hdr)[0]).1 = 0 :=
  commits_head A prm hdr _ (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk])

/-- The FRI word at a committed layer. -/
theorem friF_committed (τ : PTn) (k : Nat) (hk : k < (commitsOf A prm τ).length) (j' : Nat) :
    friF A prm τ ((commitsOf A prm τ)[k]).1 j' () =
      committedAt τ k ((commitsOf A prm τ)[k]).2 (permAt A prm τ ((commitsOf A prm τ)[k]).1 j') := by
  have hcm : commitsOf A prm τ = friCommits A prm (hdrOf τ) := rfl
  by_cases h0 : ((commitsOf A prm τ)[k]).1 = 0
  · have hk0 : k = 0 := by
      have := commits_zero A prm (hdrOf τ) (by rw [← hcm]; omega)
      exact commits_layer_inj A prm (hdrOf τ) k 0 (by rw [← hcm]; exact hk) (by rw [← hcm]; omega)
        (by simp only [← hcm] at this ⊢; rw [this]; exact h0)
    subst hk0
    rw [h0]
    have hh : (commitsOf A prm τ).head? = some (commitsOf A prm τ)[0] := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk]
    simp only [friF, hh]
  · obtain ⟨i, hi⟩ : ∃ i, ((commitsOf A prm τ)[k]).1 = i + 1 :=
      ⟨((commitsOf A prm τ)[k]).1 - 1, by omega⟩
    rw [hi]
    simp only [friF]
    cases hf : List.find? (fun x : (Nat × Nat) × Nat => x.1.fst == i + 1) (commitsOf A prm τ).zipIdx with
    | some e =>
      obtain ⟨⟨c, a⟩, k'⟩ := e
      simp only
      have hm := List.mem_of_find?_eq_some hf
      have hpc := List.find?_some hf
      simp only [beq_iff_eq] at hpc
      have hk2 := List.mem_zipIdx_iff_getElem?.mp hm
      simp only at hk2
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk2
      have hkk : k' = k := commits_layer_inj A prm (hdrOf τ) k' k (by rw [← hcm]; exact hlt)
        (by rw [← hcm]; exact hk) (by simp only [← hcm]; rw [hget, hi]; exact hpc)
      subst hkk
      rw [hget]
    | none =>
      have := List.find?_eq_none.mp hf (((commitsOf A prm τ)[k]), k)
        (List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hk]))
      simp only [hi, beq_self_eq_true, not_true_eq_false] at this

/-- The FRI word at a layer without commitment. -/
theorem friF_virtual (τ : PTn) (i : Nat)
    (h : ∀ k (hk : k < (commitsOf A prm τ).length), ((commitsOf A prm τ)[k]).1 ≠ i + 1) :
    friF A prm τ (i + 1) =
      line (line (fun j _ => (friF A prm τ i j () + friF A prm τ i (j + (setupData A prm τ).nn (i + 1)) ()) *
          (2 : Fp8)⁻¹)
        (fun j _ => (friF A prm τ i j () - friF A prm τ i (j + (setupData A prm τ).nn (i + 1)) ()) *
          (2 * (setupData A prm τ).xs i j)⁻¹) (betaOf A prm τ i))
        (rollG A prm τ i) (gammaOf A prm τ (i + 1)) := by
  conv => lhs; simp only [friF]
  split
  · rename_i c a k' hf
    have hm := List.mem_of_find?_eq_some hf
    have hpc := List.find?_some hf
    simp only [beq_iff_eq] at hpc
    have hk2 := List.mem_zipIdx_iff_getElem?.mp hm
    simp only at hk2
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk2
    exact absurd (by rw [hget]; exact hpc) (h k' hlt)
  · rfl

end
end ZkFormal.Udr.Np
