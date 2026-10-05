import ZkFormal.Udr.Poly

/-!
# ZkFormal.Udr.BWLin — underdetermined homogeneous linear systems

Fewer linear functionals than unknowns: a nonzero common zero exists
(elementary Gaussian elimination by induction on the unknowns).
-/

namespace ZkFormal.Udr

open Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- A linear functional on `α → K`. -/
def LinF {α : Type} (f : (α → K) → K) : Prop :=
  ∀ (y y' : α → K) (c : K), f (fun b => y b + c * y' b) = f y + c * f y'

theorem one_ne_zero' : (1 : K) ≠ 0 := by
  intro h
  have := Field.mul_inv_cancel (a := (1 : K)) (by intro h'; exact absurd h' (by grind))
  grind

/-- **Underdetermined systems have nonzero solutions.** -/
theorem exists_nonzero_sol {α : Type} [DecidableEq α] : ∀ (L : List α), L.Nodup →
    ∀ (fs : List ((α → K) → K)), (∀ f ∈ fs, LinF f) → fs.length < L.length →
    ∃ y : α → K, (∀ a, a ∉ L → y a = 0) ∧ (∃ a ∈ L, y a ≠ 0) ∧ ∀ f ∈ fs, f y = 0
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: L, hL, fs, hlin, hlen => by
    rw [List.nodup_cons] at hL
    let δ : α → K := fun b => if b = a then 1 else 0
    have hδa : δ a = 1 := by simp [δ]
    have hδb : ∀ b, b ≠ a → δ b = 0 := fun b hb => by simp [δ, hb]
    by_cases hall : ∀ f ∈ fs, f δ = 0
    · refine ⟨δ, fun b hb => hδb b fun h => hb (h ▸ List.mem_cons_self ..),
        ⟨a, List.mem_cons_self .., by rw [hδa]; exact one_ne_zero'⟩, hall⟩
    · have : ∃ f0 ∈ fs, f0 δ ≠ 0 := Classical.byContradiction fun h =>
        hall fun f hf => Classical.byContradiction fun h' => h ⟨f, hf, h'⟩
      obtain ⟨f0, hf0, hf0δ⟩ := this
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hf0
      have hinv := Field.mul_inv_cancel hf0δ
      have hl0 := hlin f0 (by simp)
      let φ : (α → K) → (α → K) := fun y b => y b + (-(f0 y * (f0 δ)⁻¹)) * δ b
      have hφ0 : ∀ y, f0 (φ y) = 0 := fun y => by
        show f0 (fun b => y b + (-(f0 y * (f0 δ)⁻¹)) * δ b) = 0
        rw [hl0]; grind
      have hφlin : ∀ y y' c, φ (fun b => y b + c * y' b) = fun b => φ y b + c * φ y' b := by
        intro y y' c; funext b
        simp only [φ]; rw [hl0]; grind
      have hlin' : ∀ g ∈ (s ++ t).map (fun f y => f (φ y)), LinF g := by
        intro g hg
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
        have hf' : f ∈ s ++ f0 :: t := by
          rcases List.mem_append.mp hf with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        intro y y' c
        show f (φ _) = f (φ y) + c * f (φ y')
        rw [hφlin]; exact hlin f hf' _ _ _
      have hlen' : ((s ++ t).map (fun f y => f (φ y))).length < L.length := by
        simp only [List.length_map, List.length_append, List.length_cons] at hlen ⊢; omega
      obtain ⟨y, hsupp, ⟨a', ha', hya'⟩, hsol⟩ := exists_nonzero_sol L hL.2 _ hlin' hlen'
      have ha'a : a' ≠ a := fun h => hL.1 (h ▸ ha')
      refine ⟨φ y, fun b hb => ?_, ⟨a', List.mem_cons_of_mem _ ha', ?_⟩, fun f hf => ?_⟩
      · have hba : b ≠ a := fun h => hb (h ▸ List.mem_cons_self ..)
        show y b + _ * δ b = 0
        rw [hsupp b fun h => hb (List.mem_cons_of_mem _ h), hδb b hba]; grind
      · show y a' + _ * δ a' ≠ 0
        rw [hδb a' ha'a]; intro h; exact hya' (by grind)
      · rcases List.mem_append.mp hf with h | h
        · exact hsol _ (List.mem_map.mpr ⟨f, List.mem_append_left _ h, rfl⟩)
        · rcases List.mem_cons.mp h with rfl | h
          · exact hφ0 y
          · exact hsol _ (List.mem_map.mpr ⟨f, List.mem_append_right _ h, rfl⟩)

end ZkFormal.Udr
