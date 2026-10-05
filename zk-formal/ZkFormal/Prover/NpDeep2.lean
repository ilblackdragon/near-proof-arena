import ZkFormal.Prover.NpDeep

/-!
# ZkFormal.Prover.NpDeep2 — honest openings in the DEEP batch
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

theorem foldl_ext_mem {α β : Type} (f g : α → β → α) : ∀ (l : List β), (∀ b ∈ l, ∀ a, f a b = g a b) →
    ∀ a, l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, h, a => by
    rw [List.foldl_cons, List.foldl_cons, h b (by simp), foldl_ext_mem f g l (fun b' hb' => h b' (by simp [hb']))]

theorem deepZ_congr (c : Ctx Fp8) (m : Nat) (ξ : Fp8) (M Aux Q M' Aux' Q' : Nat → List Fp8)
    (h : ∀ q ∈ classRows c m, M q.2 = M' q.2 ∧ Aux q.2 = Aux' q.2 ∧ Q q.2 = Q' q.2) :
    deepZ c m ξ M Aux Q = deepZ c m ξ M' Aux' Q' := by
  unfold deepZ
  have hf := foldl_ext_mem (deepStep M Aux Q) (deepStep M' Aux' Q') (classRows c m) (fun q hq a => by
    obtain ⟨h1, h2, h3⟩ := h q hq
    simp only [deepStep, h1, h2, h3]) (0, 0)
  split <;> simp only [hf]

theorem deepZ_ctx {c c' : Ctx Fp8} (hl : c.lay = c'.lay) (hd : c.deep = c'.deep) (hz : c.z = c'.z)
    (m : Nat) (ξ : Fp8) (M Aux Q : Nat → List Fp8) : deepZ c m ξ M Aux Q = deepZ c' m ξ M Aux Q := by
  unfold deepZ classRows; rw [hl, hd, hz]

/-- Class rows are the tables of LDE log `m`. -/
theorem classRows_mem {c : Ctx Fp8} {m : Nat} {q : (TLayout × TDeep Fp8) × Nat} (hq : q ∈ classRows c m) :
    q.1.1.lde = m ∧ ∃ h : q.2 < c.lay.length, c.lay[q.2] = q.1.1 := by
  unfold classRows at hq
  obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
  have := List.mem_zipIdx_iff_getElem?.mp hq1
  rw [List.getElem?_zip_eq_some] at this
  obtain ⟨h1, _⟩ := this
  refine ⟨by simpa using hq2, ?_⟩
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp h1
  exact ⟨hlt, he⟩

theorem chunksOf_go_eight (n : Nat) : ∀ (xs : List Fp8), xs.length * 8 ≤ n →
    chunksOf.go 8 n (limbsL xs) = xs.map fun x => StarkField.limbs (F := Fp) x
  | [], _ => by cases n <;> rfl
  | x :: xs, h => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at h; omega⟩
    have hl : (StarkField.limbs (F := Fp) x).length = 8 := rfl
    unfold limbsL
    rw [List.flatMap_cons]
    show (StarkField.limbs (F := Fp) x ++ limbsL xs).take 8 :: chunksOf.go 8 n' ((StarkField.limbs (F := Fp) x ++
      limbsL xs).drop 8) = _
    rw [List.take_left' hl, List.drop_left' hl, chunksOf_go_eight n' xs (by simp at h; omega)]
    rfl

theorem ksOfRow_limbsL (xs : List Fp8) : ksOfRow (F := Fp) (limbsL xs) = xs := by
  unfold ksOfRow chunksOf
  rw [length_limbsL, chunksOf_go_eight _ xs (by omega), List.map_map]
  conv => rhs; rw [← List.map_id xs]
  apply List.map_congr_left; intro x _; rfl

end ZkFormal.Prover.Np
