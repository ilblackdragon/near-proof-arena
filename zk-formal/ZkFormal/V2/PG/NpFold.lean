import ZkFormal.V2.PG.NpFriPoly

/-!
# ZkFormal.V2.PG.NpFold (P2 copy of `Prover.NpFold` at `dp = pg g`) — the verifier's leaf folds on honest committed layers
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

attribute [local instance] Semiring.natCast

theorem chunksOf_go_two' {α : Type} : ∀ (N : Nat) (f : Nat → α) (s fuel : Nat), N ≤ fuel →
    chunksOf.go 2 fuel ((List.range' s (2 * N)).map f) =
      (List.range' 0 N).map fun k => [f (s + 2 * k), f (s + 2 * k + 1)]
  | 0, f, s, fuel, _ => by cases fuel <;> rfl
  | N + 1, f, s, fuel, h => by
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, List.range'_succ, List.range'_succ,
      List.map_cons, List.map_cons]
    show [f s, f (s + 1)] :: chunksOf.go 2 fuel' ((List.range' (s + 1 + 1) (2 * N)).map f) = _
    rw [chunksOf_go_two' N f (s + 1 + 1) fuel' (by omega), List.range'_succ, List.map_cons]
    simp only [Nat.mul_zero, Nat.add_zero]
    congr 1
    rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map, List.map_map]
    apply List.map_congr_left; intro k _
    simp only [Function.comp]
    rw [show s + 1 + 1 + 2 * (0 + k) = s + 2 * (0 + 1 + k) by omega]

theorem chunksOf_two {α : Type} (N : Nat) (f : Nat → α) :
    chunksOf 2 ((List.range (2 * N)).map f) = (List.range N).map fun k => [f (2 * k), f (2 * k + 1)] := by
  unfold chunksOf
  rw [List.range_eq_range', chunksOf_go_two' N f 0 _ (by simp; omega), List.range_eq_range']
  simp

theorem zipIdx_map_range {α : Type} (N : Nat) (g : Nat → α) :
    ((List.range N).map g).zipIdx = (List.range N).map fun k => (g k, k) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getElem_zipIdx]

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

/-- Layer `i+1` before its roll-in. -/
noncomputable def preW (i q : Nat) : Fp8 :=
  (2 : Fp8)⁻¹ * (word A cb tr cs i (2 * q) + word A cb tr cs i (2 * q + 1)) +
    (betaL A tr cs).getD i 0 * (word A cb tr cs i (2 * q) - word A cb tr cs i (2 * q + 1)) *
      Fp8.ofBase (((2 : Fp) * domPoint (F := Fp) (K := Fp8) (n0 A tr) (n0 A tr - i) (2 * q))⁻¹)

theorem word_succ (i q : Nat) : word A cb tr cs (i + 1) q =
    match (gammaL A tr cs).lookup (i + 1) with
    | some g => preW A cb tr cs i q + g * Bw A cb tr cs (n0 A tr - (i + 1)) q
    | none => preW A cb tr cs i q := rfl

theorem foldOnce_word (c : Ctx Fp8) (hn : c.n0 = n0 A tr) (i base N : Nat) (hbase : base % 2 = 0) :
    foldOnce (F := Fp) c i base ((betaL A tr cs).getD i 0)
      ((List.range (2 * N)).map fun q => word A cb tr cs i (base + q)) =
    (List.range N).map fun k => preW A cb tr cs i (base / 2 + k) := by
  unfold foldOnce
  rw [chunksOf_two, zipIdx_map_range, List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp, List.getD_cons_zero, List.getD_cons_succ, hn]
  unfold preW
  rw [show base + 2 * k = 2 * (base / 2 + k) by omega, show base + (2 * k + 1) = 2 * (base / 2 + k) + 1 by omega]
  rfl

theorem word_eq_preW {i q : Nat} (h : (gammaL A tr cs).lookup (i + 1) = none) :
    word A cb tr cs (i + 1) q = preW A cb tr cs i q := by
  rw [word_succ, h]

/-- **A committed leaf folds to the next layer** (before its roll-in). -/
theorem foldLeaf_word (c : Ctx Fp8) (hn : c.n0 = n0 A tr) (hb : c.betas = betaL A tr cs)
    (c0 a j : Nat) (ha : 1 ≤ a) (hno : ∀ i, c0 < i → i < c0 + a → (gammaL A tr cs).lookup i = none) :
    foldLeaf (F := Fp) c c0 a j ((List.range (2 ^ a)).map fun s => word A cb tr cs c0 (j * 2 ^ a + s)) =
      preW A cb tr cs (c0 + a - 1) j := by
  unfold foldLeaf
  let F := fun (acc : List Fp8) (s : Nat) => foldOnce (F := Fp) c (c0 + s) (j <<< (a - s)) (c.betas.getD (c0 + s) 0) acc
  let us := (List.range (2 ^ a)).map fun s => word A cb tr cs c0 (j * 2 ^ a + s)
  have step : ∀ s, s < a → ∀ acc, acc = (List.range (2 ^ (a - s))).map (fun q => word A cb tr cs (c0 + s)
      (j * 2 ^ (a - s) + q)) → F acc s = (List.range (2 ^ (a - s - 1))).map
        (fun q => preW A cb tr cs (c0 + s) (j * 2 ^ (a - s - 1) + q)) := by
    intro s hs acc hacc
    show foldOnce (F := Fp) c (c0 + s) (j <<< (a - s)) (c.betas.getD (c0 + s) 0) acc = _
    rw [hb, hacc, Nat.shiftLeft_eq, show 2 ^ (a - s) = 2 * 2 ^ (a - s - 1) by
      rw [← Nat.pow_succ']; congr 1; omega, foldOnce_word A cb tr cs c hn _ _ _ (by
        rw [show j * (2 * 2 ^ (a - s - 1)) = 2 * (j * 2 ^ (a - s - 1)) by
          rw [Nat.mul_left_comm]]; simp)]
    apply List.map_congr_left; intro k _
    congr 1
    rw [show j * (2 * 2 ^ (a - s - 1)) = 2 * (j * 2 ^ (a - s - 1)) by rw [Nat.mul_left_comm]]
    omega
  have inv : ∀ s, s < a → (List.range s).foldl F us = (List.range (2 ^ (a - s))).map
      (fun q => word A cb tr cs (c0 + s) (j * 2 ^ (a - s) + q)) := by
    intro s
    induction s with
    | zero => intro _; simp [us]
    | succ s ih =>
      intro hs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        step s (by omega) _ (ih (by omega))]
      apply List.map_congr_left; intro q _
      rw [show a - (s + 1) = a - s - 1 by omega, show c0 + (s + 1) = (c0 + s) + 1 by omega,
        word_eq_preW A cb tr cs (hno _ (by omega) (by omega))]
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  show ((List.range (a' + 1)).foldl F us).getD 0 0 = _
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, step a' (by omega) _ (inv a' (by omega))]
  simp [show a' + 1 - a' - 1 = 0 by omega, show c0 + (a' + 1) - 1 = c0 + a' by omega]

end

end ZkFormal.V2.PG
