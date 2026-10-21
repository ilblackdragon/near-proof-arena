import Mathlib

/-!
# Local Merkle support needed by the family potential

An inserted node whose output is neither a root nor a child reference is
unreachable. This is a deterministic graph fact, including cyclic graphs;
it does not require treating ordinary transcript edges as bad events.

The reference count below distinguishes node outputs, node children, one-root
commit calls, and fixed VK roots. The native transcript's `observe_commit`
flushes then hashes one digest. Showing that these are *all* roots used by the
protocol's canonical extractor, and handling wide-query transitions, remain
separate obligations. These lemmas alone do not prove the family bound.
-/
namespace Qrom.MerkleSupport
variable {Y : Type}

inductive Reach (roots : Set Y) (edge : Y → Y → Prop) : Y → Prop
  | root (y : Y) : y ∈ roots → Reach roots edge y
  | step {a b : Y} : Reach roots edge a → edge a b → Reach roots edge b

def insertEdges (edge : Y → Y → Prop) (output : Y) (children : Set Y) : Y → Y → Prop :=
  fun a b => edge a b ∨ (a = output ∧ b ∈ children)

/-- Inserting an unreferenced output cannot change the reachable graph. -/
theorem orphan_unreachable (roots : Set Y) (edge : Y → Y → Prop)
    (output : Y) (children : Set Y) (hroot : output ∉ roots)
    (hincoming : ∀ a, ¬ edge a output) {y : Y}
    (h : Reach roots (insertEdges edge output children) y) :
    Reach roots edge y ∧ y ≠ output := by
  induction h with
  | root y hy =>
      refine ⟨Reach.root y hy, ?_⟩
      intro he; exact hroot (he ▸ hy)
  | @step a b _ hab ih =>
      rcases hab with hold | ⟨ha, _⟩
      · refine ⟨Reach.step ih.1 hold, ?_⟩
        intro hb; exact hincoming a (hb ▸ hold)
      · exact False.elim (ih.2 ha)

theorem orphan_preserves_reach (roots : Set Y) (edge : Y → Y → Prop)
    (output : Y) (children : Set Y) (hroot : output ∉ roots)
    (hincoming : ∀ a, ¬ edge a output) (y : Y) :
    Reach roots (insertEdges edge output children) y ↔ Reach roots edge y := by
  constructor
  · exact fun h => (orphan_unreachable roots edge output children hroot hincoming h).1
  · intro h
    induction h with
    | root y hy => exact Reach.root y hy
    | step _ hab ih => exact Reach.step ih (Or.inl hab)

/-- At most two children per binary node and one root per commit. Constants
must be charged separately; the support count is not a bound on transcript size. -/
theorem target_count {I J : Type} [DecidableEq Y]
    (nodes : Finset I) (commits : Finset J) (constants : Finset Y)
    (output : I → Y) (refs : I → Finset Y) (root : J → Y)
    (hrefs : ∀ i ∈ nodes, (refs i).card ≤ 2) (q : ℕ)
    (hsupport : nodes.card + commits.card ≤ q) :
    (constants ∪ nodes.image output ∪ nodes.biUnion refs ∪ commits.image root).card ≤
      constants.card + 3*q := by
  have h1 := Finset.card_image_le (s := nodes) (f := output)
  have h2 := Finset.card_image_le (s := commits) (f := root)
  have h3 := Finset.card_biUnion_le (s := nodes) (t := refs)
  have h4 : ∑ i ∈ nodes, (refs i).card ≤ 2 * nodes.card := by
    calc
      _ ≤ ∑ _i ∈ nodes, 2 := Finset.sum_le_sum hrefs
      _ = _ := by simp [Nat.mul_comm]
  have hu1 := Finset.card_union_le constants (nodes.image output)
  have hu2 := Finset.card_union_le (constants ∪ nodes.image output) (nodes.biUnion refs)
  have hu3 := Finset.card_union_le
    (constants ∪ nodes.image output ∪ nodes.biUnion refs) (commits.image root)
  omega

end Qrom.MerkleSupport

#print axioms Qrom.MerkleSupport.orphan_preserves_reach
#print axioms Qrom.MerkleSupport.target_count
