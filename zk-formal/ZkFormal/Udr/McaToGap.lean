import ZkFormal.Udr.Statements
import ZkFormal.Udr.Code

/-!
# Unique-decoding utilities (not the DKT-to-WHIR list-decoding bridge)

`mca_count_to_gap` restates a premise that is definitionally `LineGap`.
`strong_from_mca` applies an existing theorem **only when `2 * e < d`** and
returns `max E e`, not E. These declarations do not instantiate DKT26 at
Johnson or beyond-Johnson radii. They are retained for compatibility.

The valid RS-level Johnson/interleaving/tensor-fold composition is in the
Mathlib/ArkLib companion `research/near-compression/final-soundness/lean/DKTGlue.lean`.
Connecting its full-agreement-set conclusions (and the O-2 certificates) to the
actual WHIR folding, block distance and round-by-round state is a separate,
still open formalization obligation. `fold_union` below is an arithmetic sum
bound, not a proof about adaptively sampled fold transcripts.
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

section Field
variable {K : Type} [Field K] {ι : Type}

/-- Definitional restatement of a supplied `LineGap` premise; no DKT theorem is
imported or instantiated here. -/
theorem mca_count_to_gap {n d : Nat} (C : LinCode ι K n d) {e E : Nat}
    (hcount : ∀ (u0 u1 : Word ι K) (Ks : List K), Ks.Nodup →
      E < count Ks (fun z => Good C e u0 u1 z) → CA C e u0 u1) :
    LineGap C e E :=
  hcount

/-- Unique-decoding corollary of an assumed gap. The exceptional count is
`max E e`; this does not extend containment to list-decoding radii. -/
theorem strong_from_mca {n d : Nat} (C : LinCode ι K n d) {e E : Nat} (he : 2 * e < d)
    (hgap : LineGap C e E) (u0 u1 : Word ι K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong C e u0 u1 z) ≤ max E e :=
  strong_of_gap C he hgap u0 u1 Ks hKs

/-- `foldr` with addition is the base value plus the accumulated sum. -/
theorem foldr_add_eq (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat),
      l.foldr (fun s acc => f s + acc) a = l.foldr (fun s acc => f s + acc) 0 + a := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x xs ih =>
    intro a
    simp only [List.foldr_cons]
    rw [ih a, ih 0, Nat.add_zero]
    omega

/-- **`k`-fold union bound.** A round folds `k` times. If each sub-round's containment failure
count is at most `E`, the round's total is at most `k·E`: a union bound over the sub-rounds.

This sums supplied natural-number bounds only. It does not establish their
validity after conditioning on earlier random challenges. -/
theorem fold_union (k E : Nat) (failures : Nat → Nat)
    (h : ∀ s, s < k → failures s ≤ E) :
    (List.range k).foldr (fun s acc => failures s + acc) 0 ≤ k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
    have hk : failures k ≤ E := h k (by omega)
    have hrest : (List.range k).foldr (fun s acc => failures s + acc) 0 ≤ k * E :=
      ih (fun s hs => h s (by omega))
    rw [foldr_add_eq failures (List.range k) (failures k), Nat.add_mul, Nat.one_mul]
    omega

/-- Regression: at rate 1/16, the Johnson error fraction 3/4 is outside
unique decoding. A containment theorem requiring `2e < d` cannot justify this
parameter point (RS length 256, dimension 16, distance 241). -/
theorem johnson_example_not_unique : ¬ (2 * 192 < (256 - 16 + 1 : Nat)) := by decide

end Field

end ZkFormal.Udr
