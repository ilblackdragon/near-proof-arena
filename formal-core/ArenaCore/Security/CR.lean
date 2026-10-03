import ArenaCore.Assumptions
import ArenaCore.Verifier

/-!
# ArenaCore.Security.CR — standard-model soundness by explicit reduction to
SHA-256 collisions

A `CRReduction` is an *NPAI bytecode program* (the same VM as approved
verifiers) together with a fuel bound.  Making the reduction a fuel-bounded
program — rather than an arbitrary Lean function — is what keeps the
statement honest: an arbitrary (total, computable) Lean function could
brute-force a collision, making any verifier "secure"; a program with fuel
`≤ maxReductionFuel` cannot, so the composed finder's cost is
`cost(A) + fuel`.

Pointwise soundness (`CRReduction.Sound`): on *every* input on which the
verifier accepts a claim outside the language, the reduction outputs a
SHA-256 collision.  Since this quantifies over all `(claim, proof)` pairs,
it covers every adversary, adaptive or not, with any auxiliary oracles it
may simulate (e.g. honest proofs for statements whose witnesses it knows).

`CRSecure` is the probabilistic statement that appears in the admission
theorem: the judge-supplied hypothesis is `Sha256CollisionResistant` for the
explicitly composed finder.
-/

namespace ArenaCore.Security

open Assumptions

/-- An explicit reduction: bytecode program + fuel bound. -/
structure CRReduction where
  prog : Interp.Program
  fuel : Nat

/-- A bad acceptance: accepted claim outside the language `L`. -/
def BadAccept (L : Bytes → Prop) (v : Verifier) (pub : Bytes) (o : Bytes × Bytes) : Prop :=
  v pub o.1 o.2 = true ∧ ¬ L o.1

namespace CRReduction

/-- Run the reduction on `(pub, claim, proof)`; outputs of an accepting run,
`([], [])` otherwise (never a collision). -/
def apply (r : CRReduction) (pub : Bytes) (o : Bytes × Bytes) : Bytes × Bytes :=
  (Interp.runOut r.prog { pub, claim := o.1, proof := o.2 } r.fuel).getD ([], [])

/-- The composed collision finder `r ∘ A`. -/
def finder (r : CRReduction) (pub : Bytes) (A : CoinAdversary (Bytes × Bytes)) :
    CoinAdversary (Bytes × Bytes) :=
  A.map (r.apply pub)

/-- Pointwise soundness of the reduction. -/
def Sound (r : CRReduction) (L : Bytes → Prop) (v : Verifier) (pub : Bytes) : Prop :=
  ∀ cb pb, BadAccept L v pub (cb, pb) → IsSha256Collision (r.apply pub (cb, pb))

end CRReduction

/-- Standard-model cryptographic soundness relative to `sha256_cr`: for every
randomized adversary and every bound, if the explicit finder built from it
finds collisions with probability ≤ `num/den` (judge-supplied governed
hypothesis), then the adversary produces a bad acceptance with probability ≤
`num/den`. -/
def CRSecure (r : CRReduction) (L : Bytes → Prop) (v : Verifier) (pub : Bytes) : Prop :=
  ∀ (A : CoinAdversary (Bytes × Bytes)) (num den : Nat),
    Sha256CollisionResistant (r.finder pub A) num den →
      A.PrLE (BadAccept L v pub) num den

/-- Pointwise soundness implies the probabilistic statement (tightness 1). -/
theorem CRReduction.secure_of_sound {r : CRReduction} {L : Bytes → Prop} {v : Verifier}
    {pub : Bytes} (h : r.Sound L v pub) : CRSecure r L v pub := by
  intro A num den hcr
  unfold Sha256CollisionResistant CoinAdversary.PrLE at hcr
  unfold CoinAdversary.PrLE
  refine PrLE.mono (fun t hbad => ?_) hcr
  simp only [finder, CoinAdversary.output_map]
  exact h _ _ hbad

/-- Enlarging the "good" language `L ⊆ L'` shrinks the bad event. -/
theorem BadAccept.mono {L L' : Bytes → Prop} (hLL' : ∀ cb, L cb → L' cb) {v : Verifier}
    {pub : Bytes} {o : Bytes × Bytes} : BadAccept L' v pub o → BadAccept L v pub o :=
  fun ⟨hacc, hn⟩ => ⟨hacc, fun hL => hn (hLL' _ hL)⟩

theorem CRSecure.mono {r : CRReduction} {L L' : Bytes → Prop} (hLL' : ∀ cb, L cb → L' cb)
    {v : Verifier} {pub : Bytes} (h : CRSecure r L v pub) : CRSecure r L' v pub :=
  fun A num den hcr => PrLE.mono (fun _ hb => BadAccept.mono hLL' hb) (h A num den hcr)

end ArenaCore.Security
