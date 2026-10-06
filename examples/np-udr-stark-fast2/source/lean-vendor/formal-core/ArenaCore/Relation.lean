import ArenaCore.Bytes

/-!
# ArenaCore.Relation — the challenge relation (supplied by the spec lane)

`ChallengeSpec` packages everything the *challenge* (never the candidate)
fixes about the statement being proved:

* `Claim`, `Witness`, and the relation `Rel : Claim → Witness → Prop`
  (for NEAR this is `NearRelation`, defined in `spec/lean`);
* the input domain `Domain : Claim → Prop`: the claims an honest prover is
  required to handle (completeness only — soundness is never restricted to
  the domain, an adversary may present any bytes);
* the canonical claim codec `decodeClaim`/`encodeClaim` (`claim.bin`
  encoding, e.g. `near-arena-claim-v1`), with the round-trip law.

The spec lane instantiates this structure; candidates only ever see it as a
parameter inside the judge-constructed theorem type.
-/

namespace ArenaCore

structure ChallengeSpec where
  /-- Decoded claim (public statement). -/
  Claim : Type
  /-- Witness (private data the honest prover uses). -/
  Witness : Type
  /-- The challenge relation (e.g. `NearRelation`). -/
  Rel : Claim → Witness → Prop
  /-- Input domain fixed by the challenge: the claims whose honest proofs must
  be accepted. Used only as a precondition of completeness. -/
  Domain : Claim → Prop
  /-- Canonical claim decoding from `claim.bin`. -/
  decodeClaim : Bytes → Option Claim
  /-- Canonical claim encoding (what the honest prover emits as `claim.bin`). -/
  encodeClaim : Claim → Bytes
  /-- The codec round-trips. -/
  decode_encode : ∀ c, decodeClaim (encodeClaim c) = some c

namespace ChallengeSpec

/-- Claim bytes that decode to a *true* claim (the language of the relation). -/
def InLang (S : ChallengeSpec) (cb : Bytes) : Prop :=
  ∃ c, S.decodeClaim cb = some c ∧ ∃ w, S.Rel c w

end ChallengeSpec

end ArenaCore
