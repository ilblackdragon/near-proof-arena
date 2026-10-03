/-
Stand-in for formal-core's `ArenaCore.Admission` (tests only).
Shape mirrors the real admission statement: one conjunct per formal gate.
-/
namespace ArenaStandIn

structure ChallengeParams where
  protocolVersion : Nat
  chainId : String

structure ArtifactDesc where
  verifierDigest : String
  paramsDigest : String

/-- B(c,aux) → ∃w, NearRelation(c,w) (toy). -/
def SemanticSoundness (_p : ChallengeParams) (_a : ArtifactDesc) : Prop :=
  ∀ n : Nat, n + 0 = n

/-- NearRelation(c,w) → ∃aux, B(c,aux) (toy). -/
def SemanticCompleteness (p : ChallengeParams) (_a : ArtifactDesc) : Prop :=
  p.protocolVersion * 2 = p.protocolVersion + p.protocolVersion

/-- Game-based bound (toy). -/
def CryptoSoundness (_p : ChallengeParams) (a : ArtifactDesc) : Prop :=
  0 ≤ a.verifierDigest.length

/-- Production verifier ↔ formal verifier (toy). -/
def ImplConnection (_p : ChallengeParams) (a : ArtifactDesc) : Prop :=
  a.paramsDigest = a.paramsDigest

def AdmissionStatement (p : ChallengeParams) (a : ArtifactDesc) : Prop :=
  SemanticSoundness p a ∧ SemanticCompleteness p a ∧ CryptoSoundness p a ∧ ImplConnection p a

namespace Assumptions
/-- A named (judge-pinned) assumption that is NOT approved by the test challenge. -/
axiom toyCollisionResistance : ∀ {α : Type} (x y : α), x = y → y = x
end Assumptions

end ArenaStandIn
