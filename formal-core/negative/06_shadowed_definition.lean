-- EXPECT: SHADOWED_DEFINITION / THEOREM_TYPE_MISMATCH
-- The candidate declares its own `AdmissionStatement` (trivially true) and
-- states the certificate with the *same surface syntax* as the judge type.
-- Name resolution picks `Candidate.AdmissionStatement`.
import Toy.Artifacts
namespace Candidate
open ArenaCore
def AdmissionStatement (_ : ChallengeParams) (_ : ArtifactDescription) : Prop := True
theorem certificate : AdmissionStatement Toy.toyParams ToyJudge.artifacts := trivial
end Candidate
