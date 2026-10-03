-- EXPECT: THEOREM_TYPE_MISMATCH
-- The candidate certifies a *native* verifier model (trusted route) while the
-- judge froze the interpreter route for the built artifact.  Different
-- `ArtifactDescription` → different type.
import Toy.Certificate
namespace Candidate
open ArenaCore
def nativeArtifacts : ArtifactDescription :=
  { publicDigest := ToyJudge.publicDigest,
    impl := .nativeTrusted ToyJudge.verifierDigest "rustc-1.x" Toy.toyVerifier }
theorem certificate : AdmissionStatement Toy.toyParams nativeArtifacts :=
  ⟨Toy.toyPub, Toy.toyVerifier, by decide +kernel, rfl, Toy.toyBackend, Toy.toyObligations⟩
end Candidate
