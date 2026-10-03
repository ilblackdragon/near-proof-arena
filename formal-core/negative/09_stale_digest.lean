-- EXPECT: ARTIFACT_BINDING_FAILED (elaboration error)
-- The judge rebuilt the verifier and froze a *new* bytecode digest (here the
-- last byte differs); the candidate's proof is about the old bytecode.  The
-- kernel evaluation of `sha256 verifierCode = <new digest>` fails.
import Toy.Certificate
namespace StaleJudge
open ArenaCore
def newDigest : Digest :=
  [0xe7, 0xea, 0x8a, 0x49, 0xfd, 0xd4, 0x5c, 0xf3, 0xb7, 0x89, 0xff, 0x44, 0x2c, 0x2b, 0xad, 0xbd,
   0xb9, 0x8e, 0xad, 0xe3, 0xad, 0xbb, 0x9c, 0x35, 0x9d, 0x24, 0x23, 0xad, 0xa5, 0x21, 0xb0, 0x10]
def Expected : Prop :=
  AdmissionStatement Toy.toyParams { publicDigest := ToyJudge.publicDigest, impl := .interp newDigest }
end StaleJudge
namespace Candidate
open ArenaCore Toy
theorem certificate : StaleJudge.Expected :=
  ⟨toyPub, toyVerifier, by decide +kernel,
    ⟨verifierCode, by decide +kernel, rfl⟩, toyBackend, toyObligations⟩
end Candidate
