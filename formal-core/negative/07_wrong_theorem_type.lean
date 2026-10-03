-- EXPECT: THEOREM_TYPE_MISMATCH
-- A true, sorry-free theorem — but not the admission statement (here: only
-- the public-artifact binding).
import Toy.Certificate
namespace Candidate
open ArenaCore
theorem certificate : ∃ pub : Bytes, sha256 pub = ToyJudge.publicDigest :=
  ⟨Toy.toyPub, by decide +kernel⟩
end Candidate
