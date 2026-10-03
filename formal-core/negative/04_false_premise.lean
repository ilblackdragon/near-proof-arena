-- EXPECT: THEOREM_TYPE_MISMATCH
-- The candidate adds its own hypothesis: "SHA-256 has no collisions".  This
-- is FALSE (pigeonhole) and would make every soundness claim vacuous.  The
-- constant's type is a Π-type, not `ToyJudge.Expected`.
import Toy.Artifacts
namespace Candidate
open ArenaCore
theorem certificate (_hNoCollisions : ∀ x y : Bytes, sha256 x = sha256 y → x = y) :
    ToyJudge.Expected := by
  sorry -- a real attempt would exploit the false premise; the type alone already fails
end Candidate
