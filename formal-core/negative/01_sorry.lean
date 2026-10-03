-- EXPECT: SORRY_FOUND  (axiom `sorryAx` in the transitive axiom set)
import Toy.Artifacts
namespace Candidate
theorem certificate : ToyJudge.Expected := sorry
end Candidate
