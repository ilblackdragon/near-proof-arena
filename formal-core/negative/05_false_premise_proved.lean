-- EXPECT: THEOREM_TYPE_MISMATCH
-- Same as 04 but sorry-free: under the premise `False`-like assumption
-- everything is provable.  Elaborates fine, axioms are clean — only the
-- type check against the judge-constructed type rejects it.
import Toy.Artifacts
namespace Candidate
open ArenaCore
theorem certificate (_h : ∀ x y : Bytes, sha256 x = sha256 y → x = y) (hne : (0 : Nat) = 1) :
    ToyJudge.Expected := absurd hne (by decide)
end Candidate
