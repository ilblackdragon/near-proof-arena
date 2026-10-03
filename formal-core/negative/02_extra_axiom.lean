-- EXPECT: FORBIDDEN_AXIOM / UNAPPROVED_ASSUMPTION
-- The candidate "assumes" its own (false!) injectivity of SHA-256 as an axiom.
import Toy.Certificate
namespace Candidate
open ArenaCore
axiom sha256_injective : ∀ x y : Bytes, sha256 x = sha256 y → x = y
theorem certificate : ToyJudge.Expected := by
  have := sha256_injective  -- the axiom is used, so it is in the axiom set
  exact Toy.certificate
end Candidate
