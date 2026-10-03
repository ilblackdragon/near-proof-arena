-- EXPECT: PASS  (positive control: the real toy certificate)
import Toy.Certificate
namespace Candidate
theorem certificate : ToyJudge.Expected := Toy.certificate
end Candidate
