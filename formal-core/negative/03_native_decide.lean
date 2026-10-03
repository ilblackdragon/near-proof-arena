-- EXPECT: NATIVE_EVAL_FOUND  (Lean v4.34 emits auxiliary axioms `<decl>._native.native_decide.ax_*`;
-- older versions use `Lean.ofReduceBool`)
-- The digest bindings are "proved" by compiled evaluation instead of the kernel.
import Toy.Certificate
namespace Candidate
open ArenaCore Toy
theorem certificate : ToyJudge.Expected :=
  ⟨toyPub, toyVerifier, by native_decide,
    ⟨verifierCode, by native_decide, rfl⟩, toyBackend, toyObligations⟩
end Candidate
