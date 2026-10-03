import ZkFormal.Algebra.Poly

/-!
# ZkFormal.Algebra.RS — Reed–Solomon codes (definitions)

`RS.Mem n D pts u`: the word `u` (positions `[0, n)`) is the evaluation
table of a polynomial of degree `< D` at the points `pts 0, …, pts (n-1)`.
With distinct points it is a linear code of minimum distance `n − D + 1`
(`Algebra.Compose.RS.code`, from `RSLinStmt` and `RSSepStmt`).
-/

namespace ZkFormal.Algebra

open Lean.Grind

namespace RS

variable {K : Type} [Field K]

/-- `u` is a Reed–Solomon codeword: evaluations of a degree-`< D` polynomial. -/
def Mem (n D : Nat) (pts : Nat → K) (u : Nat → K) : Prop :=
  ∃ f : Poly K, f.DegLt D ∧ ∀ i, i < n → u i = f.eval (pts i)

/-- The evaluation points are distinct on `[0, n)`. -/
def PtsInj (n : Nat) (pts : Nat → K) : Prop :=
  ∀ i j, i < n → j < n → pts i = pts j → i = j

end RS
end ZkFormal.Algebra
