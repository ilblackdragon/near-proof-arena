import ZkFormal.Algebra.PolyLemmas
import ZkFormal.Algebra.PolyRoots
import ZkFormal.Algebra.RSProofs
import ZkFormal.Algebra.Compose

/-!
# ZkFormal.Algebra.Main — the L1 statements as unconditional theorems

Closes the `…Stmt` obligations of `Algebra.Statements` by composing the
proof modules, and gives `RS.code'`, the Reed–Solomon `LinCode` of distance
`n − D + 1` with no hypotheses.
-/

namespace ZkFormal.Algebra

open Poly PolyRoots

theorem Poly.card_roots_le : CardRootsLeStmt :=
  cardRootsLe_of polyEval polyDeg quotFacts isZeroEval

theorem Poly.eq_zero_of_roots : EqZeroOfRootsStmt :=
  eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval

theorem Poly.lagrange_spec : LagrangeStmt := lagrange_of polyEval polyDeg

theorem RS.lin : RSLinStmt := rsLin_of polyEval polyDeg

/-- **`RS.sep`**: Reed–Solomon codes have distance `n − D + 1`. -/
theorem RS.sep : RSSepStmt := rsSep_of polyEval polyDeg Poly.eq_zero_of_roots isZeroEval

/-- The Reed–Solomon code `RS[n, D]` at distinct points, as a `LinCode` of
distance `n − D + 1`. -/
def RS.code' {K : Type} [Lean.Grind.Field K] [DecidableEq K] (n D : Nat) (pts : Nat → K)
    (hpts : RS.PtsInj n pts) : LineLemma.LinCode K n (n - D + 1) :=
  RS.code RS.lin RS.sep n D pts hpts

end ZkFormal.Algebra
