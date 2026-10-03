import ZkFormal.Algebra.Statements

/-!
# ZkFormal.Algebra.Compose — downstream objects from the L1 statements

`RS.code` packages a Reed–Solomon code as a `LineLemma.LinCode` of distance
`n − D + 1`, given the proved statements `RSLinStmt` and `RSSepStmt`.  Once
those are theorems (`Algebra.RSProofs`), `RS.code'` needs no hypotheses.
-/

namespace ZkFormal.Algebra

open Lean.Grind

/-- Reed–Solomon code `RS[n, D]` at distinct points, distance `n − D + 1`. -/
def RS.code (hlin : RSLinStmt) (hsep : RSSepStmt) {K : Type} [Field K] [DecidableEq K]
    (n D : Nat) (pts : Nat → K) (hpts : RS.PtsInj n pts) : LineLemma.LinCode K n (n - D + 1) where
  mem := RS.Mem n D pts
  lin u v a b hu hv := hlin K n D pts u v a b hu hv
  sep u v hu hv hd i hi := hsep K n D pts hpts u v hu hv hd i hi

end ZkFormal.Algebra
