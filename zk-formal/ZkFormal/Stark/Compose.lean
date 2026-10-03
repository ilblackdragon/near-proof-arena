import ZkFormal.Stark.Statements

/-!
# ZkFormal.Stark.Compose — L4 deliverables from the `Statements`
-/

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Air

theorem compileBound_np {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) :
    compileBound (Iop.verifier F K A prm) (schedBound A prm) (oracleBound prm) prm.maxLogLde =
      NVu A prm := rfl

/-- **Query-count bound of the deployed verifier** (`NVu`, for `romSound_of_potential`). -/
theorem verifier_queryBound (hQ1 : CompileQueryBoundStmt) (hQ2 : NpBoundsStmt)
    {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    (A : Air) (prm : Params) (pub cb pb : Bytes) :
    OracleComp.QueryBound unitWeight ((verifier F K A prm).tree pub cb pb) (NVu A prm) := by
  rw [verifier_eq_compile F K A prm pub cb pb, ← compileBound_np (F := F) (K := K) A prm]
  exact hQ1 F K _ _ _ _ (hQ2 F K A prm) pub cb pb

end ZkFormal.Stark
