import ZkFormal.NearV3.Qv.Candidates.CombinedOverlay
import ZkFormal.NearV3.Qv.Candidates.CombinedWalkCells

namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air

/-- Overlay preservation also holds at a walk row whose requested mode is zero.
This covers the physical parser-to-first-walk wrap boundary. -/
theorem parser_row_preserved_or_zero {F : Type} [Lean.Grind.CommRing F]
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hw : ∀ next, (rowEnv tr t r pub).col walk next = 0 ∨
      (rowEnv tr t r pub).col ValueTable.len next = 0) (e : Expr) :
    (parserExpr e).eval tr t r pub = e.eval tr t r pub := by
  unfold Expr.eval
  rw [parserExpr_eval,parserEnv_eq]
  intro next
  rcases hw next with hw | hl
  · simp only [rowEnv,Lean.Grind.Semiring.natCast_one] at hw ⊢
    grind
  · simp only [rowEnv,Lean.Grind.Semiring.natCast_one] at hl ⊢
    grind

theorem parser_wrap_preserved {F : Type} [Lean.Grind.CommRing F]
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hw : tr.cell t r walk=0)
    (hl : tr.cell t 0 ValueTable.len=0)
    (hr : r+1=tr.height t) (e : Expr) :
    (parserExpr e).eval tr t r pub=e.eval tr t r pub := by
  apply parser_row_preserved_or_zero
  intro next
  cases next
  · exact Or.inl hw
  · right
    simpa [rowEnv,hr] using hl

end ZkFormal.NearV3.Qv.Candidates.CombinedTable

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Algebra

theorem first_main_mode_zero (v : MainValues) (K : Nat) (resolve : Resolve)
    (pos : Nat) (b : UInt8) :
    ((mainWalk v K resolve .delayed 0 v.delayed).row pos b).getD ValueTable.len 0=0 := by
  simp [ValueTable.len,mainWalk,Walk.mode]

/-- The actual first generated word supplies the zero-mode wrap premise. -/
theorem generated_parser_wrap (v : MainValues) (K : Nat) (resolve : Resolve)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t 0 c = Fp.ofNat
      (((mainWalk v K resolve .delayed 0 v.delayed).row 0 7).getD c 0))
    (hw : tr.cell t r CombinedTable.walk=0) (hr : r+1=tr.height t) (e : Expr) :
    (CombinedTable.parserExpr e).eval tr t r pub=e.eval tr t r pub := by
  apply CombinedTable.parser_wrap_preserved tr t r pub hw _ hr e
  rw [hc,first_main_mode_zero]
  rfl

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
