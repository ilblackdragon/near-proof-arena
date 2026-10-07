import ZkFormal.NearV3.Qv.Candidates.CombinedOverlay
import ZkFormal.Near.Extract.BusCount

namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

theorem parser_constraint_mem {e : Expr} (he : e ∈ ValueTable.constraints) :
    parserExpr e ∈ constraints := by
  simp only [constraints,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨e,he,rfl⟩)))))

theorem parser_constraints_of_combined {F : Type} [Lean.Grind.CommRing F]
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hw : ∀ next, (rowEnv tr t r pub).col walk next = 0)
    (hc : ∀ e ∈ constraints, e.eval tr t r pub = 0) :
    ∀ e ∈ ValueTable.constraints, e.eval tr t r pub = 0 := by
  intro e he
  rw [← parser_row_preserved tr t r pub hw e]
  exact hc _ (parser_constraint_mem he)

theorem parser_flags_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hw : tr.cell t r walk = 0)
    (hc : ∀ e ∈ constraints, e.eval tr t r pub = 0) :
    ∀ x ∈ [wf,wl,wend,groupByte,countRead,main,lastMain,present], tr.cell t r x = 0 := by
  intro x hx
  have hm : Expr.mul (Dsl.c x) (Dsl.not (Dsl.c walk)) ∈ constraints := by
    simp only [constraints,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨x,hx,rfl⟩))))
  have he := hc _ hm
  simp only [Expr.eval,Expr.evalWith,Dsl.c,Dsl.not,Dsl.sub,Dsl.k,rowEnv,
    Lean.Grind.Semiring.natCast_one] at he
  simp [hw] at he
  grind

/-- A parser row has precisely the original parser traffic, with no added read
messages. The hypotheses are the extra gates; local extraction can derive them. -/
theorem parser_row_traffic (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hw : tr.cell t r walk = 0)
    (hf : tr.cell t r wf = 0) (hl : tr.cell t r wl = 0)
    (hp : tr.cell t r present = 0)
    (hg : tr.cell t r groupByte = 0) (hc : tr.cell t r countRead = 0)
    (bus : Nat) (side : Bool) :
    rowTraffic interactions tr t r pub bus side =
      rowTraffic ValueTable.interactions tr t r pub bus side := by
  have hz : (0 : Fp) ≠ 1 := by decide
  have hfct (x : Fp) : x * (1 + -0) = x := by grind
  simp [rowTraffic,interactions,ValueTable.interactions,Dsl.send,Dsl.recv,
    Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
    Dsl.c,Dsl.not,Dsl.sub,Dsl.k,hfct,hz,hw,hf,hl,hp,hg,hc,
    Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_zero]

theorem parser_traffic_of_combined (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hw : tr.cell t r walk = 0)
    (hc : ∀ e ∈ constraints, e.eval tr t r pub = 0)
    (bus : Nat) (side : Bool) :
    rowTraffic interactions tr t r pub bus side =
      rowTraffic ValueTable.interactions tr t r pub bus side := by
  have hz := parser_flags_zero tr t r pub hw hc
  exact parser_row_traffic tr t r pub hw (hz wf (by simp)) (hz wl (by simp))
    (hz present (by simp)) (hz groupByte (by simp)) (hz countRead (by simp)) bus side

end ZkFormal.NearV3.Qv.Candidates.CombinedTable
