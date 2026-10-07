import ZkFormal.NearV3.Qv.Candidates.CombinedPrefixLocal

namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem parser_bits (tr : Trace F) (t r : Nat) (pub : List F)
    (hz : ∀ x, 37≤x → tr.cell t r x=0)
    (hb : ∀ e ∈ ValueTable.table.bitConstraints,e.eval tr t r pub=0) :
    ∀ e ∈ table.bitConstraints,e.eval tr t r pub=0 := by
  simp [Table.bitConstraints,ValueTable.table,ValueTable.interactions,table,interactions,
    send,recv,Dsl.bool,c,k,sub,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,
    walk,wf,wl,present,groupByte,countRead,hz,
    Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.zero_mul,
    Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.mul_one,
    Lean.Grind.AddCommGroup.neg_zero,Lean.Grind.AddCommMonoid.zero_add,Lean.Grind.Semiring.add_zero] at hb ⊢
  exact hb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem parser_row_all_constraints (tr : Trace F) (t r : Nat) (pub : List F)
    (hz : ∀ x, 37≤x → tr.cell t r x=0)
    (hr : r≠0)
    (hn : r+1=tr.height t ∨ tr.cell t ((r+1)%tr.height t) walk=0)
    (hoverlay : tr.cell t ((r+1)%tr.height t) walk=0 ∨
      tr.cell t ((r+1)%tr.height t) ValueTable.len=0)
    (hbase : ∀ e ∈ ValueTable.table.allConstraints,e.eval tr t r pub=0) :
    ∀ e ∈ table.allConstraints,e.eval tr t r pub=0 := by
  have hw : tr.cell t r walk=0 := hz _ (by decide)
  have hp : ∀ e ∈ ValueTable.constraints,(parserExpr e).eval tr t r pub=0 := by
    intro e he
    rw [parser_row_preserved_or_zero tr t r pub (fun next => by
      cases next
      · exact Or.inl hw
      · exact hoverlay) e]
    exact hbase e (List.mem_append_left _ he)
  have hrestart : (mul3 .isTransition (Dsl.not (c walk)) (n walk)).eval tr t r pub=0 := by
    rcases hn with hn | hn
    · simp [mul3,Expr.eval,Expr.evalWith,rowEnv,hn,Lean.Grind.Semiring.zero_mul]
    · simp [mul3,n,Expr.eval,Expr.evalWith,rowEnv,hn,Lean.Grind.Semiring.mul_zero]
  have hc : ∀ e ∈ constraints,e.eval tr t r pub=0 := by
    simp only [constraints,List.forall_mem_append,List.forall_mem_map]
    refine ⟨⟨⟨⟨⟨hp,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
    all_goals
      simp [Dsl.bool,c,n,k,sub,Dsl.not,eqG,mul3,inside,more,advanceMain,leaveMain,advanceImplicit,
        Expr.eval,Expr.evalWith,rowEnv,walk,lo,hi,wf,wl,wend,absent,groupByte,countRead,main,lastMain,present,
        hz,hr,Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_zero,
        Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.mul_one,
        Lean.Grind.Semiring.one_mul,Lean.Grind.AddCommGroup.neg_zero,
        Lean.Grind.AddCommMonoid.zero_add,Lean.Grind.Semiring.add_zero]
    rcases hn with hn | hn
    · simp [hn,Lean.Grind.Semiring.zero_mul]
    · change tr.cell t ((r+1)%tr.height t) 37=0 at hn
      simp [hn,Lean.Grind.Semiring.mul_zero]
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hc e he
  · exact parser_bits tr t r pub hz (fun e he => hbase e (List.mem_append_right _ he)) e he

end ZkFormal.NearV3.Qv.Candidates.CombinedTable
