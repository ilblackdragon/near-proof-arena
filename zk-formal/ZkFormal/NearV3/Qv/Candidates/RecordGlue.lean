import ZkFormal.NearV3.Qv.Candidates.ValueTable

/-! Local transfer at record boundaries. These lemmas permit concatenating
independently rendered queue values without imposing equality between unrelated
records' next-row cells. They do not supply record capacity or bus balance. -/
namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

def recordEnv (cur nxt : Nat → F) (first last transition : F) : Env F where
  ofNat := fun n => @Nat.cast F Lean.Grind.Semiring.natCast n
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  col := fun c nx => if nx then nxt c else cur c
  pub := fun _ => 0
  isFirst := first
  isLast := last
  isTransition := transition

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem terminal_record_transfer (cur oldNext newNext : Nat → F)
    (oldFirst oldLast oldTransition first last transition : F)
    (ha : cur ValueTable.act = 1) (hl : cur ValueTable.vl = 1)
    (hc : cur ValueTable.cont = 0)
    (hf : first * (1 + -cur ValueTable.vf) = 0)
    (hn : newNext ValueTable.act * (1 + -newNext ValueTable.vf) = 0)
    (hv : ∀ e ∈ ValueTable.table.allConstraints,
      e.evalWith (recordEnv cur oldNext oldFirst oldLast oldTransition) = 0) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.evalWith (recordEnv cur newNext first last transition) = 0 := by
  simp [ValueTable.table,Table.allConstraints,Table.bitConstraints,
    ValueTable.constraints,ValueTable.interactions,ValueTable.modes,ValueTable.phases,
    ValueTable.selectors,ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,
    ValueTable.entryEnd,ValueTable.mode,ValueTable.counterBytes,ValueTable.same,
    send,recv,Expr.evalWith,recordEnv,c,n,k,ZkFormal.Near.Dsl.bool,
    sub,sum,smul,mul3,eqG,ZkFormal.Near.Dsl.not,List.range_succ,Function.comp_def,
    ha,hl,hc,hf,hn,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
    Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
    Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero] at hv ⊢
  grind only

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem interior_record_transfer (cur nxt : Nat → F) (oldFirst first : F)
    (hf : first * (cur ValueTable.act + -cur ValueTable.vf) = 0)
    (hv : ∀ e ∈ ValueTable.table.allConstraints,
      e.evalWith (recordEnv cur nxt oldFirst 0 1) = 0) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.evalWith (recordEnv cur nxt first 0 1) = 0 := by
  simp [ValueTable.table,Table.allConstraints,Table.bitConstraints,
    ValueTable.constraints,ValueTable.interactions,ValueTable.modes,ValueTable.phases,
    ValueTable.selectors,ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,
    ValueTable.entryEnd,ValueTable.mode,ValueTable.counterBytes,ValueTable.same,
    send,recv,Expr.evalWith,recordEnv,c,n,k,ZkFormal.Near.Dsl.bool,
    sub,sum,smul,mul3,eqG,ZkFormal.Near.Dsl.not,List.range_succ,Function.comp_def,
    hf,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
    Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
    Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero] at hv ⊢
  grind only

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem padding_record_local (nxt : Nat → F) (first last transition : F)
    (hn : transition * nxt ValueTable.act = 0) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.evalWith (recordEnv (fun _ => 0) nxt first last transition) = 0 := by
  simp [ValueTable.table,Table.allConstraints,Table.bitConstraints,
    ValueTable.constraints,ValueTable.interactions,ValueTable.modes,ValueTable.phases,
    ValueTable.selectors,ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,
    ValueTable.entryEnd,ValueTable.mode,ValueTable.counterBytes,ValueTable.same,
    send,recv,Expr.evalWith,recordEnv,c,n,k,ZkFormal.Near.Dsl.bool,
    sub,sum,smul,mul3,eqG,ZkFormal.Near.Dsl.not,List.range_succ,Function.comp_def,
    hn,
    Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
    Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
    Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero]


end ZkFormal.NearV3.Qv.Candidates.ValueGen
