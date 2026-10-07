import ZkFormal.NearV3.Qv.Candidates.EmptyPadded

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem emptyPaddedTrace_end_local (log vid tau users : Nat) (index : Bytes)
    (hb : 16≤2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (emptyPaddedTrace (F:=F) log vid tau users index) 0 15 [] = 0 := by
  generalize hheight : 2^log = height at hb
  have hm : 16%height=if height=16 then 0 else 16 := by
    split
    · rename_i h; simp [h]
    · rw [Nat.mod_eq_of_lt (by omega)]
  by_cases hl : height=16
  all_goals
    simp (config := { maxSteps := 500000 }) [ValueTable.table,Table.allConstraints,Table.bitConstraints,ValueTable.constraints,
      ValueTable.interactions,ValueTable.modes,ValueTable.phases,ValueTable.selectors,
      ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,ValueTable.entryEnd,
      ValueTable.mode,ValueTable.counterBytes,ValueTable.same,send,recv,
      Expr.eval,Expr.evalWith,rowEnv,Trace.height,emptyPaddedTrace,c,n,k,ZkFormal.Near.Dsl.bool,
      sub,sum,smul,mul3,eqG,ZkFormal.Near.Dsl.not,
      ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.vz,ValueTable.gb,
      ValueTable.cont,ValueTable.vid,ValueTable.len,ValueTable.pos,ValueTable.byte,ValueTable.users,
      ValueTable.tau,ValueTable.entry,ValueTable.count,ValueTable.mEmpty,ValueTable.mBuffer,
      ValueTable.mRaw,ValueTable.header,ValueTable.shard,ValueTable.firstIndex,ValueTable.nextIndex,
      ValueTable.sel,ValueTable.reg,List.range_succ,Function.comp_def,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,hheight,hm,hl
       ] <;> grind

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem emptyPaddedTrace_padding_local (log vid tau users : Nat) (index : Bytes)
    {r : Nat} (hr : r<2^log) (hp : 16≤r) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (emptyPaddedTrace (F:=F) log vid tau users index) 0 r [] = 0 := by
  generalize hheight : 2^log = height at hr
  have h0 : r≠0 := by omega
  have hp0 : ¬r<16 := by omega
  have hnp : ¬r+1<16 := by omega
  by_cases hl : height=r+1
  all_goals
    have hm : (r+1)%height=if height=r+1 then 0 else r+1 := by
      split
      · rename_i h; rw [h,Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  all_goals
    simp (config := { maxSteps := 500000 }) [ValueTable.table,Table.allConstraints,Table.bitConstraints,ValueTable.constraints,
      ValueTable.interactions,ValueTable.modes,ValueTable.phases,ValueTable.selectors,
      ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,ValueTable.entryEnd,
      ValueTable.mode,ValueTable.counterBytes,ValueTable.same,send,recv,
      Expr.eval,Expr.evalWith,rowEnv,Trace.height,emptyPaddedTrace,c,n,k,ZkFormal.Near.Dsl.bool,
      sub,sum,smul,mul3,eqG,ZkFormal.Near.Dsl.not,
      ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.vz,ValueTable.gb,
      ValueTable.cont,ValueTable.vid,ValueTable.len,ValueTable.pos,ValueTable.byte,ValueTable.users,
      ValueTable.tau,ValueTable.entry,ValueTable.count,ValueTable.mEmpty,ValueTable.mBuffer,
      ValueTable.mRaw,ValueTable.header,ValueTable.shard,ValueTable.firstIndex,ValueTable.nextIndex,
      ValueTable.sel,ValueTable.reg,List.range_succ,Function.comp_def,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,hheight,hm,hl,h0,hp0,hnp
       ] <;> grind

end ZkFormal.NearV3.Qv.Candidates.ValueGen
