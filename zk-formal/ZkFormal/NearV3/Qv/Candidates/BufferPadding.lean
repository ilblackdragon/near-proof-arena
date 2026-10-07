import ZkFormal.NearV3.Qv.Candidates.BufferLocal

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem bufferTrace_padding_local (log vid tau users : Nat) (es : List ByteBuffer)
    {r : Nat} (hr : r<2^log) (hp : 4+24*es.length ≤ r) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferTrace (F:=F) log vid tau users es) 0 r [] = 0 := by
  generalize hheight : 2^log = height at hr
  have h0 : r≠0 := by omega
  have h4 : ¬r<4 := by omega
  have hp0 : ¬r<4+24*es.length := by omega
  have hn4 : ¬r+1<4 := by omega
  have hnp : ¬r+1<4+24*es.length := by omega
  by_cases hl : height=r+1
  all_goals
    have hm : (r+1)%height = if height=r+1 then 0 else r+1 := by
      split
      · rename_i h; rw [h,Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  all_goals
    simp (config := { maxSteps := 500000 }) [ValueTable.table,Table.allConstraints,Table.bitConstraints,ValueTable.constraints,
      ValueTable.interactions,ValueTable.modes,ValueTable.phases,ValueTable.selectors,
      ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,ValueTable.entryEnd,
      ValueTable.mode,ValueTable.counterBytes,ValueTable.same,send,recv,
      Expr.eval,Expr.evalWith,rowEnv,Trace.height,bufferTrace,bufferRowAt,c,n,k,ZkFormal.Near.Dsl.bool,
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
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,hheight,hm,hl,h0,h4,hp0,hn4,hnp
       ] <;> grind

end ZkFormal.NearV3.Qv.Candidates.ValueGen
