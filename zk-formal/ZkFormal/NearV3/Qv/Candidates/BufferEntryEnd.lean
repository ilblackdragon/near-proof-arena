import ZkFormal.NearV3.Qv.Candidates.BufferLocal
import ZkFormal.NearV3.Qv.Candidates.BufferEntryRows

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem bufferTrace_entry_end_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hb : 4+24*es.length ≤ 2^log) (i : Nat) (hi : i<es.length) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferTrace (F:=F) log vid tau users es) 0 (4+24*i+23) [] = 0 := by
  generalize hheight : 2^log = height at hb
  have hfirst : 4+24*i+23≠0 := by omega
  have hnfirst : 4+24*i+23+1≠0 := by omega
  have hvl : (4+24*i+23+1=4+24*es.length) ↔ i+1=es.length := by omega
  have hm : (4+24*i+23+1)%height =
      if height=4+24*i+23+1 then 0 else 4+24*i+23+1 := by
    split
    · rename_i h; rw [h,Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hC := bufferRowAt_entry vid tau users es i 23 hi (by decide)
  have hN := bufferRowAt_after_entry vid tau users es i hi
  by_cases hfinal : i+1=es.length <;> by_cases hphys : height=4+24*i+23+1
  all_goals try omega
  all_goals try
    have hF := congrArg (@Nat.cast F Lean.Grind.Semiring.natCast) hfinal
    simp only [Lean.Grind.Semiring.natCast_add,Lean.Grind.Semiring.natCast_one] at hF
  all_goals
    simp (config := { maxSteps := 500000 }) [ValueTable.table,Table.allConstraints,Table.bitConstraints,ValueTable.constraints,
      ValueTable.interactions,ValueTable.modes,ValueTable.phases,ValueTable.selectors,
      ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,ValueTable.entryEnd,
      ValueTable.mode,ValueTable.counterBytes,ValueTable.same,send,recv,
      Expr.eval,Expr.evalWith,rowEnv,Trace.height,bufferTrace,c,n,k,ZkFormal.Near.Dsl.bool,
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
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,hheight,hm,hC,hN,bufferRowAt_zero,hfirst,hnfirst,hfinal,hphys,hvl
       ] <;>
    (repeat' first | split | constructor)
  all_goals try simp_all [Lean.Grind.Semiring.natCast_zero,
      Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_add,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero]
  all_goals grind

end ZkFormal.NearV3.Qv.Candidates.ValueGen
