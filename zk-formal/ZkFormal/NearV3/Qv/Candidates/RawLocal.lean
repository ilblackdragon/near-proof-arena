import ZkFormal.NearV3.Qv.Candidates.EmptyRender

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

def rawTrace (log vid tau users : Nat) (bytes : Bytes) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      (if r<bytes.length ∨ (bytes.length=0 ∧ r=0) then
        (row ⟨vid,tau,users,2,bytes.length,0⟩ r (bytes.getD r 0).toNat 4 0 0 []).getD c 0
       else 0) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem rawTrace_local (log vid tau users : Nat) (bytes : Bytes)
    (hb : bytes.length ≤ 2^log) {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (rawTrace (F:=F) log vid tau users bytes) 0 r [] = 0 := by
  generalize hheight : 2^log = height at hb hr
  have hh : 0<height := by rw [← hheight]; exact Nat.two_pow_pos log
  by_cases hz : bytes.length=0 <;>
    by_cases h0 : r=0 <;>
    by_cases hl : r+1=height <;>
    by_cases ha : r<bytes.length <;>
    by_cases he : r+1=bytes.length
  all_goals try omega
  all_goals
    have hm : (r+1)%height = if r+1=height then 0 else r+1 := by
      split
      · rename_i h; rw [h,Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  all_goals try subst r
  all_goals try (have hlast := Eq.symm hl; clear hl)
  all_goals try (have hlen := Eq.symm he; clear he)
  all_goals
    simp_all (config := { maxSteps := 500000 }) [ValueTable.table,Table.allConstraints,Table.bitConstraints,ValueTable.constraints,
      ValueTable.interactions,ValueTable.modes,ValueTable.phases,ValueTable.selectors,
      ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,ValueTable.entryEnd,
      ValueTable.mode,ValueTable.counterBytes,ValueTable.same,send,recv,
      Expr.eval,Expr.evalWith,rowEnv,Trace.height,rawTrace,row,c,n,k,ZkFormal.Near.Dsl.bool,
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
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,
       ] <;>
    (repeat' first | split | constructor) <;>
    simp_all [Lean.Grind.Semiring.natCast_zero,
      Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_add,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero] <;> grind

end ZkFormal.NearV3.Qv.Candidates.ValueGen
