import ZkFormal.NearV3.Qv.Candidates.ValueTraffic

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl

variable {F : Type} [Lean.Grind.CommRing F]

/-- Direct sixteen-row encoding for the empty-index mode. -/
def emptyTrace (vid tau users : Nat) (index : Bytes) : Trace F :=
  { log := fun _ => 4,
    cell := fun _ r c =>
      let cfg : Config := ⟨vid,tau,users,0,16,0⟩
      (@Nat.cast F Lean.Grind.Semiring.natCast ((row cfg r (index.getD (r%8) 0).toNat (if r<8 then 2 else 3) (r%8) 0 index).getD c 0)) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem emptyTrace_local (vid tau users : Nat) (index : Bytes) {r : Nat} (hr : r<16) :
    ∀ e ∈ ValueTable.table.allConstraints, e.eval (emptyTrace (F:=F) vid tau users index) 0 r [] = 0 := by
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨
      r=8 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=14 ∨ r=15 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [ValueTable.table,Table.allConstraints,Table.bitConstraints,ValueTable.constraints,
      ValueTable.interactions,ValueTable.modes,ValueTable.phases,ValueTable.selectors,
      ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,ValueTable.entryEnd,
      ValueTable.mode,ValueTable.counterBytes,ValueTable.same,send,recv,
      Expr.eval,Expr.evalWith,rowEnv,Trace.height,emptyTrace,row,c,n,k,ZkFormal.Near.Dsl.bool,sub,sum,smul,mul3,eqG,
      ZkFormal.Near.Dsl.not,ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.vz,ValueTable.gb,
      ValueTable.cont,ValueTable.vid,ValueTable.len,ValueTable.pos,ValueTable.byte,ValueTable.users,
      ValueTable.tau,ValueTable.entry,ValueTable.count,ValueTable.mEmpty,ValueTable.mBuffer,
      ValueTable.mRaw,ValueTable.header,ValueTable.shard,ValueTable.firstIndex,ValueTable.nextIndex,
      ValueTable.sel,ValueTable.reg,List.range_succ,Function.comp_def,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero] <;> grind

end ZkFormal.NearV3.Qv.Candidates.ValueGen
