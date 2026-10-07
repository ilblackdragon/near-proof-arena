import ZkFormal.NearV3.Qv.Candidates.BufferLocal
import ZkFormal.NearV3.Qv.Candidates.BufferEntryRows

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem bufferTrace_entry_interior_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hb : 4+24*es.length ≤ 2^log) (i j : Nat) (hi : i<es.length) (hj : j<23) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferTrace (F:=F) log vid tau users es) 0 (4+24*i+j) [] = 0 := by
  generalize hheight : 2^log = height at hb
  have hfirst : 4+24*i+j≠0 := by omega
  have hnfirst : 4+24*i+j+1≠0 := by omega
  have hlast : ¬4+24*i+j+1=height := by omega
  have hvl : ¬4+24*i+j+1=4+24*es.length := by omega
  have hm : (4+24*i+j+1)%height=4+24*i+j+1 := Nat.mod_eq_of_lt (by omega)
  have hC := bufferRowAt_entry vid tau users es i j hi (by omega)
  have hN : bufferRowAt vid tau users es (4+24*i+j+1) =
      let e := es.getD i ⟨[],[]⟩
      row ⟨vid,tau,users,1,4+24*es.length,es.length⟩ (4+24*i+j+1)
        ((if j+1<8 then e.shard.getD (j+1) 0 else e.index.getD ((j+1)%8) 0).toNat)
        (if j+1<8 then 1 else if j+1<16 then 2 else 3) ((j+1)%8) i e.index := by
    simpa only [Nat.add_assoc] using bufferRowAt_entry vid tau users es i (j+1) hi (by omega)
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,hheight,hm,hC,hN,hfirst,hnfirst,hlast,hvl
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
