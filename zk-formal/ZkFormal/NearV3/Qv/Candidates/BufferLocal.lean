import ZkFormal.NearV3.Qv.Candidates.RowCells
import ZkFormal.NearV3.Qv.Candidates.BufferHeader

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem bufferTrace_header_prefix_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hn : es.length<16777216) (hb : 4+24*es.length ≤ 2^log)
    {r : Nat} (hr : r<3) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferTrace (F:=F) log vid tau users es) 0 r [] = 0 := by
  generalize hheight : 2^log = height at hb
  have ht := buffer_count_top_zero es.length hn
  have hm1 : 1%height=1 := Nat.mod_eq_of_lt (by omega)
  have hm2 : 2%height=2 := Nat.mod_eq_of_lt (by omega)
  have hm3 : 3%height=3 := Nat.mod_eq_of_lt (by omega)
  have hn1 : ¬ 1=height := by omega
  have hn2 : ¬ 2=height := by omega
  have hn3 : ¬ 3=height := by omega
  have hl1 : ¬ 1=4+24*es.length := by omega
  have hl2 : ¬ 2=4+24*es.length := by omega
  have hl3 : ¬ 3=4+24*es.length := by omega
  have hc : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hc with rfl|rfl|rfl
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
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,hheight,hm1,hm2,hm3,ht,hn1,hn2,hn3,hl1,hl2,hl3
       ] <;>
    (repeat' first | split | constructor)
  all_goals try simp_all [Lean.Grind.Semiring.natCast_zero,
      Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_add,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.one_mul,Lean.Grind.Semiring.mul_one,
      Lean.Grind.Semiring.add_zero,Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero]
  all_goals grind

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem bufferTrace_header_end_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hn : es.length<16777216) (hb : 4+24*es.length ≤ 2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferTrace (F:=F) log vid tau users es) 0 3 [] = 0 := by
  generalize hheight : 2^log = height at hb
  have ht := buffer_count_top_zero es.length hn
  have hv := buffer_count_value es.length hn
  have hF := congrArg (@Nat.cast F Lean.Grind.Semiring.natCast) hv
  simp only [Lean.Grind.Semiring.natCast_add,Lean.Grind.Semiring.natCast_mul] at hF
  clear hv
  have hzero : u32 0 = [0,0,0,0] := rfl
  have hm4 : 4%height=if height=4 then 0 else 4 := by
    split
    · rename_i h; simp [h]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hl4 : (4=4+24*es.length) ↔ es.length=0 := by omega
  have hpos : (4<4+24*es.length) ↔ es.length≠0 := by omega
  by_cases hz : es.length=0 <;> by_cases he : height=4
  all_goals try omega
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
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.AddCommGroup.neg_zero,hheight,hm4,ht,hz,he,hl4,hpos,hzero
       ] <;>
    (repeat' first | split | constructor)
  all_goals try simp_all [Lean.Grind.Semiring.natCast_zero,
      Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_add,
      Lean.Grind.Semiring.natCast_mul,Lean.Grind.Semiring.zero_mul,
      Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.one_mul,
      Lean.Grind.Semiring.mul_one,Lean.Grind.Semiring.add_zero,
      Lean.Grind.AddCommMonoid.zero_add,Lean.Grind.AddCommGroup.add_neg_cancel,
      Lean.Grind.AddCommGroup.neg_zero]
  all_goals grind

theorem bufferTrace_header_local (log vid tau users : Nat) (es : List ByteBuffer)
    (hn : es.length<16777216) (hb : 4+24*es.length ≤ 2^log) {r : Nat} (hr : r<4) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (bufferTrace (F:=F) log vid tau users es) 0 r [] = 0 := by
  by_cases hp : r<3
  · exact bufferTrace_header_prefix_local log vid tau users es hn hb hp
  · have h : r=3 := by omega
    subst r
    exact bufferTrace_header_end_local log vid tau users es hn hb

end ZkFormal.NearV3.Qv.Candidates.ValueGen
