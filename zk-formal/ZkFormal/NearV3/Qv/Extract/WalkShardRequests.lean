import ZkFormal.NearV3.Qv.Extract.NativeShardBalance

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (tau count)

/-- Exact physical receive packets, with the byte and count gates kept distinct. -/
theorem shard_receive_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tt r pub B_QSH false=
      (if tr.cell tt r groupByte=1 then
        [[tr.cell tt r tau,tr.cell tt r slot-3,tr.cell tt r wp-1,tr.cell tt r wb]] else []) ++
      (if tr.cell tt r countRead=1 then [[tr.cell tt r tau,0,8,tr.cell tt r count]] else []) := by
  have h3 : ((3:Nat):Fp)=3 := by decide
  have h8 : ((8:Nat):Fp)=8 := by decide
  by_cases hg : tr.cell tt r groupByte=1 <;> by_cases hc : tr.cell tt r countRead=1 <;>
    simp [rowTraffic,interactions,send,recv,B_QSH,B_FINAL,B_KEYNIB,B_VBYTES,Candidates.ValueTable.B_QVC,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,eval_c,eval_sub,eval_k,hg,hc,h3,h8,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one]

/-- A live walk shard-byte request occurs in the complete receiving stream. -/
theorem shard_byte_request_mem (tr : Trace Fp) (tt r H : Nat) (pub : List Fp)
    (hr : r<H) (hg : tr.cell tt r groupByte=1) :
    [tr.cell tt r tau,tr.cell tt r slot-3,tr.cell tt r wp-1,tr.cell tt r wb]∈
      (List.range H).flatMap (fun r => rowTraffic interactions tr tt r pub B_QSH false) := by
  apply List.mem_flatMap.mpr
  refine ⟨r,List.mem_range.mpr hr,?_⟩
  rw [shard_receive_row]
  simp [hg]

/-- A live walk count request occurs in the complete receiving stream. -/
theorem shard_count_request_mem (tr : Trace Fp) (tt r H : Nat) (pub : List Fp)
    (hr : r<H) (hc : tr.cell tt r countRead=1) :
    [tr.cell tt r tau,0,8,tr.cell tt r count]∈
      (List.range H).flatMap (fun r => rowTraffic interactions tr tt r pub B_QSH false) := by
  apply List.mem_flatMap.mpr
  refine ⟨r,List.mem_range.mpr hr,?_⟩
  rw [shard_receive_row]
  simp [hc]

end ZkFormal.NearV3.Qv.Extract
