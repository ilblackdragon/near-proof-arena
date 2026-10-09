import ZkFormal.NearV3.Qv.Extract.WalkShardPosition

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

def isShardCount (m : List Fp) : Bool := decide (m.getD 2 0=8)

private theorem byte_position_ne_count {i : Nat} (hi : i<8) : (i:Fp)≠8 := by
  intro he
  have hn := congrArg Fp.toNat he
  change (Fp.ofNat i).toNat=(8:Fp).toNat at hn
  have hp : 8<P := by decide
  have h8 : (8:Fp).toNat=8 := by decide
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show i<P by omega),h8] at hn
  omega

/-- Each native buffer contributes exactly one count packet, including empty buffers. -/
theorem native_shard_count_filter (tau : Fp) (ss : List Nat) :
    (Parser.nativeShardMessages tau ss).filter isShardCount=[[tau,0,8,(ss.length:Fp)]] := by
  unfold Parser.nativeShardMessages
  rw [List.filter_append,List.filter_flatMap]
  have hz : (List.range ss.length).flatMap (fun (j : Nat) =>
      ((List.range 8).map (fun (i : Nat) =>
        [tau,(j:Fp),(i:Fp),(((NearSpec.u64 (ss.getD j 0)).getD i 0).toNat:Fp)])).filter isShardCount)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j hj
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    have hn := byte_position_ne_count (List.mem_range.mp hi)
    simpa [isShardCount] using hn
  rw [hz,List.append_nil]
  simp [isShardCount]

/-- On a checked walk segment only the actual count gate survives count filtering. -/
theorem physical_shard_count_filter {tr : Trace Fp} {tt s n r : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub) (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt Candidates.CombinedTable.walk)
      (isOne tr tt Candidates.CombinedTable.wf) (isOne tr tt Candidates.CombinedTable.wl) s n)
    (hr : s≤r) (hb : r<s+n) :
    (rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false).filter isShardCount=
      if tr.cell tt r Candidates.CombinedTable.countRead=1 then
        [[tr.cell tt r tau,0,8,tr.cell tt r count]] else [] := by
  rw [shard_receive_row,List.filter_append]
  by_cases hg : tr.cell tt r Candidates.CombinedTable.groupByte=1
  · have hn := shard_request_not_count hL hfit hs hr hb hg
    by_cases hc : tr.cell tt r Candidates.CombinedTable.countRead=1 <;> simp [hg,hc,isShardCount,hn]
  · by_cases hc : tr.cell tt r Candidates.CombinedTable.countRead=1 <;> simp [hg,hc,isShardCount]

end ZkFormal.NearV3.Qv.Extract
