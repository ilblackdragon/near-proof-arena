import ZkFormal.NearV3.Qv.Extract.PhysicalBufferedUnique
import ZkFormal.NearV3.Qv.Extract.NativeShardLookup

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (q : WalkChain tr tt) (ps : List (Nat × Nat)) (ss : Nat × Nat → List Nat)
variable (hperm : ((List.range (segEnd 0 q.segs)).flatMap
  (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false)).Perm
  (ps.flatMap (fun p => if tr.cell tt p.1 mBuffer=1 then
    Parser.nativeShardMessages (tr.cell tt p.1 tau) (ss p) else [])))
variable {p : Nat × Nat} (hp : p∈ps) (hm : tr.cell tt p.1 mBuffer=1)
include hL q ps ss hperm hp hm

/-- Any balanced shard request belongs to the same unique buffered provider. -/
theorem unique_shard_member {m : List Fp}
    (hreq : m∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false)) :
    m∈Parser.nativeShardMessages (tr.cell tt p.1 tau) (ss p) := by
  have hcap := buffered_provider_capacity hL q ps ss hperm
  obtain ⟨p',hp',hmsg⟩ := List.mem_flatMap.mp (hperm.mem_iff.mp hreq)
  by_cases hm' : tr.cell tt p'.1 mBuffer=1
  · have he := buffered_provider_unique hcap hp hp' hm hm'
    subst p'
    simpa only [hm,ite_true] using hmsg
  · simp only [hm',ite_false,List.not_mem_nil] at hmsg

/-- A count request decodes the length of that provider's native shard vector. -/
theorem unique_shard_count {id value : Fp} (hlen : (ss p).length<P)
    (hreq : [id,0,8,value]∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false)) :
    id=tr.cell tt p.1 tau ∧ value.toNat=(ss p).length := by
  exact Parser.native_shard_count_nat hlen (unique_shard_member hL q ps ss hperm hp hm hreq)

/-- A canonical entry/byte request decodes the exact byte of that native vector. -/
theorem unique_shard_byte {id value : Fp} {j i : Nat}
    (hlen : (ss p).length<P) (hj : j<P) (hi : i<8)
    (hreq : [id,(j:Fp),(i:Fp),value]∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false)) :
    id=tr.cell tt p.1 tau ∧ j<(ss p).length ∧
      value=(((NearSpec.u64 ((ss p).getD j 0)).getD i 0).toNat:Fp) := by
  exact Parser.native_shard_byte_index hlen hj hi (unique_shard_member hL q ps ss hperm hp hm hreq)

end ZkFormal.NearV3.Qv.Extract
