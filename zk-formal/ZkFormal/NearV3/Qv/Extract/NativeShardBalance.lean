import ZkFormal.NearV3.Qv.Extract.NativeShardWhole

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Physical QSH conservation identifies the complete multiset of walk requests
with recovered native buffered values, preserving all message multiplicities. -/
theorem physical_native_shard_balance {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tq pub)
    (q : WalkChain tr tq) (v : ParserChain tr tq (segEnd 0 q.segs))
    (as : List AcctV) (aks : List AkeyE) (vals : List ValE) (hv : ValWf vals)
    (ha : TableTraffic AcctV3.interactions tr ta pub (acctV3Traffic as))
    (hk : TableTraffic AkeyV3.interactions tr tk pub (akeyTraffic aks))
    (ht : TableTraffic ValV3.interactions tr tv pub (valTraffic vals))
    (hbalance : ∀ m,
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_VBYTES true m +
      tableBusCount AcctV3.interactions tr ta pub B_VBYTES true m +
      tableBusCount AkeyV3.interactions tr tk pub B_VBYTES true m =
      tableBusCount ValV3.interactions tr tv pub B_VBYTES false m)
    (ts : List Nat) (hsha : ∀ t∈ts, Sha.ShaLocal tr t pub)
    (hbytes : ∀ m, tableBusCount ValV3.interactions tr tv pub B_BYTES true m≤
      Assembly.shaUnionCount tr pub ts false B_BYTES m)

    (hqsh : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH false m) :
    ∃ shards : Nat × Nat → List Nat,
      (∀ p∈v.segs, tr.cell tq p.1 mBuffer=1 →
        ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) (shards p)) ∧
      ((List.range (segEnd 0 q.segs)).flatMap
        (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH false)).Perm (
      v.segs.flatMap (fun p => if tr.cell tq p.1 mBuffer=1 then
        Parser.nativeShardMessages (tr.cell tq p.1 tau) (shards p) else [])) := by
  obtain ⟨ss,he,htotal⟩ := physical_native_shard_all hL q v as aks vals hv ha hk ht hbalance ts hsha hbytes
  refine ⟨ss,he,List.perm_iff_count.mpr ?_⟩
  intro m
  have h := hqsh m
  rw [tableBusCount_eq,tableBusCount_eq,htotal,shard_receives_prefix hL q] at h
  exact h.symm

end ZkFormal.NearV3.Qv.Extract
