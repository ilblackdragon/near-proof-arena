import ZkFormal.NearV3.Qv.Extract.ShardCountCapacity
import ZkFormal.NearV3.Qv.Extract.NativeShardBalance

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Actual physical byte and shard balances force uniqueness of the buffered
parser provider. No separate provider-uniqueness or native-stream premise. -/
theorem physical_buffered_provider_unique {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH false m)
    {p p' : Nat × Nat} (hp : p∈v.segs) (hp' : p'∈v.segs)
    (hm : tr.cell tq p.1 mBuffer=1) (hm' : tr.cell tq p'.1 mBuffer=1) : p=p' := by
  obtain ⟨ss,hrecords,hperm⟩ := physical_native_shard_balance hL q v as aks vals hv ha hk ht hbalance ts hsha hbytes hqsh
  exact buffered_provider_unique (buffered_provider_capacity hL q v.segs ss hperm) hp hp' hm hm'

end ZkFormal.NearV3.Qv.Extract
