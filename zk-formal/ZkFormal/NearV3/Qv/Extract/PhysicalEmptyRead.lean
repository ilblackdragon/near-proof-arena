import ZkFormal.NearV3.Qv.Extract.EmptyProvider
import ZkFormal.NearV3.Qv.Extract.PhysicalNativeRecord

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- A present empty-index read obtains its actual native sixteen-byte value,
and the native empty-queue predicate follows from the physical constraints. -/
theorem physical_empty_read {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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


    (hqvc : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC false m)
    (w : Nat × Nat) (hw : w∈q.segs)
    (hpresent : tr.cell tq w.1 Candidates.CombinedTable.absent=0)
    (hmode : cv tr tq w.1 len=0) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq w.1 vid ∧ e.len=16 ∧
      EmptyQueue (some (toBytes e.bytes)) := by
  obtain ⟨p,hp,hempty,hvid,htau⟩ := physical_empty_provider_exists hL q v hqvc w hw hpresent hmode
  obtain ⟨e,he,hz,hid,hlen,hval⟩ := physical_empty_native hL q v as aks vals hv ha hk ht hbalance ts hsha hbytes p hp hempty
  exact ⟨e,he,hz,hid.trans hvid,hlen,hval⟩

end ZkFormal.NearV3.Qv.Extract
