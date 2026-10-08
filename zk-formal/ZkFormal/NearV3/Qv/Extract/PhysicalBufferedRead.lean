import ZkFormal.NearV3.Qv.Extract.BufferedProvider
import ZkFormal.NearV3.Qv.Extract.NativeShardBounds
import ZkFormal.NearV3.Qv.Extract.CountReadMode

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- A present buffered queue read obtains its actual native value and every
shard request is authenticated to that same value. All provider and byte-range
facts are derived from the physical balances. -/
theorem physical_buffered_read {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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
    (hqvc : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC false m)
    (w : Nat × Nat) (hw : w∈q.segs)
    (hpresent : tr.cell tq w.1 Candidates.CombinedTable.absent=0)
    (hmode : cv tr tq w.1 len=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq w.1 vid ∧
      ∃ shards, BufferedValue (some (toBytes e.bytes)) shards ∧ shards.length<P ∧
        ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
          (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH false),
          m∈Parser.nativeShardMessages (tr.cell tq w.1 tau) shards := by
  obtain ⟨p,hp,hbuf,hvid,htau⟩ := physical_buffered_provider_exists hL q v hqvc w hw hpresent hmode
  obtain ⟨ss,hrecords,hperm⟩ := physical_native_shard_balance_bounded hL q v as aks vals hv ha hk ht hbalance ts hsha hbytes hqsh
  obtain ⟨e,he,hz,hid,hlen,hnative,hbound⟩ := hrecords p hp hbuf
  have htfield : tr.cell tq p.1 tau=tr.cell tq w.1 tau := by
    have h := congrArg Fp.ofNat htau
    simpa only [cv,Fp.ofNat_toNat] using h
  refine ⟨e,he,hz,hid.trans hvid,ss p,hnative,hbound,?_⟩
  intro m hm
  rw [←htfield]
  exact unique_shard_member hL q v.segs ss hperm hp hbuf hm

/-- The count gate authenticates the declared shard count to the native value
of the actual buffered read; no assumed native value or count equality. -/
theorem physical_count_read {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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
    (hqvc : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC false m)
    (w : Nat × Nat) (hw : w∈q.segs)
    (hcount : tr.cell tq w.1 Candidates.CombinedTable.countRead=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq w.1 vid ∧
      ∃ shards, BufferedValue (some (toBytes e.bytes)) shards ∧ shards.length<P ∧ cv tr tq w.1 count=shards.length ∧
        ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
          (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH false),
          m∈Parser.nativeShardMessages (tr.cell tq w.1 tau) shards := by
  have hend := seg_le_end q.segs 0 q.consecutive w hw
  have hn := (q.valid w hw).1
  have hrow : w.1<tr.height tq := by have := q.fits; omega
  have hprefix : w.1<segEnd 0 q.segs := by omega
  obtain ⟨hpresent,hmode⟩ := count_request_read_mode hL hrow hcount
  obtain ⟨e,he,hz,hid,ss,hbuf,hbound,hrequests⟩ := physical_buffered_read hL q v as aks vals hv ha hk ht hbalance ts hsha hbytes hqsh hqvc w hw hpresent hmode
  have hreq := shard_count_request_mem tr tq w.1 (segEnd 0 q.segs) pub hprefix hcount
  have hcnt := Parser.native_shard_count_nat hbound (hrequests _ hreq)
  exact ⟨e,he,hz,hid,ss,hbuf,hbound,hcnt.2,hrequests⟩

end ZkFormal.NearV3.Qv.Extract
