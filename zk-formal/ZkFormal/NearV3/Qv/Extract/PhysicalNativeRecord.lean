import ZkFormal.NearV3.Qv.Extract.ValShaBytes

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Physical byte balances and locally valid SHA tables suffice to recover the
same native buffered value and its exact shard stream. There is no independent
byte-range, native-byte-witness, or record-ownership assumption. -/
theorem physical_buffered_native {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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
    (p : Nat × Nat) (hp : p∈v.segs) (hm : tr.cell tq p.1 mBuffer=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
      ∃ shards, BufferedValue (some (toBytes e.bytes)) shards ∧
        (List.range' p.1 p.2).flatMap (fun r =>
          rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH true)=
        Parser.nativeShardMessages (tr.cell tq p.1 tau) shards := by
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tq := Nat.le_trans hb.2 v.fits
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tq r Candidates.CombinedTable.walk=0 := by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  have hs := v.valid p hp
  have hmin := (Parser.buffered_header_rows hL hfit hw hs hm 3 (by omega)).1
  have hn : cv tr tq p.1 len≠0 := by
    rcases Parser.length_cases hL hfit hw hs with h|h <;> omega
  have hc := physical_balanced_record_complete hL q v as aks vals hv ha hk ht hbalance p hp hn
  exact buffered_native_record hL hfit hw hs hv (value_bytes_of_sha ts hsha vals hv ht hbytes) hc hm

/-- The same physical balances recover the native empty-index value. -/
theorem physical_empty_native {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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
    (p : Nat × Nat) (hp : p∈v.segs) (hm : tr.cell tq p.1 mEmpty=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=16 ∧
      EmptyQueue (some (toBytes e.bytes)) := by
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tq := Nat.le_trans hb.2 v.fits
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tq r Candidates.CombinedTable.walk=0 := by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  have hs := v.valid p hp
  have hmin := Parser.empty_row_count hL hfit hw hs hm
  have hn : cv tr tq p.1 len≠0 := by
    rcases Parser.length_cases hL hfit hw hs with h|h <;> omega
  have hc := physical_balanced_record_complete hL q v as aks vals hv ha hk ht hbalance p hp hn
  exact empty_native_record hL hfit hw hs hv (value_bytes_of_sha ts hsha vals hv ht hbytes) hc hm

end ZkFormal.NearV3.Qv.Extract
