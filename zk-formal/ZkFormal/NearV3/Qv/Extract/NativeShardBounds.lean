import ZkFormal.NearV3.Qv.Extract.NativeShardLookup

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Every buffered shard vector recovered from a physical record is below the
field modulus. This follows from the existing table height, not a new domain cap. -/
theorem physical_native_shard_bound {tr : Trace Fp} {tt s n : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (hfit : s+n≤tr.height tt) {vals : List ValE} (hv : ValWf vals)
    {e : ValE} (he : e∈vals) (hz : e.vz=false) (hlen : e.len=n)
    {ss : List Nat} (hbuf : BufferedValue (some (toBytes e.bytes)) ss) :
    ss.length≤174762 ∧ ss.length<P := by
  have hshape := (hv.shape e he).2 hz
  have hb := bufferedValue_length hbuf
  simp only [toBytes,List.length_map] at hb
  have hh : tr.height tt≤4194304 := height_le hL
  have hp : 174762<P := by decide
  constructor <;> omega

open Candidates.ValueTable

/-- The physical-balance native stream comes with canonical shard counts for
all recovered records; downstream lookup needs no separate length premise. -/
theorem physical_native_shard_balance_bounded {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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
          BufferedValue (some (toBytes e.bytes)) (shards p) ∧ (shards p).length<P) ∧
      ((List.range (segEnd 0 q.segs)).flatMap
        (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH false)).Perm (
      v.segs.flatMap (fun p => if tr.cell tq p.1 mBuffer=1 then
        Parser.nativeShardMessages (tr.cell tq p.1 tau) (shards p) else [])) := by
  obtain ⟨ss,hrecords,hperm⟩ := physical_native_shard_balance hL q v as aks vals hv ha hk ht hbalance ts hsha hbytes hqsh
  refine ⟨ss,?_,hperm⟩
  intro p hp hm
  obtain ⟨e,he,hz,hid,hlen,hbuf⟩ := hrecords p hp hm
  have hend := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tq := Nat.le_trans hend.2 v.fits
  exact ⟨e,he,hz,hid,hlen,hbuf,(physical_native_shard_bound hL hfit hv he hz hlen hbuf).2⟩

end ZkFormal.NearV3.Qv.Extract
