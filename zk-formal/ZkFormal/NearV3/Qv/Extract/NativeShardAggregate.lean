import ZkFormal.NearV3.Qv.Extract.PhysicalNativeRecord
import ZkFormal.NearV3.Qv.Extract.ShardAggregate

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Physical balances identify every buffered record with its native value and
identify the complete ordered parser shard stream, including repeated records. -/
theorem physical_native_shard_suffix {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
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
 :
    ∃ shards : Nat × Nat → List Nat,
      (∀ p∈v.segs, tr.cell tq p.1 mBuffer=1 →
        ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) (shards p)) ∧
      (List.range' (segEnd 0 q.segs) (tr.height tq-segEnd 0 q.segs)).flatMap
        (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH true)=
      v.segs.flatMap (fun p => if tr.cell tq p.1 mBuffer=1 then
        Parser.nativeShardMessages (tr.cell tq p.1 tau) (shards p) else []) := by
  classical
  have hx : ∀ p : Nat × Nat, ∃ shards : List Nat,
      p∈v.segs → tr.cell tq p.1 mBuffer=1 →
        (∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) shards) ∧
        (List.range' p.1 p.2).flatMap (fun r =>
          rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH true)=
          Parser.nativeShardMessages (tr.cell tq p.1 tau) shards := by
    intro p
    by_cases hp : p∈v.segs
    · by_cases hm : tr.cell tq p.1 mBuffer=1
      · obtain ⟨e,he,hz,hid,hlen,ss,hbuf,hstream⟩ :=
          physical_buffered_native hL q v as aks vals hv ha hk ht hbalance ts hsha hbytes p hp hm
        exact ⟨ss,fun _ _ => ⟨⟨e,he,hz,hid,hlen,hbuf⟩,hstream⟩⟩
      · exact ⟨[],fun _ hm' => False.elim (hm hm')⟩
    · exact ⟨[],fun hp' _ => False.elim (hp hp')⟩
  let shards := fun p => Classical.choose (hx p)
  have hshards := fun p => Classical.choose_spec (hx p)
  refine ⟨shards,fun p hp hm => (hshards p hp hm).1,?_⟩
  rw [parser_shard_suffix hL q v true]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro p hp
  by_cases hm : tr.cell tq p.1 mBuffer=1
  · simpa only [hm,ite_true,List.flatMap_def,shards] using (hshards p hp hm).2
  · simpa only [hm,ite_false,List.flatMap_def] using nonbuffer_record_silent hL q v p hp hm true

end ZkFormal.NearV3.Qv.Extract
