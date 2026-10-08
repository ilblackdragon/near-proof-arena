import ZkFormal.NearV3.Qv.Extract.ShardRecord
import ZkFormal.NearV3.Qv.Extract.BufferedValue
import ZkFormal.NearV3.Qv.Extract.NativeShardBytes

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open NearSpec NearSpecV3 Candidates.ValueTable

/-- Exact QSH wire representation of a native buffered shard vector. -/
def nativeShardMessages (tau : Fp) (shards : List Nat) : List (List Fp) :=
  [[tau,0,8,(shards.length:Fp)]] ++
    (List.range shards.length).flatMap (fun (j : Nat) =>
      (List.range 8).map (fun (i : Nat) =>
        [tau,(j:Fp),(i:Fp),(((u64 (shards.getD j 0)).getD i 0).toNat:Fp)]))

/-- Physical buffered QSH traffic describes exactly the same native value as
its authenticated bytes, preserving every shard occurrence and its ordinal. -/
theorem buffered_native_shard_stream {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (hfit : s+n≤tr.height tt)
    (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
    (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
    (hm : tr.cell tt s mBuffer=1)
    (bs : Bytes) (hlen : bs.length=n)
    (hbytes : ∀ i, i<n → (bs.getD i 0).toNat=cv tr tt (s+i) byte) :
    ∃ shards, BufferedValue (some bs) shards ∧
      (List.range' s n).flatMap (fun r =>
        rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true)=
      nativeShardMessages (tr.cell tt s tau) shards := by
  obtain ⟨shards,hbuf⟩ := buffered_queue_bytes hL hfit hw hs hm bs hlen hbytes
  have hn := (buffered_structure hL hfit hw hs hm).1
  have hnative := bufferedValue_length hbuf
  have hcount : cv tr tt s count=shards.length := by omega
  have hfield : tr.cell tt s count=(shards.length:Fp) := by
    rw [←hcount]
    exact (Fp.ofNat_toNat _).symm
  refine ⟨shards,hbuf,?_⟩
  rw [buffered_shard_segment hL hfit hw hs hm,hcount,hfield]
  unfold nativeShardMessages
  apply congrArg (fun xs => [[tr.cell tt s tau,0,8,(shards.length:Fp)]]++xs)
  rw [List.flatMap_def,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have hb := hbytes (4+24*j+i) (by omega)
  have he := bufferedValue_shard_byte hbuf j hj' i hi'
  rw [List.getElem_eq_getD (h:=hj') 0] at he
  rw [he] at hb
  have hcell : tr.cell tt (s+4+24*j+i) byte=
      (((u64 (shards.getD j 0)).getD i 0).toNat:Fp) := by
    rw [hb]
    simpa only [cv,Nat.add_assoc,natCast_eq] using (Fp.ofNat_toNat (tr.cell tt (s+4+24*j+i) byte)).symm
  rw [hcell]

end ZkFormal.NearV3.Qv.Extract.Parser
