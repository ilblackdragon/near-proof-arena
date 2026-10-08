import ZkFormal.NearV3.Qv.Extract.RecordValue
import ZkFormal.NearV3.Qv.Extract.NativeShardStream
import ZkFormal.NearV3.Qv.Extract.EmptyWords
import ZkFormal.Near.Link.EncLemmas

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Byte range, supplied by SHA reception, makes the extracted natural record
and its native UInt8 encoding agree at every position. -/
theorem native_value_bytes {tr : Trace Fp} {tt s n : Nat} {e : ValE}
    (hb : Bytes8 e.bytes) (hlen : e.bytes.length=n)
    (hbytes : ∀ i, i<n → cv tr tt (s+i) byte=e.bytes.getD i 0) :
    (toBytes e.bytes).length=n ∧
      ∀ i, i<n → ((toBytes e.bytes).getD i 0).toNat=cv tr tt (s+i) byte := by
  refine ⟨by simpa [toBytes] using hlen,?_⟩
  intro i hi
  rw [hbytes i hi]
  have hi' : i<e.bytes.length := by omega
  simp only [toBytes,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem hi',Option.map_some,Option.getD_some]
  exact Link.toNat_ofNat_byte (hb _ (List.getElem_mem hi'))

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable {vals : List ValE} (hv : ValWf vals)
variable (hvb : ∀ e∈vals, Bytes8 e.bytes)
variable (hc : (physicalRecordBytes tr tt s n pub).Perm
  (((valRecvs vals B_VBYTES).map Msg.toFp).filter
    (fun m => decide ((byteKey m).1=tr.cell tt s vid))))
include hL hfit hw hs hv hvb hc

/-- Buffered mode recovers a native value from the actual unique value record,
not a separately assumed native byte witness. -/
theorem buffered_native_record (hm : tr.cell tt s mBuffer=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tt s vid ∧ e.len=n ∧
      ∃ shards, BufferedValue (some (toBytes e.bytes)) shards ∧
        (List.range' s n).flatMap (fun r =>
          rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true)=
        Parser.nativeShardMessages (tr.cell tt s tau) shards := by
  have hmin := (Parser.buffered_header_rows hL hfit hw hs hm 3 (by omega)).1
  have hn : cv tr tt s len≠0 := by
    have hcases := Parser.length_cases hL hfit hw hs
    rcases hcases with hcases|hcases <;> omega
  obtain ⟨e,he,hz,hid,hlen,hlogical,hbytes⟩ := record_value_exact hL hfit hw hs hn hv hc
  have hshape := (hv.shape e he).2 hz
  have hb := native_value_bytes (hvb e he) (by omega) hbytes
  obtain ⟨shards,hbuf,hstream⟩ := Parser.buffered_native_shard_stream hL hfit hw hs hm
    (toBytes e.bytes) hb.1 hb.2
  exact ⟨e,he,hz,hid,hlen,shards,hbuf,hstream⟩

/-- Empty-index mode likewise accepts the unique native value record. -/
theorem empty_native_record (hm : tr.cell tt s mEmpty=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tt s vid ∧ e.len=16 ∧
      EmptyQueue (some (toBytes e.bytes)) := by
  have hn16 := Parser.empty_row_count hL hfit hw hs hm
  have hn : cv tr tt s len≠0 := by
    have hcases := Parser.length_cases hL hfit hw hs
    rcases hcases with hcases|hcases <;> omega
  obtain ⟨e,he,hz,hid,hlen,hlogical,hbytes⟩ := record_value_exact hL hfit hw hs hn hv hc
  have hshape := (hv.shape e he).2 hz
  have hb := native_value_bytes (hvb e he) (by omega) hbytes
  exact ⟨e,he,hz,hid,by omega,Parser.empty_queue_bytes hL hfit hw hs hm (toBytes e.bytes) hb.1 hb.2⟩

end ZkFormal.NearV3.Qv.Extract
