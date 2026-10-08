import ZkFormal.NearV3.Qv.Extract.BufferedStructure
import ZkFormal.NearV3.Qv.Extract.HeaderValue
import ZkFormal.NearV3.Qv.Extract.NativeBufferedBytes

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open NearSpec NearSpecV3 Candidates.ValueTable

private theorem leNat_first_four (bs : Bytes) (hb : 4≤bs.length) :
    leNat (bs.take 4)=(bs.getD 0 0).toNat+256*((bs.getD 1 0).toNat+
      256*((bs.getD 2 0).toNat+256*(bs.getD 3 0).toNat)) := by
  match bs with
  | [] => simp at hb
  | [_] => simp at hb
  | [_,_] => simp at hb
  | [_,_,_] => simp at hb
  | b0::b1::b2::b3::rest => simp [leNat]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable (hm : tr.cell tt s mBuffer=1)
variable (bs : Bytes) (hlen : bs.length=n)
variable (hbytes : ∀ i, i<n → (bs.getD i 0).toNat=cv tr tt (s+i) byte)
include hL hfit hw hs hm hlen hbytes

/-- The authenticated native header decodes to the extracted physical count. -/
theorem buffered_native_count : leNat (bs.take 4)=cv tr tt s count := by
  have hmin := (buffered_header_rows hL hfit hw hs hm 3 (by omega)).1
  have hb : ∀ i, i<3 → cv tr tt (s+i) byte<256 := by
    intro i hi
    rw [←hbytes i (by omega)]
    exact (bs.getD i 0).toNat_lt
  have hc := buffered_header_count_nat hL hfit hw hs hm hb
  have h0 := hbytes 0 (by omega)
  have h1 := hbytes 1 (by omega)
  have h2 := hbytes 2 (by omega)
  have h3 := hbytes 3 (by omega)
  simp only [Nat.add_zero] at h0
  have hz := congrArg Fp.toNat (buffered_header_high_zero hL hfit hw hs hm)
  change cv tr tt (s+3) byte=0 at hz
  rw [hz] at h3
  rw [←h0,←h1,←h2] at hc
  have hh := leNat_first_four bs (by omega)
  rw [h3] at hh
  omega

/-- Native first/next words match at every extracted entry ordinal. -/
theorem buffered_native_words (j : Nat) (hj : j<cv tr tt s count) :
    (bs.drop (4+24*j+8)).take 8=(bs.drop (4+24*j+16)).take 8 := by
  have hstr := buffered_structure hL hfit hw hs hm
  have hlen1 : ((bs.drop (4+24*j+8)).take 8).length=8 := by
    simp only [List.length_take,List.length_drop]; omega
  have hlen2 : ((bs.drop (4+24*j+16)).take 8).length=8 := by
    simp only [List.length_take,List.length_drop]; omega
  apply List.ext_getElem (by omega)
  intro i hi hi'
  have hi8 : i<8 := by omega
  rw [List.getElem_take,List.getElem_drop,List.getElem_take,List.getElem_drop]
  apply UInt8.toNat_inj.mp
  have h1 := hbytes (4+24*j+8+i) (by omega)
  have h2 := hbytes (4+24*j+16+i) (by omega)
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 4+24*j+8+i<bs.length by omega),
    List.getElem?_eq_getElem (show 4+24*j+16+i<bs.length by omega),Option.getD_some] at h1 h2
  rw [h1,h2]
  have he := congrArg Fp.toNat ((hstr.2 j hj).2 i hi8).2.2.2.2
  simpa only [cv,Nat.add_assoc] using he

/-- Actual AIR buffered records over identified native bytes satisfy the native
BufferedValue predicate. No shard sorting, uniqueness or extra domain cap is assumed. -/
theorem buffered_queue_bytes : ∃ shards, BufferedValue (some bs) shards := by
  have hstr := buffered_structure hL hfit hw hs hm
  exact buffered_value_of_bytes bs (cv tr tt s count) (by omega)
    (buffered_native_count hL hfit hw hs hm bs hlen hbytes)
    (buffered_native_words hL hfit hw hs hm bs hlen hbytes)

end ZkFormal.NearV3.Qv.Extract.Parser
