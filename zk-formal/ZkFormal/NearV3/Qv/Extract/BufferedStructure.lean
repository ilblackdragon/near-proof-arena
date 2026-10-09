import ZkFormal.NearV3.Qv.Extract.EntryCounter
import ZkFormal.NearV3.Qv.Extract.EntryWords

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

/-- Complete physical buffered structure, with a canonical count, ordered shard
words, and equal index words. Native byte decoding and QSH balance are separate. -/
theorem buffered_structure {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (hfit : s+n≤tr.height tt)
    (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
    (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
    (hm : tr.cell tt s mBuffer=1) :
    n=4+24*cv tr tt s count ∧
    ∀ j, j<cv tr tt s count →
      tr.cell tt (s+4+24*j) entry=(j:Fp) ∧
      ∀ i, i<8 →
        tr.cell tt (s+4+24*j+i) shard=1 ∧ tr.cell tt (s+4+24*j+i) (sel i)=1 ∧
        tr.cell tt (s+4+24*j+8+i) firstIndex=1 ∧
        tr.cell tt (s+4+24*j+16+i) nextIndex=1 ∧
        tr.cell tt (s+4+24*j+8+i) byte=tr.cell tt (s+4+24*j+16+i) byte := by
  obtain ⟨k,hlen,hstarts⟩ := buffered_record_layout hL hfit hw hs hm
  have hcount := buffered_count_exact hL hfit hw hs hm hlen hstarts
  rw [hcount]
  refine ⟨hlen,?_⟩
  intro j hj
  have start := hstarts j hj
  refine ⟨buffered_entry_ordinal hL hfit hw hs hm hlen hstarts j hj,?_⟩
  intro i hi
  have rows := buffered_entry_rows hL hfit hw hs hm (r:=s+4+24*j)
    (by omega) (by omega) start.1 start.2
  have hbytes := buffered_words_equal hL hfit hw hs hm (r:=s+4+24*j)
    (by omega) (by omega) start.1 start.2 i hi
  exact ⟨(rows.2.1 i hi).1,(rows.2.1 i hi).2,(rows.2.2.1 i hi).1,
    (rows.2.2.2 i hi).1,hbytes⟩

end ZkFormal.NearV3.Qv.Extract.Parser
