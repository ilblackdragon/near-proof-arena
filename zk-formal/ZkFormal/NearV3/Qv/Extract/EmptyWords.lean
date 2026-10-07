import ZkFormal.NearV3.Qv.Extract.EmptyRows
import ZkFormal.NearV3.Qv.Queue

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s n : Nat} (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable (hem : tr.cell tt s mEmpty=1)
include hL hfit hw hs hem

theorem empty_header_zero (r : Nat) (hr : s≤r) (hb : r<s+n) :
    tr.cell tt r header=0 := by
  have hn := empty_row_count hL hfit hw hs hem
  have hrow : r<tr.height tt := by omega
  by_cases hi : r-s<8
  · have hf := (empty_first_rows hL hfit hw hs hem (r-s) hi).2.1
    have he : s+(r-s)=r := by omega
    rw [he] at hf
    exact (phase_exclusive hL hrow (hw r hr hb) (x:=firstIndex) (by simp [phases]) hf).2
      header (by simp [phases]) (by decide)
  · have hf := (empty_second_rows hL hfit hw hs hem (r-s-8) (by omega)).2.1
    have he : s+8+(r-s-8)=r := by omega
    rw [he] at hf
    exact (phase_exclusive hL hrow (hw r hr hb) (x:=nextIndex) (by simp [phases]) hf).2
      header (by simp [phases]) (by decide)

/-- The two index words share registers: there is no reset between them. -/
theorem empty_register_constant (i : Nat) (hi : i<8) :
    ∀ r, s≤r → r<s+n → tr.cell tt r (reg i)=tr.cell tt s (reg i) := by
  apply const_of
  intro r hr hb
  have hrow : r<tr.height tt := by omega
  have hwalk := hw r hr (by omega)
  have hlast := hs.2.2.2.2.2 r hr hb
  have hl : tr.cell tt r vl=0 := by
    rcases isBool hL hrow hwalk (x:=vl) (by simp) with h | h
    · exact h
    · simp [isOne,h] at hlast
  have hc := (record_continue hL hfit hw hs r hr (by omega) hl).2
  have hh : headerEnd.eval tr tt r pub=0 := by
    have hz := empty_header_zero hL hfit hw hs hem r hr (by omega)
    simp only [headerEnd,eval_mul,eval_c,hz]
    grind
  have hm := metadata hL hfit hw hs (x:=mEmpty) (by simp) r hr (by omega)
  rw [hem] at hm
  have hend := empty_last hL hrow hwalk hm
  have he : entryEnd.eval tr tt r pub=0 := by
    simp only [entryEnd,wordEnd,eval_mul,eval_c]
    rw [←hend,hl]
  exact register_carry hL hrow hwalk (by omega) hc hh he i hi

/-- Every first-index byte equals the corresponding last-index byte. -/
theorem empty_words_equal (i : Nat) (hi : i<8) :
    tr.cell tt (s+i) byte=tr.cell tt (s+8+i) byte := by
  obtain ⟨hf,hfirst,hsel⟩ := empty_first_rows hL hfit hw hs hem i hi
  obtain ⟨hn,hnext,hsel'⟩ := empty_second_rows hL hfit hw hs hem i hi
  have hb1 := selected_word_byte hL (show s+i<tr.height tt by omega)
    (hw (s+i) (by omega) (by omega)) hi hsel (x:=firstIndex) (by simp) hfirst
  have hb2 := selected_word_byte hL (show s+8+i<tr.height tt by omega)
    (hw (s+8+i) (by omega) (by omega)) hi hsel' (x:=nextIndex) (by simp) hnext
  rw [hb1,hb2,empty_register_constant hL hfit hw hs hem i hi (s+i) (by omega) (by omega),
    empty_register_constant hL hfit hw hs hem i hi (s+8+i) (by omega) (by omega)]

/-- Once physical bytes are identified with native bytes, empty mode satisfies
exactly the native queue-empty predicate. No new byte or length cap is assumed. -/
theorem empty_queue_bytes (bs : NearSpec.Bytes) (hlen : bs.length=n)
    (hbytes : ∀ i, i<n → (bs.getD i 0).toNat=cv tr tt (s+i) byte) :
    EmptyQueue (some bs) := by
  have hn := empty_row_count hL hfit hw hs hem
  have hb : bs.length=16 := by omega
  refine ⟨hb,?_⟩
  apply List.ext_getElem (by simp [hb])
  intro i hi hj
  have hi8 : i<8 := by simpa [hb] using hi
  rw [List.getElem_take,List.getElem_drop]
  apply UInt8.toNat_inj.mp
  have h1 := hbytes i (by omega)
  have h2 := hbytes (8+i) (by omega)
  have he := congrArg Fp.toNat (empty_words_equal hL hfit hw hs hem i hi8)
  simp only [cv] at h1 h2
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show i<bs.length by omega),
    List.getElem?_eq_getElem (show 8+i<bs.length by omega),Option.getD_some] at h1 h2
  rw [h1,h2]
  simpa only [Nat.add_assoc] using he

end ZkFormal.NearV3.Qv.Extract.Parser
