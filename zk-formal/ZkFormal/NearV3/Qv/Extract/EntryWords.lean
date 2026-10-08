import ZkFormal.NearV3.Qv.Extract.EntryRows

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n r : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ q, s≤q → q<s+n → tr.cell tt q Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable (hm : tr.cell tt s mBuffer=1)
variable (hr : s≤r) (hb : r<s+n) (hp : tr.cell tt r shard=1) (hz : tr.cell tt r (sel 0)=1)
include hL hfit hw hs hm hr hb hp hz

/-- No register reset occurs between an entry's first and next index words. -/
theorem buffered_register_constant (i : Nat) (hi : i<8) :
    ∀ q, r+8≤q → q<r+8+16 → tr.cell tt q (reg i)=tr.cell tt (r+8) (reg i) := by
  have rows := buffered_entry_rows hL hfit hw hs hm hr hb hp hz
  apply const_of
  intro q hq hqb
  have hbq : q<s+n := by omega
  have hrow : q<tr.height tt := by omega
  have hwalk := hw q (by omega) hbq
  have hphase : tr.cell tt q firstIndex=1 ∨
      (tr.cell tt q nextIndex=1 ∧ tr.cell tt q (sel 7)=0) := by
    by_cases hf : q<r+16
    · left
      have hh := (rows.2.2.1 (q-(r+8)) (by omega)).1
      have he : r+8+(q-(r+8))=q := by omega
      simpa only [he] using hh
    · right
      have hh := rows.2.2.2 (q-(r+16)) (by omega)
      have he : r+16+(q-(r+16))=q := by omega
      rw [he] at hh
      have hx := phase_exclusive hL hrow hwalk (x:=nextIndex) (by simp [phases]) hh.1
      have hraw := hx.2 mRaw (by simp [phases]) (by decide)
      have h7 := selector_exclusive hL hrow hwalk hx.1 hraw (by omega) hh.2 7 (by omega) (by omega)
      exact ⟨hh.1,h7⟩
  have hends : headerEnd.eval tr tt q pub=0 ∧ entryEnd.eval tr tt q pub=0 := by
    rcases hphase with hf|⟨hn,h7⟩
    · have hx := phase_exclusive hL hrow hwalk (x:=firstIndex) (by simp [phases]) hf
      have hh := hx.2 header (by simp [phases]) (by decide)
      have hn := hx.2 nextIndex (by simp [phases]) (by decide)
      simp only [headerEnd,entryEnd,wordEnd,eval_mul,eval_c,hh,hn]
      constructor <;> grind
    · have hx := phase_exclusive hL hrow hwalk (x:=nextIndex) (by simp [phases]) hn
      have hh := hx.2 header (by simp [phases]) (by decide)
      simp only [headerEnd,entryEnd,wordEnd,eval_mul,eval_c,hh,h7]
      constructor <;> grind
  have hnot := hs.2.2.2.2.2 q (by omega) (by omega)
  have hl : tr.cell tt q vl=0 := by
    rcases isBool hL hrow hwalk (x:=vl) (by simp) with hl|hl
    · exact hl
    · simp [isOne,hl] at hnot
  have hc := (record_continue hL hfit hw hs q (by omega) hbq hl).2
  exact register_carry hL hrow hwalk (by omega) hc hends.1 hends.2 i hi

/-- Each buffered entry's two index words are byte-for-byte equal. -/
theorem buffered_words_equal (i : Nat) (hi : i<8) :
    tr.cell tt (r+8+i) byte=tr.cell tt (r+16+i) byte := by
  have rows := buffered_entry_rows hL hfit hw hs hm hr hb hp hz
  have hf := rows.2.2.1 i hi
  have hn := rows.2.2.2 i hi
  have b1 := selected_word_byte hL (show r+8+i<tr.height tt by omega)
    (hw (r+8+i) (by omega) (by omega)) hi hf.2 (x:=firstIndex) (by simp) hf.1
  have b2 := selected_word_byte hL (show r+16+i<tr.height tt by omega)
    (hw (r+16+i) (by omega) (by omega)) hi hn.2 (x:=nextIndex) (by simp) hn.1
  rw [b1,b2,buffered_register_constant hL hfit hw hs hm hr hb hp hz i hi (r+8+i) (by omega) (by omega),
    buffered_register_constant hL hfit hw hs hm hr hb hp hz i hi (r+16+i) (by omega) (by omega)]

end ZkFormal.NearV3.Qv.Extract.Parser
