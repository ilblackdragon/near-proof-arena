import ZkFormal.NearV3.Qv.Extract.EntryCounter

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable (hm : tr.cell tt s mBuffer=1)
include hL hfit hw hs hm

/-- Header registers persist until the fourth header byte. -/
theorem buffered_header_register (i : Nat) (hi : i<8) :
    ∀ q, s≤q → q<s+4 → tr.cell tt q (reg i)=tr.cell tt s (reg i) := by
  have rows := buffered_header_rows hL hfit hw hs hm
  have hmin := (rows 3 (by omega)).1
  apply const_of
  intro q hq hqb
  obtain ⟨_,hh,hsel⟩ := rows (q-s) (by omega)
  have he : s+(q-s)=q := by omega
  rw [he] at hh hsel
  have hrow : q<tr.height tt := by omega
  have hwalk := hw q hq (by omega)
  have hx := phase_exclusive hL hrow hwalk (x:=header) (by simp [phases]) hh
  have hn := hx.2 nextIndex (by simp [phases]) (by decide)
  have hraw := hx.2 mRaw (by simp [phases]) (by decide)
  have h3 := selector_exclusive hL hrow hwalk hx.1 hraw (by omega) hsel 3 (by omega) (by omega)
  have hnot := hs.2.2.2.2.2 q hq (by omega)
  have hl : tr.cell tt q vl=0 := by
    rcases isBool hL hrow hwalk (x:=vl) (by simp) with hl|hl
    · exact hl
    · simp [isOne,hl] at hnot
  have hc := (record_continue hL hfit hw hs q hq (by omega) hl).2
  apply register_carry hL hrow hwalk (by omega) hc ?_ ?_ i hi
  · simp only [headerEnd,eval_mul,eval_c,h3]; grind
  · simp only [entryEnd,wordEnd,eval_mul,eval_c,hn]; grind

theorem buffered_header_byte (i : Nat) (hi : i<4) :
    tr.cell tt (s+i) byte=tr.cell tt s (reg i) := by
  obtain ⟨hb,hh,hsel⟩ := buffered_header_rows hL hfit hw hs hm i hi
  have hbyte := selected_word_byte hL (show s+i<tr.height tt by omega)
    (hw (s+i) (by omega) (by omega)) (by omega) hsel (x:=header) (by simp) hh
  rw [hbyte,buffered_header_register hL hfit hw hs hm i (by omega) (s+i) (by omega) (by omega)]

theorem buffered_header_high_zero : tr.cell tt (s+3) byte=0 := by
  obtain ⟨hb,hh,_⟩ := buffered_header_rows hL hfit hw hs hm 0 (by omega)
  simp only [Nat.add_zero] at hh
  have h := con hL (show s<tr.height tt by omega) (hw s (by omega) (by omega))
    (e:=.mul (c header) (c (reg 3))) (by simp [constraints])
  simp only [eval_mul,eval_c,hh] at h
  rw [buffered_header_byte hL hfit hw hs hm 3 (by omega)]
  grind

/-- The count is the little-endian value of the actual header bytes; its high byte is zero. -/
theorem buffered_header_count_field :
    tr.cell tt s count=tr.cell tt s byte+256*tr.cell tt (s+1) byte+65536*tr.cell tt (s+2) byte := by
  obtain ⟨hb,hh,hsel⟩ := buffered_header_rows hL hfit hw hs hm 3 (by omega)
  have h := con hL (show s+3<tr.height tt by omega) (hw (s+3) (by omega) (by omega))
    (e:=eqG headerEnd (c count) counterBytes) (by simp [constraints])
  have hcount := metadata hL hfit hw hs (x:=count) (by simp) (s+3) (by omega) (by omega)
  have h0 := buffered_header_register hL hfit hw hs hm 0 (by omega) (s+3) (by omega) (by omega)
  have h1 := buffered_header_register hL hfit hw hs hm 1 (by omega) (s+3) (by omega) (by omega)
  have h2 := buffered_header_register hL hfit hw hs hm 2 (by omega) (s+3) (by omega) (by omega)
  have h3 := buffered_header_register hL hfit hw hs hm 3 (by omega) (s+3) (by omega) (by omega)
  have b0 := buffered_header_byte hL hfit hw hs hm 0 (by omega)
  have b1 := buffered_header_byte hL hfit hw hs hm 1 (by omega)
  have b2 := buffered_header_byte hL hfit hw hs hm 2 (by omega)
  have b3 := buffered_header_byte hL hfit hw hs hm 3 (by omega)
  have bz := buffered_header_high_zero hL hfit hw hs hm
  simp only [Nat.add_zero] at b0
  simp [eval_eqG,headerEnd,eval_mul,eval_c,hh,hsel,counterBytes,List.range_succ,
    List.map_cons,List.map_nil,sum,smul] at h
  rw [hcount,h0,h1,h2,h3,←b0,←b1,←b2,←b3,bz] at h
  change (1:Fp)*1*(tr.cell tt s count-(1*tr.cell tt s byte+
    (256*tr.cell tt (s+1) byte+(65536*tr.cell tt (s+2) byte+(16777216*0+0)))))=0 at h
  grind

/-- Canonical byte bounds prevent any field alias in the decoded header count. -/
theorem buffered_header_count_nat
    (hb : ∀ i, i<3 → cv tr tt (s+i) byte<256) :
    cv tr tt s count=cv tr tt s byte+256*cv tr tt (s+1) byte+65536*cv tr tt (s+2) byte := by
  have h := buffered_header_count_field hL hfit hw hs hm
  have hdecode : tr.cell tt s count=
      ((cv tr tt s byte+256*cv tr tt (s+1) byte+65536*cv tr tt (s+2) byte:Nat):Fp) := by
    simp only [natCast_add,natCast_mul]
    change tr.cell tt s count=Fp.ofNat (cv tr tt s byte)+
      256*Fp.ofNat (cv tr tt (s+1) byte)+65536*Fp.ofNat (cv tr tt (s+2) byte)
    simpa only [cv,Fp.ofNat_toNat] using h
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  simp only [Nat.add_zero] at h0
  have hbound : cv tr tt s byte+256*cv tr tt (s+1) byte+65536*cv tr tt (s+2) byte<P := by
    unfold P; omega
  change (tr.cell tt s count).toNat=_
  rw [hdecode,toNat_natCast,Nat.mod_eq_of_lt hbound]

end ZkFormal.NearV3.Qv.Extract.Parser
