import ZkFormal.NearV3.Qv.Extract.ParserClock
import ZkFormal.NearV3.Qv.Extract.ParserRecord

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s n : Nat} (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
include hL hfit hw hs

theorem record_continue (r : Nat) (hr : s≤r) (hb : r<s+n) (hl : tr.cell tt r vl=0) :
    r+1<s+n ∧ tr.cell tt r cont=1 := by
  have hp := hs.1
  have hnext : r+1<s+n := by
    by_cases hn : r+1<s+n
    · exact hn
    exfalso
    have he : r=s+n-1 := by omega
    have hh : tr.cell tt (s+n-1) vl=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
    rw [←he,hl] at hh
    exact (by decide : (0:Fp)≠1) hh
  have ha : tr.cell tt r act=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr hb
  have hc := continuation hL (show r<tr.height tt by omega) (hw r hr hb)
  rw [ha,hl] at hc
  exact ⟨hnext,by grind⟩

theorem empty_first_rows (hem : tr.cell tt s mEmpty=1) :
    ∀ i, i<8 → i<n ∧ tr.cell tt (s+i) firstIndex=1 ∧ tr.cell tt (s+i) (sel i)=1 := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hp := hs.1
    have hf : tr.cell tt s vf=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.1
    have ha := marker hL (show s<tr.height tt by omega) (hw s (by omega) (by omega)) (Or.inl rfl) hf
    have hm := mode_cases hL (show s<tr.height tt by omega) (hw s (by omega) (by omega)) ha
    have hraw : tr.cell tt s mRaw=0 := by rcases hm with hm | hm | hm <;> grind
    have hstart := start_state hL (show s<tr.height tt by omega) (hw s (by omega) (by omega)) hf
    simp only [Nat.add_zero]
    exact ⟨hp,by rw [hstart.2.2.1,hem],by rw [hstart.2.2.2,hraw]; grind⟩
  | succ i ih =>
    intro hi
    obtain ⟨hin,hfirst,hsel⟩ := ih (by omega)
    have hr : s+i<tr.height tt := by omega
    have hwalk := hw (s+i) (by omega) (by omega)
    have hm := metadata hL hfit hw hs (x:=mEmpty) (by simp) (s+i) (by omega) (by omega)
    rw [hem] at hm
    have hp := phase_exclusive hL hr hwalk (x:=firstIndex) (by simp [phases]) hfirst
    have hn := hp.2 nextIndex (by simp [phases]) (by decide)
    have hl := empty_last hL hr hwalk hm
    have hl0 : tr.cell tt (s+i) vl=0 := by rw [hn] at hl; grind
    obtain ⟨hnext,hc⟩ := record_continue hL hfit hw hs (s+i) (by omega) (by omega) hl0
    have hstep := first_word_advance hL hr hwalk (by omega) hc hfirst i (by omega) hsel
    refine ⟨by omega,?_,?_⟩ <;> simpa only [Nat.add_assoc] using (by first | exact hstep.1 | exact hstep.2)

theorem empty_second_rows (hem : tr.cell tt s mEmpty=1) :
    ∀ i, i<8 → 8+i<n ∧ tr.cell tt (s+8+i) nextIndex=1 ∧ tr.cell tt (s+8+i) (sel i)=1 := by
  intro i
  induction i with
  | zero =>
    intro hi
    obtain ⟨hin,hfirst,hsel⟩ := empty_first_rows hL hfit hw hs hem 7 (by omega)
    have hr : s+7<tr.height tt := by omega
    have hwalk := hw (s+7) (by omega) (by omega)
    have hm := metadata hL hfit hw hs (x:=mEmpty) (by simp) (s+7) (by omega) (by omega)
    rw [hem] at hm
    have hp := phase_exclusive hL hr hwalk (x:=firstIndex) (by simp [phases]) hfirst
    have hn := hp.2 nextIndex (by simp [phases]) (by decide)
    have hl := empty_last hL hr hwalk hm
    have hl0 : tr.cell tt (s+7) vl=0 := by rw [hn] at hl; grind
    obtain ⟨hnext,hc⟩ := record_continue hL hfit hw hs (s+7) (by omega) (by omega) hl0
    have hstep := first_word_end hL hr hwalk (by omega) hc hfirst hsel
    refine ⟨by omega,?_,?_⟩ <;> simpa only [Nat.add_assoc,Nat.add_zero] using (by first | exact hstep.1 | exact hstep.2)
  | succ i ih =>
    intro hi
    obtain ⟨hin,hnext,hsel⟩ := ih (by omega)
    have hr : s+8+i<tr.height tt := by omega
    have hwalk := hw (s+8+i) (by omega) (by omega)
    have hm := metadata hL hfit hw hs (x:=mEmpty) (by simp) (s+8+i) (by omega) (by omega)
    rw [hem] at hm
    have hp := phase_exclusive hL hr hwalk (x:=nextIndex) (by simp [phases]) hnext
    have hraw := hp.2 mRaw (by simp [phases]) (by decide)
    have hheader := hp.2 header (by simp [phases]) (by decide)
    have h7 := selector_exclusive hL hr hwalk hp.1 hraw (by omega) hsel 7 (by omega) (by omega)
    have hl := empty_last hL hr hwalk hm
    have hl0 : tr.cell tt (s+8+i) vl=0 := by rw [h7] at hl; grind
    obtain ⟨hbound,hc⟩ := record_continue hL hfit hw hs (s+8+i) (by omega) (by omega) hl0
    have hphase := (index_phase_step hL hr hwalk (by omega) hc).2
    have hclock := clock_shift hL hr hwalk (by omega) hc i (by omega)
    rw [hnext,h7] at hphase
    rw [hsel,hheader] at hclock
    have hp1 : tr.cell tt (s+8+i+1) nextIndex=1 := by grind
    have hs1 : tr.cell tt (s+8+i+1) (sel (i+1))=1 := by split at hclock <;> grind
    exact ⟨by omega,by simpa only [Nat.add_assoc] using hp1,by simpa only [Nat.add_assoc] using hs1⟩

theorem empty_row_count (hem : tr.cell tt s mEmpty=1) : n=16 := by
  obtain ⟨hi,hnext,hsel⟩ := empty_second_rows hL hfit hw hs hem 7 (by omega)
  have hm := metadata hL hfit hw hs (x:=mEmpty) (by simp) (s+8+7) (by omega) (by omega)
  rw [hem] at hm
  have hl := empty_last hL (show s+8+7<tr.height tt by omega) (hw _ (by omega) (by omega)) hm
  have hl1 : tr.cell tt (s+8+7) vl=1 := by rw [hnext,hsel] at hl; grind
  by_cases he : n=16
  · exact he
  exfalso
  have hz := hs.2.2.2.2.2 (s+8+7) (by omega) (by omega)
  simp [isOne,hl1] at hz

end ZkFormal.NearV3.Qv.Extract.Parser
