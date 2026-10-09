import ZkFormal.NearV3.Qv.Extract.EmptyRows

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hr : r<tr.height tt) (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
include hL hr hw

theorem header_last (hh : tr.cell tt r header=1) (hl : tr.cell tt r vl=1) :
    tr.cell tt r (sel 3)=1 ∧ tr.cell tt r count=0 := by
  have h1 := con hL hr hw (e:=mul3 (c vl) (c header) (Dsl.not (c (sel 3)))) (by simp [constraints])
  have h2 := con hL hr hw (e:=mul3 (c vl) (c header) (c count)) (by simp [constraints])
  simp only [eval_mul3,eval_c,eval_not,hh,hl] at h1 h2
  grind

theorem header_advance (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hh : tr.cell tt r header=1) (i : Nat) (hi : i<3) (hsel : tr.cell tt r (sel i)=1) :
    tr.cell tt (r+1) header=1 ∧ tr.cell tt (r+1) (sel (i+1))=1 := by
  have hp := phase_exclusive hL hr hw (x:=header) (by simp [phases]) hh
  have hraw := hp.2 mRaw (by simp [phases]) (by decide)
  have h3 := selector_exclusive hL hr hw hp.1 hraw (by omega) hsel 3 (by omega) (by omega)
  have hphase := con hL hr hw (e:=eqG (c cont) (n header) (.mul (c header) (Dsl.not (c (sel 3)))))
    (by simp [constraints])
  simp only [eval_eqG,eval_n,eval_c,eval_mul,eval_not,hc,hh,h3,Nat.mod_eq_of_lt hn] at hphase
  have hclock := clock_shift hL hr hw hn hc i (by omega)
  simp only [if_neg (show i≠3 by omega),hsel] at hclock
  exact ⟨by grind,hclock⟩

theorem header_to_shard (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hh : tr.cell tt r header=1) (hsel : tr.cell tt r (sel 3)=1) :
    tr.cell tt (r+1) shard=1 ∧ tr.cell tt (r+1) (sel 0)=1 := by
  have hp := phase_exclusive hL hr hw (x:=header) (by simp [phases]) hh
  have hraw := hp.2 mRaw (by simp [phases]) (by decide)
  have hsh := hp.2 shard (by simp [phases]) (by decide)
  have hnext := hp.2 nextIndex (by simp [phases]) (by decide)
  have h7 := selector_exclusive hL hr hw hp.1 hraw (by decide) hsel 7 (by decide) (by decide)
  have hphase := con hL hr hw (e:=eqG (c cont) (n shard)
    (sum [.mul (c shard) (Dsl.not wordEnd),headerEnd,entryEnd])) (by simp [constraints])
  simp [eval_eqG,eval_n,eval_c,eval_mul,eval_not,wordEnd,headerEnd,entryEnd,
    hc,hh,hsel,hsh,hnext,h7,Nat.mod_eq_of_lt hn] at hphase
  have hclock := clock_zero hL hr hw hn hc
  rw [h7,hh,hsel] at hclock
  constructor <;> grind

omit hr hw in
theorem buffered_header_rows {s n : Nat} (hfit : s+n≤tr.height tt)
    (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
    (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
    (hm : tr.cell tt s mBuffer=1) :
    ∀ i, i<4 → i<n ∧ tr.cell tt (s+i) header=1 ∧ tr.cell tt (s+i) (sel i)=1 := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hp := hs.1
    have hf : tr.cell tt s vf=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.1
    have hr : s<tr.height tt := by omega
    have hwalk := hw s (by omega) (by omega)
    have ha := marker hL hr hwalk (Or.inl rfl) hf
    have hmodes := mode_cases hL hr hwalk ha
    have hraw : tr.cell tt s mRaw=0 := by rcases hmodes with hmodes|hmodes|hmodes <;> grind
    have hstart := start_state hL hr hwalk hf
    simp only [Nat.add_zero]
    exact ⟨hp,by rw [hstart.2.1,hm],by rw [hstart.2.2.2,hraw]; grind⟩
  | succ i ih =>
    intro hi
    obtain ⟨hin,hh,hsel⟩ := ih (by omega)
    have hr : s+i<tr.height tt := by omega
    have hwalk := hw (s+i) (by omega) (by omega)
    have hp := phase_exclusive hL hr hwalk (x:=header) (by simp [phases]) hh
    have hraw := hp.2 mRaw (by simp [phases]) (by decide)
    have h3 := selector_exclusive hL hr hwalk hp.1 hraw (by omega) hsel 3 (by omega) (by omega)
    have hl : tr.cell tt (s+i) vl=0 := by
      rcases isBool hL hr hwalk (x:=vl) (by simp) with hl|hl
      · exact hl
      · have he := (header_last hL hr hwalk hh hl).1
        rw [h3] at he
        exact False.elim ((by decide : (0:Fp)≠1) he)
    obtain ⟨hn,hc⟩ := record_continue hL hfit hw hs (s+i) (by omega) (by omega) hl
    have hstep := header_advance hL hr hwalk (by omega) hc hh i (by omega) hsel
    exact ⟨by omega,by simpa only [Nat.add_assoc] using hstep.1,by simpa only [Nat.add_assoc] using hstep.2⟩

omit hr hw in
theorem buffered_header_exit {s n : Nat} (hfit : s+n≤tr.height tt)
    (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
    (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
    (hm : tr.cell tt s mBuffer=1) :
    (n=4 ∧ tr.cell tt s count=0) ∨
      (4<n ∧ tr.cell tt (s+4) shard=1 ∧ tr.cell tt (s+4) (sel 0)=1) := by
  obtain ⟨hin,hh,hsel⟩ := buffered_header_rows hL hfit hw hs hm 3 (by omega)
  have hr : s+3<tr.height tt := by omega
  have hwalk := hw (s+3) (by omega) (by omega)
  by_cases hn : n=4
  · left
    have he : s+n-1=s+3 := by omega
    have hl : tr.cell tt (s+3) vl=1 := by
      simpa only [isOne,decide_eq_true_eq,he] using hs.2.2.1
    have hc := (header_last hL hr hwalk hh hl).2
    have hmeta := metadata hL hfit hw hs (x:=count) (by simp) (s+3) (by omega) (by omega)
    exact ⟨hn,by rw [←hmeta,hc]⟩
  · right
    have hnot := hs.2.2.2.2.2 (s+3) (by omega) (by omega)
    have hl : tr.cell tt (s+3) vl=0 := by
      rcases isBool hL hr hwalk (x:=vl) (by simp) with hl|hl
      · exact hl
      · simp [isOne,hl] at hnot
    have hc := (record_continue hL hfit hw hs (s+3) (by omega) (by omega) hl).2
    have hstep := header_to_shard hL hr hwalk (by omega) hc hh hsel
    exact ⟨by omega,by simpa only [Nat.add_assoc] using hstep.1,
      by simpa only [Nat.add_assoc] using hstep.2⟩

end ZkFormal.NearV3.Qv.Extract.Parser
