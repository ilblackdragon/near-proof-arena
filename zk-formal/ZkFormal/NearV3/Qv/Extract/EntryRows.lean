import ZkFormal.NearV3.Qv.Extract.EntryClock

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

/-- Every buffered body word contains its full eight bytes within the record. -/
theorem buffered_word_rows {r x : Nat} (hr : s≤r) (hb : r<s+n)
    (hx : x∈[shard,firstIndex,nextIndex]) (hp : tr.cell tt r x=1)
    (hz : tr.cell tt r (sel 0)=1) :
    ∀ i, i<8 → r+i<s+n ∧ tr.cell tt (r+i) x=1 ∧ tr.cell tt (r+i) (sel i)=1 := by
  intro i
  induction i with
  | zero => intro _; simpa using And.intro hb (And.intro hp hz)
  | succ i ih =>
    intro hi
    obtain ⟨hb',hp',hsel⟩ := ih (by omega)
    have hr' : r+i<tr.height tt := by omega
    have hw' := hw (r+i) (by omega) hb'
    have hm' : tr.cell tt (r+i) mBuffer=1 := by
      rw [metadata hL hfit hw hs (x:=mBuffer) (by simp) (r+i) (by omega) hb',hm]
    have hl : tr.cell tt (r+i) vl=0 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx|hx|hx
      · subst x; exact buffered_body_not_last hL hr' hw' hm' (by simp) hp'
      · subst x; exact buffered_body_not_last hL hr' hw' hm' (by simp) hp'
      · subst x; exact next_word_not_last hL hr' hw' hp' i (by omega) hsel
    obtain ⟨hn,hc⟩ := record_continue hL hfit hw hs (r+i) (by omega) hb' hl
    have step : tr.cell tt (r+i+1) x=1 ∧ tr.cell tt (r+i+1) (sel (i+1))=1 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx|hx|hx
      · subst x; exact shard_word_advance hL hr' hw' (by omega) hc hp' i (by omega) hsel
      · subst x; exact first_word_advance hL hr' hw' (by omega) hc hp' i (by omega) hsel
      · subst x; exact next_word_advance hL hr' hw' (by omega) hc hp' i (by omega) hsel
    exact ⟨by omega,by simpa only [Nat.add_assoc] using step.1,
      by simpa only [Nat.add_assoc] using step.2⟩

/-- The shard and first-index word boundaries cannot end a buffered record. -/
theorem buffered_word_boundary {r x : Nat} (hr : s≤r) (hb : r<s+n)
    (hx : x∈[shard,firstIndex]) (hp : tr.cell tt r x=1)
    (hz : tr.cell tt r (sel 7)=1) :
    r+1<s+n ∧ tr.cell tt (r+1) (if x=shard then firstIndex else nextIndex)=1 ∧
      tr.cell tt (r+1) (sel 0)=1 := by
  have hr' : r<tr.height tt := by omega
  have hw' := hw r hr hb
  have hm' : tr.cell tt r mBuffer=1 := by
    rw [metadata hL hfit hw hs (x:=mBuffer) (by simp) r hr hb,hm]
  have hl := buffered_body_not_last hL hr' hw' hm' hx hp
  obtain ⟨hn,hc⟩ := record_continue hL hfit hw hs r hr hb hl
  refine ⟨hn,?_⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx
  · subst x
    simpa using shard_word_end hL hr' hw' (by omega) hc hp hz
  · subst x
    simpa [show firstIndex≠shard by decide] using first_word_end hL hr' hw' (by omega) hc hp hz

/-- A buffered entry is exactly three complete words: shard, first index, next index. -/
theorem buffered_entry_rows {r : Nat} (hr : s≤r) (hb : r<s+n)
    (hp : tr.cell tt r shard=1) (hz : tr.cell tt r (sel 0)=1) :
    r+23<s+n ∧
    (∀ i, i<8 → tr.cell tt (r+i) shard=1 ∧ tr.cell tt (r+i) (sel i)=1) ∧
    (∀ i, i<8 → tr.cell tt (r+8+i) firstIndex=1 ∧ tr.cell tt (r+8+i) (sel i)=1) ∧
    (∀ i, i<8 → tr.cell tt (r+16+i) nextIndex=1 ∧ tr.cell tt (r+16+i) (sel i)=1) := by
  have hsh := buffered_word_rows hL hfit hw hs hm hr hb (by simp) hp hz
  obtain ⟨h7,hp7,hz7⟩ := hsh 7 (by omega)
  have b1 := buffered_word_boundary hL hfit hw hs hm (r:=r+7) (by omega) h7 (by simp) hp7 hz7
  simp only [Nat.add_assoc,ite_true] at b1
  have hfirst := buffered_word_rows hL hfit hw hs hm (r:=r+8) (by omega) b1.1 (by simp) b1.2.1 b1.2.2
  obtain ⟨h15,hp15,hz15⟩ := hfirst 7 (by omega)
  have b2 := buffered_word_boundary hL hfit hw hs hm (r:=r+8+7) (by omega) h15 (by simp) hp15 hz15
  simp only [Nat.add_assoc,show firstIndex≠shard by decide,ite_false] at b2
  have hnext := buffered_word_rows hL hfit hw hs hm (r:=r+16) (by omega) b2.1 (by simp) b2.2.1 b2.2.2
  refine ⟨by have := (hnext 7 (by omega)).1; omega,?_,?_,?_⟩
  · intro i hi; exact (hsh i hi).2
  · intro i hi; exact (hfirst i hi).2
  · intro i hi; exact (hnext i hi).2

/-- After 24 bytes an entry either terminates at the declared count or starts the next entry. -/
theorem buffered_entry_exit {r : Nat} (hr : s≤r) (hb : r<s+n)
    (hp : tr.cell tt r shard=1) (hz : tr.cell tt r (sel 0)=1) :
    (r+24=s+n ∧ tr.cell tt (r+23) entry+1=tr.cell tt s count) ∨
    (r+24<s+n ∧ tr.cell tt (r+24) shard=1 ∧ tr.cell tt (r+24) (sel 0)=1 ∧
      tr.cell tt (r+24) entry=tr.cell tt (r+23) entry+1) := by
  have rows := buffered_entry_rows hL hfit hw hs hm hr hb hp hz
  have hb' := rows.1
  have last := rows.2.2.2 7 (by omega)
  have hp' : tr.cell tt (r+23) nextIndex=1 := by simpa only [Nat.add_assoc] using last.1
  have hz' : tr.cell tt (r+23) (sel 7)=1 := by simpa only [Nat.add_assoc] using last.2
  have hr' : r+23<tr.height tt := by omega
  have hw' := hw (r+23) (by omega) hb'
  by_cases hend : r+24=s+n
  · left
    have he : s+n-1=r+23 := by omega
    have hl : tr.cell tt (r+23) vl=1 := by
      simpa only [isOne,decide_eq_true_eq,he] using hs.2.2.1
    have hm' : tr.cell tt (r+23) mBuffer=1 := by
      rw [metadata hL hfit hw hs (x:=mBuffer) (by simp) (r+23) (by omega) hb',hm]
    have hc := buffered_entry_last hL hr' hw' hm' hp' hl
    rw [metadata hL hfit hw hs (x:=count) (by simp) (r+23) (by omega) hb'] at hc
    exact ⟨hend,hc⟩
  · right
    have hnot := hs.2.2.2.2.2 (r+23) (by omega) (by omega)
    have hl : tr.cell tt (r+23) vl=0 := by
      rcases isBool hL hr' hw' (x:=vl) (by simp) with hl|hl
      · exact hl
      · simp [isOne,hl] at hnot
    have hc := (record_continue hL hfit hw hs (r+23) (by omega) hb' hl).2
    have step := next_word_end hL hr' hw' (by omega) hc hp' hz'
    exact ⟨by omega,by simpa only [Nat.add_assoc] using step⟩

end ZkFormal.NearV3.Qv.Extract.Parser
