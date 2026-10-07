import ZkFormal.NearV3.Qv.Extract.ParserWords

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hr : r<tr.height tt) (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
include hL hr hw

theorem clock_zero (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1) :
    tr.cell tt (r+1) (sel 0)=tr.cell tt r (sel 7)+tr.cell tt r header*tr.cell tt r (sel 3) := by
  have h := con hL hr hw (e:=eqG (c cont) (n (sel 0)) (.add wordEnd headerEnd)) (by simp [constraints])
  simp only [eval_eqG,eval_n,eval_c,eval_add,wordEnd,headerEnd,eval_mul,hc,Nat.mod_eq_of_lt hn] at h
  grind

theorem clock_shift (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (i : Nat) (hi : i<7) :
    tr.cell tt (r+1) (sel (i+1))=
      if i=3 then tr.cell tt r (sel i)*(1-tr.cell tt r header) else tr.cell tt r (sel i) := by
  have hm := List.mem_map_of_mem (f:=fun i => eqG (c cont) (n (sel (i+1)))
    (if i=3 then .mul (c (sel i)) (Dsl.not (c header)) else c (sel i))) (List.mem_range.mpr hi)
  have h := con hL hr hw (e:=eqG (c cont) (n (sel (i+1)))
    (if i=3 then .mul (c (sel i)) (Dsl.not (c header)) else c (sel i)))
    (by unfold constraints; simp only [List.mem_append,hm,true_or,or_true])
  by_cases he : i=3 <;>
    simp only [he,ite_true,ite_false,eval_eqG,eval_n,eval_c,eval_mul,eval_not,hc,Nat.mod_eq_of_lt hn] at * <;> grind

theorem index_phase_step (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1) :
    tr.cell tt (r+1) firstIndex=tr.cell tt r firstIndex*(1-tr.cell tt r (sel 7))+
      tr.cell tt r shard*tr.cell tt r (sel 7) ∧
    tr.cell tt (r+1) nextIndex=tr.cell tt r nextIndex*(1-tr.cell tt r (sel 7))+
      tr.cell tt r firstIndex*tr.cell tt r (sel 7) := by
  have h1 := con hL hr hw (e:=eqG (c cont) (n firstIndex)
    (.add (.mul (c firstIndex) (Dsl.not wordEnd)) (.mul (c shard) wordEnd))) (by simp [constraints])
  have h2 := con hL hr hw (e:=eqG (c cont) (n nextIndex)
    (.add (.mul (c nextIndex) (Dsl.not wordEnd)) (.mul (c firstIndex) wordEnd))) (by simp [constraints])
  simp only [eval_eqG,eval_n,eval_c,eval_add,eval_mul,eval_not,wordEnd,hc,Nat.mod_eq_of_lt hn] at h1 h2
  grind

theorem empty_last (hm : tr.cell tt r mEmpty=1) :
    tr.cell tt r vl=tr.cell tt r nextIndex*tr.cell tt r (sel 7) := by
  have h := con hL hr hw (e:=eqG (c mEmpty) (c vl) entryEnd) (by simp [constraints])
  simp only [eval_eqG,eval_c,entryEnd,wordEnd,eval_mul,hm] at h
  grind

/-- Within the first eight-byte index word the clock advances deterministically. -/
theorem first_word_advance (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hf : tr.cell tt r firstIndex=1) (i : Nat) (hi : i<7)
    (hsel : tr.cell tt r (sel i)=1) :
    tr.cell tt (r+1) firstIndex=1 ∧ tr.cell tt (r+1) (sel (i+1))=1 := by
  have hp := phase_exclusive hL hr hw (x:=firstIndex) (by simp [phases]) hf
  have hh := hp.2 header (by simp [phases]) (by decide)
  have hm := hp.2 mRaw (by simp [phases]) (by decide)
  have h7 := selector_exclusive hL hr hw hp.1 hm (by omega) hsel 7 (by omega) (by omega)
  have hphase := (index_phase_step hL hr hw hn hc).1
  have hclock := clock_shift hL hr hw hn hc i hi
  rw [hf,h7] at hphase
  rw [hsel,hh] at hclock
  constructor
  · grind
  · split at hclock <;> grind

/-- Byte seven transitions from the first index to the last index and resets the clock. -/
theorem first_word_end (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hf : tr.cell tt r firstIndex=1) (hsel : tr.cell tt r (sel 7)=1) :
    tr.cell tt (r+1) nextIndex=1 ∧ tr.cell tt (r+1) (sel 0)=1 := by
  have hp := phase_exclusive hL hr hw (x:=firstIndex) (by simp [phases]) hf
  have hh := hp.2 header (by simp [phases]) (by decide)
  have hphase := (index_phase_step hL hr hw hn hc).2
  have hclock := clock_zero hL hr hw hn hc
  rw [hf,hsel] at hphase
  rw [hsel,hh] at hclock
  constructor <;> grind

end ZkFormal.NearV3.Qv.Extract.Parser
