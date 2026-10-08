import ZkFormal.NearV3.Qv.Extract.BufferedHeader

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hr : r<tr.height tt) (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
include hL hr hw

/-- Buffered records cannot terminate in their shard or first-index word. -/
theorem buffered_body_not_last (hm : tr.cell tt r mBuffer=1)
    {x : Nat} (hx : x∈[shard,firstIndex]) (hp : tr.cell tt r x=1) :
    tr.cell tt r vl=0 := by
  have he := phase_exclusive hL hr hw (x:=x) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl <;> simp [phases]) hp
  have hh := he.2 header (by simp [phases]) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl <;> decide)
  have hn := he.2 nextIndex (by simp [phases]) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl <;> decide)
  have h := con hL hr hw (e:=mul3 (c vl) (c mBuffer)
    (sub (.add (c header) (c nextIndex)) (k 1))) (by simp [constraints])
  simp only [eval_mul3,eval_c,eval_sub,eval_add,eval_k,hm,hh,hn] at h
  grind

/-- A last-index word can terminate only on its eighth byte. -/
theorem next_word_not_last (hp : tr.cell tt r nextIndex=1)
    (i : Nat) (hi : i<7) (hsel : tr.cell tt r (sel i)=1) :
    tr.cell tt r vl=0 := by
  have he := phase_exclusive hL hr hw (x:=nextIndex) (by simp [phases]) hp
  have hm := he.2 mRaw (by simp [phases]) (by decide)
  have h7 := selector_exclusive hL hr hw he.1 hm (by omega) hsel 7 (by omega) (by omega)
  have h := con hL hr hw (e:=mul3 (c vl) (c nextIndex) (Dsl.not wordEnd)) (by simp [constraints])
  simp only [eval_mul3,eval_c,eval_not,wordEnd,hp,h7] at h
  grind

theorem shard_word_advance (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hp : tr.cell tt r shard=1) (i : Nat) (hi : i<7) (hsel : tr.cell tt r (sel i)=1) :
    tr.cell tt (r+1) shard=1 ∧ tr.cell tt (r+1) (sel (i+1))=1 := by
  have he := phase_exclusive hL hr hw (x:=shard) (by simp [phases]) hp
  have hh := he.2 header (by simp [phases]) (by decide)
  have hnext := he.2 nextIndex (by simp [phases]) (by decide)
  have hm := he.2 mRaw (by simp [phases]) (by decide)
  have h7 := selector_exclusive hL hr hw he.1 hm (by omega) hsel 7 (by omega) (by omega)
  have h := con hL hr hw (e:=eqG (c cont) (n shard)
    (sum [.mul (c shard) (Dsl.not wordEnd),headerEnd,entryEnd])) (by simp [constraints])
  simp [eval_eqG,eval_n,eval_c,eval_mul,eval_not,wordEnd,headerEnd,entryEnd,
    hc,hp,hh,hnext,h7,Nat.mod_eq_of_lt hn] at h
  have hclock := clock_shift hL hr hw hn hc i hi
  rw [hsel,hh] at hclock
  constructor
  · grind
  · split at hclock <;> grind

theorem shard_word_end (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hp : tr.cell tt r shard=1) (hsel : tr.cell tt r (sel 7)=1) :
    tr.cell tt (r+1) firstIndex=1 ∧ tr.cell tt (r+1) (sel 0)=1 := by
  have he := phase_exclusive hL hr hw (x:=shard) (by simp [phases]) hp
  have hh := he.2 header (by simp [phases]) (by decide)
  have h := (index_phase_step hL hr hw hn hc).1
  have hclock := clock_zero hL hr hw hn hc
  rw [hp,hsel] at h
  rw [hsel,hh] at hclock
  constructor <;> grind

theorem next_word_advance (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hp : tr.cell tt r nextIndex=1) (i : Nat) (hi : i<7) (hsel : tr.cell tt r (sel i)=1) :
    tr.cell tt (r+1) nextIndex=1 ∧ tr.cell tt (r+1) (sel (i+1))=1 := by
  have he := phase_exclusive hL hr hw (x:=nextIndex) (by simp [phases]) hp
  have hh := he.2 header (by simp [phases]) (by decide)
  have hm := he.2 mRaw (by simp [phases]) (by decide)
  have h7 := selector_exclusive hL hr hw he.1 hm (by omega) hsel 7 (by omega) (by omega)
  have h := (index_phase_step hL hr hw hn hc).2
  have hclock := clock_shift hL hr hw hn hc i hi
  rw [hp,h7] at h
  rw [hsel,hh] at hclock
  constructor
  · grind
  · split at hclock <;> grind

/-- Continuing past an entry starts the next shard and increments the entry counter. -/
theorem next_word_end (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (hp : tr.cell tt r nextIndex=1) (hsel : tr.cell tt r (sel 7)=1) :
    tr.cell tt (r+1) shard=1 ∧ tr.cell tt (r+1) (sel 0)=1 ∧
    tr.cell tt (r+1) entry=tr.cell tt r entry+1 := by
  have he := phase_exclusive hL hr hw (x:=nextIndex) (by simp [phases]) hp
  have hh := he.2 header (by simp [phases]) (by decide)
  have h := con hL hr hw (e:=eqG (c cont) (n shard)
    (sum [.mul (c shard) (Dsl.not wordEnd),headerEnd,entryEnd])) (by simp [constraints])
  simp [eval_eqG,eval_n,eval_c,eval_mul,eval_not,wordEnd,headerEnd,entryEnd,
    hc,hp,hh,hsel,Nat.mod_eq_of_lt hn] at h
  have hclock := clock_zero hL hr hw hn hc
  rw [hsel,hh] at hclock
  have hentry := con hL hr hw (e:=eqG (c cont) (n entry) (.add (c entry) entryEnd)) (by simp [constraints])
  simp only [eval_eqG,eval_n,eval_c,eval_add,entryEnd,wordEnd,eval_mul,
    hc,hp,hsel,Nat.mod_eq_of_lt hn] at hentry
  refine ⟨?_,?_,?_⟩ <;> grind

/-- The terminal buffered entry agrees with the declared vector count. -/
theorem buffered_entry_last (hm : tr.cell tt r mBuffer=1)
    (hp : tr.cell tt r nextIndex=1) (hl : tr.cell tt r vl=1) :
    tr.cell tt r entry+1=tr.cell tt r count := by
  have h := con hL hr hw (e:=mul3 (c vl) (c nextIndex) (.mul (c mBuffer)
    (sub (.add (c entry) (k 1)) (c count)))) (by simp [constraints])
  simp only [eval_mul3,eval_mul,eval_c,eval_sub,eval_add,eval_k,hm,hp,hl] at h
  grind

/-- The entry counter is stable until the last byte of a last-index word. -/
theorem entry_carry (hn : r+1<tr.height tt) (hc : tr.cell tt r cont=1)
    (he : tr.cell tt r nextIndex*tr.cell tt r (sel 7)=0) :
    tr.cell tt (r+1) entry=tr.cell tt r entry := by
  have h := con hL hr hw (e:=eqG (c cont) (n entry) (.add (c entry) entryEnd)) (by simp [constraints])
  simp only [eval_eqG,eval_n,eval_c,eval_add,entryEnd,wordEnd,eval_mul,
    hc,he,Nat.mod_eq_of_lt hn] at h
  grind

end ZkFormal.NearV3.Qv.Extract.Parser
