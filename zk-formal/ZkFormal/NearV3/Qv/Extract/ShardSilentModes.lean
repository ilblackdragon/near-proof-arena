import ZkFormal.NearV3.Qv.Extract.ShardRecord

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
include hL hfit hw hs

theorem empty_shard_row (hm : tr.cell tt s mEmpty=1)
    (r : Nat) (hr : s≤r) (hb : r<s+n) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd=[] := by
  have hn := empty_row_count hL hfit hw hs hm
  have hrow : r<tr.height tt := by omega
  have hwalk := hw r hr hb
  by_cases hi : r-s<8
  · have hp := (empty_first_rows hL hfit hw hs hm (r-s) hi).2.1
    have he : s+(r-s)=r := by omega
    rw [he] at hp
    exact shard_nonphase_row hL hrow hwalk (x:=firstIndex) (by simp) hp sd
  · have hp := (empty_second_rows hL hfit hw hs hm (r-s-8) (by omega)).2.1
    have he : s+8+(r-s-8)=r := by omega
    rw [he] at hp
    exact shard_nonphase_row hL hrow hwalk (x:=nextIndex) (by simp) hp sd

theorem raw_shard_row (hm : tr.cell tt s mRaw=1)
    (r : Nat) (hr : s≤r) (hb : r<s+n) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd=[] := by
  have hp := metadata hL hfit hw hs (x:=mRaw) (by simp) r hr hb
  rw [hm] at hp
  exact shard_nonphase_row hL (by omega) (hw r hr hb) (x:=mRaw) (by simp) hp sd

/-- Empty-index and uninterpreted raw records contribute no QSH traffic. -/
theorem nonbuffer_shard_segment
    (hm : tr.cell tt s mEmpty=1 ∨ tr.cell tt s mRaw=1) (sd : Bool) :
    (List.range' s n).flatMap (fun r =>
      rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro r hr
  obtain ⟨i,hi,he⟩ := List.mem_range'.mp hr
  simp only [Nat.one_mul] at he
  rcases hm with hm|hm
  · exact empty_shard_row hL hfit hw hs hm r (by omega) (by omega) sd
  · exact raw_shard_row hL hfit hw hs hm r (by omega) (by omega) sd

end ZkFormal.NearV3.Qv.Extract.Parser
