import ZkFormal.NearV3.Candidates.ProcDistShardRow
namespace ZkFormal.NearV3.Candidates.ProcDistShardCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll SchedSetAllRange
open ProcDistShardRow

theorem core_cell (tv n sd i x count left budget kpV col:Nat)(hc:col<119)
    (hbt:col<35 ∨41≤col)(hqb:col<80 ∨103≤col)(hrb:col<109 ∨115≤col) :
    (row tv n sd i x count left budget kpV)[col]! =lookup (core tv n sd i x count left budget kpV) col 0 := by
  unfold row
  rw [cell Dist.width _ col hc]
  have hq(v:Nat):lookup (bitsN Dist.qb2 23 (average count left)) col v=v :=
    miss_block 80 23 col v (fun j=>bit (average count left) j) hqb
  have hr(v:Nat):lookup (bitsN Dist.rb2 6 (remainder count left)) col v=v :=
    miss_block 109 6 col v (fun j=>bit (remainder count left) j) hrb
  simp only [append,hq,hr]
  split
  · rfl
  · exact miss_block 35 6 col _ (fun j=>bit (count-1-remainder count left) j) hbt

theorem quotient_bits (tv n sd i x count left budget kpV j:Nat)(hj:j<23) :
    (row tv n sd i x count left budget kpV)[Dist.qb2 j]! =bit (average count left) j := by
  unfold row
  rw [cell _ _ _ (by unfold Dist.qb2 Dist.width;omega)]
  simp only [append]
  have hr(v:Nat):lookup (bitsN Dist.rb2 6 (remainder count left)) (Dist.qb2 j) v=v :=
    miss_block 109 6 (80+j) v (fun k=>bit (remainder count left) k) (Or.inl (by omega))
  rw [hr]
  change lookup (block 80 23 (fun k=>bit (average count left) k)) (80+j) _=_
  rw [lookup_block,if_pos (by omega)]
  simp

theorem remainder_bits (tv n sd i x count left budget kpV j:Nat)(hj:j<6) :
    (row tv n sd i x count left budget kpV)[Dist.rb2 j]! =bit (remainder count left) j := by
  unfold row
  rw [cell _ _ _ (by unfold Dist.rb2 Dist.width;omega),append]
  change lookup (block 109 6 (fun k=>bit (remainder count left) k)) (109+j) _=_
  rw [lookup_block,if_pos (by omega)]
  simp

theorem complement_bits (tv n sd i x count left budget kpV j:Nat)(hj:j<6)(hc:count≠0) :
    (row tv n sd i x count left budget kpV)[Dist.bt2 j]! =bit (count-1-remainder count left) j := by
  unfold row
  rw [cell _ _ _ (by unfold Dist.bt2 Dist.width;omega)]
  have hq(v:Nat):lookup (bitsN Dist.qb2 23 (average count left)) (Dist.bt2 j) v=v :=
    miss_block 80 23 (35+j) v (fun k=>bit (average count left) k) (Or.inl (by omega))
  have hr(v:Nat):lookup (bitsN Dist.rb2 6 (remainder count left)) (Dist.bt2 j) v=v :=
    miss_block 109 6 (35+j) v (fun k=>bit (remainder count left) k) (Or.inl (by omega))
  simp only [append,hq,hr,if_neg hc]
  change lookup (block 35 6 (fun k=>bit (count-1-remainder count left) k)) (35+j) _=_
  rw [lookup_block,if_pos (by omega)]
  simp
end ZkFormal.NearV3.Candidates.ProcDistShardCells
