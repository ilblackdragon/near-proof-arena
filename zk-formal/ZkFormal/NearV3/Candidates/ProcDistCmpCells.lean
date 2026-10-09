import ZkFormal.NearV3.Candidates.SchedSetAllRange
import ZkFormal.NearV3.Candidates.ProcDistGeneratorFactor
namespace ZkFormal.NearV3.Candidates.ProcDistCmpCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open SchedSetAll SchedSetAllRange

theorem bits1 (x c v:Nat)(hc:49≤c ∧ c≤52) : lookup (bitsOf Dist.bt1 x) c v=v := by
  change lookup (block 27 6 (fun i=>bit x i)) c v=v
  apply miss_block;omega
theorem bits2 (x c v:Nat)(hc:49≤c ∧ c≤52) : lookup (bitsOf Dist.bt2 x) c v=v := by
  change lookup (block 35 6 (fun i=>bit x i)) c v=v
  apply miss_block;omega
theorem qbits1 (x c v:Nat)(hc:49≤c ∧ c≤52) : lookup (bitsN Dist.qb1 23 x) c v=v := by
  change lookup (block 57 23 (fun i=>bit x i)) c v=v
  apply miss_block;omega
theorem qbits2 (x c v:Nat)(hc:49≤c ∧ c≤52) : lookup (bitsN Dist.qb2 23 x) c v=v := by
  change lookup (block 80 23 (fun i=>bit x i)) c v=v
  apply miss_block;omega
theorem rbits1 (x c v:Nat)(hc:49≤c ∧ c≤52) : lookup (bitsN Dist.rb1 6 x) c v=v := by
  change lookup (block 103 6 (fun i=>bit x i)) c v=v
  apply miss_block;omega
theorem rbits2 (x c v:Nat)(hc:49≤c ∧ c≤52) : lookup (bitsN Dist.rb2 6 x) c v=v := by
  change lookup (block 109 6 (fun i=>bit x i)) c v=v
  apply miss_block;omega

theorem tail (core:List (Nat×Nat))(use:Bool)(srem rrem q1 q2 r1 r2 c:Nat)
    (hc:49≤c ∧ c≤52) :
    (setAll Dist.width (core++(if use then bitsOf Dist.bt1 srem++bitsOf Dist.bt2 rrem else [])++
      bitsN Dist.qb1 23 q1++bitsN Dist.qb2 23 q2++bitsN Dist.rb1 6 r1++bitsN Dist.rb2 6 r2))[c]! =
      lookup core c 0 := by
  rw [cell _ _ _ (by unfold Dist.width;omega)]
  simp only [append,qbits1 _ _ _ hc,qbits2 _ _ _ hc,rbits1 _ _ _ hc,rbits2 _ _ _ hc]
  split
  · rw [append,bits2 _ _ _ hc,bits1 _ _ _ hc]
  · rfl

theorem shard_tail (core:List (Nat×Nat))(use:Prop)[Decidable use](rem q r c:Nat)(hc:49≤c ∧ c≤52) :
    (setAll Dist.width (core++(if use then [] else bitsOf Dist.bt2 rem)++
      bitsN Dist.qb2 23 q++bitsN Dist.rb2 6 r))[c]! =lookup core c 0 := by
  rw [cell _ _ _ (by unfold Dist.width;omega)]
  simp only [append,qbits2 _ _ _ hc,rbits2 _ _ _ hc]
  split
  · rfl
  · exact bits2 _ _ _ hc
end ZkFormal.NearV3.Candidates.ProcDistCmpCells
