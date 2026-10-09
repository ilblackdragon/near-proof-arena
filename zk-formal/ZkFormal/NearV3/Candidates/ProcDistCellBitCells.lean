import ZkFormal.NearV3.Candidates.ProcDistCellGrid
namespace ZkFormal.NearV3.Candidates.ProcDistCellBitCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll SchedSetAllRange
open ProcDistCellRow

theorem q1 (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)(k:Nat)(hk:k<23) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.qb1 k]! =bit (quot allowed n1 l1) k := by
  unfold row
  rw [cell Dist.width _ _ (by unfold Dist.width Dist.qb1;omega)]
  simp only [append]
  rw [show lookup (bitsN Dist.rb2 6 (remn allowed n2 l2)) (Dist.qb1 k) _=_ from
    miss_block 109 6 (57+k) _ (fun x=>bit (remn allowed n2 l2) x) (Or.inl (by omega))]
  rw [show lookup (bitsN Dist.rb1 6 (remn allowed n1 l1)) (Dist.qb1 k) _=_ from
    miss_block 103 6 (57+k) _ (fun x=>bit (remn allowed n1 l1) x) (Or.inl (by omega))]
  rw [show lookup (bitsN Dist.qb2 23 (quot allowed n2 l2)) (Dist.qb1 k) _=_ from
    miss_block 80 23 (57+k) _ (fun x=>bit (quot allowed n2 l2) x) (Or.inl (by omega))]
  change lookup (block 57 23 (fun x=>bit (quot allowed n1 l1) x)) (57+k) _=_
  rw [lookup_block,if_pos (by omega)]
  simp

theorem q2 (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)(k:Nat)(hk:k<23) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.qb2 k]! =bit (quot allowed n2 l2) k := by
  unfold row
  rw [cell Dist.width _ _ (by unfold Dist.width Dist.qb2;omega)]
  simp only [append]
  rw [show lookup (bitsN Dist.rb2 6 (remn allowed n2 l2)) (Dist.qb2 k) _=_ from
    miss_block 109 6 (80+k) _ (fun x=>bit (remn allowed n2 l2) x) (Or.inl (by omega))]
  rw [show lookup (bitsN Dist.rb1 6 (remn allowed n1 l1)) (Dist.qb2 k) _=_ from
    miss_block 103 6 (80+k) _ (fun x=>bit (remn allowed n1 l1) x) (Or.inl (by omega))]
  change lookup (block 80 23 (fun x=>bit (quot allowed n2 l2) x)) (80+k) _=_
  rw [lookup_block,if_pos (by omega)]
  simp

theorem r1 (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)(k:Nat)(hk:k<6) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.rb1 k]! =bit (remn allowed n1 l1) k := by
  unfold row
  rw [cell Dist.width _ _ (by unfold Dist.width Dist.rb1;omega)]
  simp only [append]
  rw [show lookup (bitsN Dist.rb2 6 (remn allowed n2 l2)) (Dist.rb1 k) _=_ from
    miss_block 109 6 (103+k) _ (fun x=>bit (remn allowed n2 l2) x) (Or.inl (by omega))]
  change lookup (block 103 6 (fun x=>bit (remn allowed n1 l1) x)) (103+k) _=_
  rw [lookup_block,if_pos (by omega)]
  simp

theorem r2 (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)(k:Nat)(hk:k<6) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.rb2 k]! =bit (remn allowed n2 l2) k := by
  unfold row
  rw [cell Dist.width _ _ (by unfold Dist.width Dist.rb2;omega)]
  simp only [append]
  change lookup (block 109 6 (fun x=>bit (remn allowed n2 l2) x)) (109+k) _=_
  rw [lookup_block,if_pos (by omega)]
  simp
end ZkFormal.NearV3.Candidates.ProcDistCellBitCells
