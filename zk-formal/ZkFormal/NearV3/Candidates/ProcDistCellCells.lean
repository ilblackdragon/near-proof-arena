import ZkFormal.NearV3.Candidates.ProcDistCellArithmetic
namespace ZkFormal.NearV3.Candidates.ProcDistCellCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll SchedSetAllRange
open ProcDistCellRow

theorem core_cell (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)(col:Nat)
    (hc:col<119)(hbt1:col<27∨33≤col)(hbt2:col<35∨41≤col)(hh:col<57∨115≤col) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]! =
      lookup (core ids tv n i j sv rr n1 l1 n2 l2 allowed) col 0 := by
  unfold row
  rw [cell Dist.width _ col hc]
  have hq1(v:Nat):lookup (bitsN Dist.qb1 23 (quot allowed n1 l1)) col v=v :=
    miss_block 57 23 col v (fun k=>bit (quot allowed n1 l1) k) (by omega)
  have hq2(v:Nat):lookup (bitsN Dist.qb2 23 (quot allowed n2 l2)) col v=v :=
    miss_block 80 23 col v (fun k=>bit (quot allowed n2 l2) k) (by omega)
  have hr1(v:Nat):lookup (bitsN Dist.rb1 6 (remn allowed n1 l1)) col v=v :=
    miss_block 103 6 col v (fun k=>bit (remn allowed n1 l1) k) (by omega)
  have hr2(v:Nat):lookup (bitsN Dist.rb2 6 (remn allowed n2 l2)) col v=v :=
    miss_block 109 6 col v (fun k=>bit (remn allowed n2 l2) k) (by omega)
  simp only [append,hq1,hq2,hr1,hr2]
  split
  · rw [append]
    rw [show lookup (bitsOf Dist.bt1 (n1-1-remn allowed n1 l1)) col
        (lookup (core ids tv n i j sv rr n1 l1 n2 l2 allowed) col 0)=
        lookup (core ids tv n i j sv rr n1 l1 n2 l2 allowed) col 0 from
      miss_block 27 6 col _ (fun k=>bit (n1-1-remn allowed n1 l1) k) hbt1]
    exact miss_block 35 6 col _ (fun k=>bit (n2-1-remn allowed n2 l2) k) hbt2
  · rfl

theorem complement1 (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2 k:Nat)(hk:k<6) :
    (row ids tv n i j sv rr n1 l1 n2 l2 true)[Dist.bt1 k]! =bit (n1-1-remn true n1 l1) k := by
  unfold row
  rw [cell Dist.width _ _ (by unfold Dist.width Dist.bt1;omega)]
  have hmiss (base len value v:Nat)(hbase:33≤base) :
      lookup (bitsN (fun x=>base+x) len value) (Dist.bt1 k) v=v :=
    miss_block base len (27+k) v (fun x=>bit value x) (Or.inl (by omega))
  simp only [append,ite_true]
  rw [show lookup (bitsN Dist.rb2 6 (remn true n2 l2)) (Dist.bt1 k) _=_ from hmiss 109 6 _ _ (by decide),
    show lookup (bitsN Dist.rb1 6 (remn true n1 l1)) (Dist.bt1 k) _=_ from hmiss 103 6 _ _ (by decide),
    show lookup (bitsN Dist.qb2 23 (quot true n2 l2)) (Dist.bt1 k) _=_ from hmiss 80 23 _ _ (by decide),
    show lookup (bitsN Dist.qb1 23 (quot true n1 l1)) (Dist.bt1 k) _=_ from hmiss 57 23 _ _ (by decide),
    show lookup (bitsOf Dist.bt2 (n2-1-remn true n2 l2)) (Dist.bt1 k) _=_ from hmiss 35 6 _ _ (by decide)]
  change lookup (block 27 6 (fun x=>bit (n1-1-remn true n1 l1) x)) (27+k) _=_
  rw [lookup_block,if_pos (by omega)]
  simp

theorem complement2 (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2 k:Nat)(hk:k<6) :
    (row ids tv n i j sv rr n1 l1 n2 l2 true)[Dist.bt2 k]! =bit (n2-1-remn true n2 l2) k := by
  unfold row
  rw [cell Dist.width _ _ (by unfold Dist.width Dist.bt2;omega)]
  have hmiss (base len value v:Nat)(hbase:41≤base) :
      lookup (bitsN (fun x=>base+x) len value) (Dist.bt2 k) v=v :=
    miss_block base len (35+k) v (fun x=>bit value x) (Or.inl (by omega))
  simp only [append,ite_true]
  rw [show lookup (bitsN Dist.rb2 6 (remn true n2 l2)) (Dist.bt2 k) _=_ from hmiss 109 6 _ _ (by decide),
    show lookup (bitsN Dist.rb1 6 (remn true n1 l1)) (Dist.bt2 k) _=_ from hmiss 103 6 _ _ (by decide),
    show lookup (bitsN Dist.qb2 23 (quot true n2 l2)) (Dist.bt2 k) _=_ from hmiss 80 23 _ _ (by decide),
    show lookup (bitsN Dist.qb1 23 (quot true n1 l1)) (Dist.bt2 k) _=_ from hmiss 57 23 _ _ (by decide)]
  change lookup (block 35 6 (fun x=>bit (n2-1-remn true n2 l2) x)) (35+k) _=_
  rw [lookup_block,if_pos (by omega)]
  simp
end ZkFormal.NearV3.Candidates.ProcDistCellCells
