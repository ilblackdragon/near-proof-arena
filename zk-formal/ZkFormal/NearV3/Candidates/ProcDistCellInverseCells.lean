import ZkFormal.NearV3.Candidates.ProcDistCellBools
namespace ZkFormal.NearV3.Candidates.ProcDistCellInverseCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistCellRow ProcDistCellCells
attribute [local irreducible] ProcDistCellRow.row finv fsub

private theorem tail1 (xs:List (Nat×Nat))(v1 e2 v2 flag init:Nat) :
    lookup (xs++[(47,v1),(42,e2),(41,v2),(56,flag)]) 47 init=v1 := by
  simp [append,lookup]
private theorem tail2 (xs:List (Nat×Nat))(v flag init:Nat) :
    lookup (xs++[(41,v),(56,flag)]) 41 init=v := by
  simp [append,lookup]

theorem first (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.ig1]! =finv (fsub j (n-1)) := by
  have hcore:lookup (core ids tv n i j sv rr n1 l1 n2 l2 allowed) Dist.ig1 0=finv (fsub j (n-1)) :=
    tail1 ((core ids tv n i j sv rr n1 l1 n2 l2 allowed).take 35) (finv (fsub j (n-1)))
      (if i+1=n then 1 else 0) (finv (fsub i (n-1)))
      ((if j+1=n then 1 else 0)*(if i+1=n then 1 else 0)) 0
  exact (core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.ig1 (by decide) (by decide) (by decide) (by decide)).trans hcore

theorem second (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.ig2]! =finv (fsub i (n-1)) := by
  have hcore:lookup (core ids tv n i j sv rr n1 l1 n2 l2 allowed) Dist.ig2 0=finv (fsub i (n-1)) :=
    tail2 ((core ids tv n i j sv rr n1 l1 n2 l2 allowed).take 37) (finv (fsub i (n-1)))
      ((if j+1=n then 1 else 0)*(if i+1=n then 1 else 0)) 0
  exact (core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.ig2 (by decide) (by decide) (by decide) (by decide)).trans hcore
end ZkFormal.NearV3.Candidates.ProcDistCellInverseCells
