import ZkFormal.NearV3.Candidates.ProcDistCellCells
namespace ZkFormal.NearV3.Candidates.ProcDistCellDivisionCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistCellRow ProcDistCellCells
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem fields (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.al]! =(b2n allowed) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.N1]! =(n1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.L1]! =(l1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.N2]! =(n2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.L2]! =(l2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.q1]! =(quot allowed n1 l1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.r1]! =(remn allowed n1 l1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.q2]! =(quot allowed n2 l2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.r2]! =(remn allowed n2 l2) := by
  rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.al (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.N1 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.L1 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.N2 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.L2 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.q1 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.r1 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.q2 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.r2 (by decide) (by decide) (by decide) (by decide)]
  simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
end ZkFormal.NearV3.Candidates.ProcDistCellDivisionCells
