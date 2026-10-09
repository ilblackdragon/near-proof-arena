import ZkFormal.NearV3.Candidates.ProcDistCellCounts
namespace ZkFormal.NearV3.Candidates.ProcDistCellOutputCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistCellRow ProcDistCellCells
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem fields (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) :
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.kSh]! =(0) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.kGH]! =(0) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.kC]! =(1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.s]! =(sv) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.nn]! =(n) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.r]! =(rr) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.llo]! =((sv*n+rr)%256) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.lhi]! =((sv*n+rr)/256) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.alc]! =(b2n allowed) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.al]! =(b2n allowed) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.cx]! =(quot allowed n1 l1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.cy]! =(quot allowed n2 l2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.q1]! =(quot allowed n1 l1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.q2]! =(quot allowed n2 l2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.gb]! =(grant allowed n1 l1 n2 l2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.cb]! =(if allowed && quot allowed n2 l2≤quot allowed n1 l1 then 1 else 0) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.cg]! =(b2n allowed) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.a]! =(i) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.b]! =(j) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.da]! =(i+1) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.db]! =(j) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.sL]! =(l2-grant allowed n1 l1 n2 l2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.L2]! =(l2) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.e2]! =(if i+1=n then 1 else 0) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.dlsg]! =(1-(if i+1=n then 1 else 0)) ∧
    (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[Dist.dlrg]! =(1) := by
  rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kSh (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kGH (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kC (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.s (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.nn (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.r (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.llo (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.lhi (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.alc (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.al (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.cx (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.cy (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.q1 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.q2 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.gb (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.cb (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.cg (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.a (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.b (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.da (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.db (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.sL (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.L2 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.e2 (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.dlsg (by decide) (by decide) (by decide) (by decide),
    core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.dlrg (by decide) (by decide) (by decide) (by decide)]
  simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kSh,Dist.kGH,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
end ZkFormal.NearV3.Candidates.ProcDistCellOutputCells
