import ZkFormal.NearV3.Candidates.ProcDistShardRange
namespace ZkFormal.NearV3.Candidates.ProcDistShardAverageCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistShardRow ProcDistShardCells

theorem fields (tv n sd i x count left budget kpV:Nat) :
    (row tv n sd i x count left budget kpV)[Dist.kSh]! =1 ∧
    (row tv n sd i x count left budget kpV)[Dist.N2]! =count ∧
    (row tv n sd i x count left budget kpV)[Dist.L2]! =left ∧
    (row tv n sd i x count left budget kpV)[Dist.icnt]! =finv count ∧
    (row tv n sd i x count left budget kpV)[Dist.zc]! =(if count=0 then 1 else 0) := by
  rw [core_cell _ _ _ _ _ _ _ _ _ Dist.kSh (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.N2 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.L2 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.icnt (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.zc (by decide) (by decide) (by decide) (by decide)]
  simp [core,lookup,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
end ZkFormal.NearV3.Candidates.ProcDistShardAverageCells
