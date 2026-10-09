import ZkFormal.NearV3.Candidates.ProcDistShardAverage
namespace ZkFormal.NearV3.Candidates.ProcDistShardOutputCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistShardRow ProcDistShardCells
set_option maxRecDepth 32768
theorem fields (tv n sd i x count left budget kpV:Nat) :
    (row tv n sd i x count left budget kpV)[Dist.cx]! =(average count left*64+x) ∧
    (row tv n sd i x count left budget kpV)[Dist.cy]! =(kpV) ∧
    (row tv n sd i x count left budget kpV)[Dist.cb]! =(1) ∧
    (row tv n sd i x count left budget kpV)[Dist.kp]! =(kpV) ∧
    (row tv n sd i x count left budget kpV)[Dist.side]! =(sd) ∧
    (row tv n sd i x count left budget kpV)[Dist.a]! =(i) ∧
    (row tv n sd i x count left budget kpV)[Dist.r]! =(x) ∧
    (row tv n sd i x count left budget kpV)[Dist.da]! =(if sd=0 then i else 0) ∧
    (row tv n sd i x count left budget kpV)[Dist.db]! =(if sd=0 then 255 else i) ∧
    (row tv n sd i x count left budget kpV)[Dist.sL]! =(left) ∧
    (row tv n sd i x count left budget kpV)[Dist.al]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.shd]! =(x) ∧
    (row tv n sd i x count left budget kpV)[Dist.lnk]! =(count) ∧
    (row tv n sd i x count left budget kpV)[Dist.llo]! =(n) ∧
    (row tv n sd i x count left budget kpV)[Dist.nn]! =(n) ∧
    (row tv n sd i x count left budget kpV)[Dist.adr]! =(4096*(sd+1)+x) ∧
    (row tv n sd i x count left budget kpV)[Dist.bv]! =(budget) ∧
    (row tv n sd i x count left budget kpV)[Dist.by0]! =(budget%256) ∧
    (row tv n sd i x count left budget kpV)[Dist.by1]! =(budget/256%256) ∧
    (row tv n sd i x count left budget kpV)[Dist.by2]! =(budget/65536%256) ∧
    (row tv n sd i x count left budget kpV)[Dist.b]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.s]! =(0) := by
  rw [core_cell _ _ _ _ _ _ _ _ _ Dist.cx (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.cy (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.cb (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.kp (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.side (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.a (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.r (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.da (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.db (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.sL (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.al (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.shd (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.lnk (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.llo (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.nn (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.adr (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.bv (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.by0 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.by1 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.by2 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.b (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.s (by decide) (by decide) (by decide) (by decide)]
  simp [core,lookup,Dist.al,Dist.b,Dist.s,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
end ZkFormal.NearV3.Candidates.ProcDistShardOutputCells
