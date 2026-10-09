import ZkFormal.NearV3.Candidates.ProcDistShardCells
namespace ZkFormal.NearV3.Candidates.ProcDistShardScalarCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistShardRow ProcDistShardCells

private theorem high_miss (tv n sd i x count left budget kpV col:Nat)(hc:57≤col) :
    lookup (core tv n sd i x count left budget kpV) col 0=0 := by
  apply lookup_miss
  have hcols:∀p∈core tv n sd i x count left budget kpV,p.1<57 := by
    simp [core,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  intro p hp
  have hh:=hcols p hp
  omega

theorem unused_quotient_bits (tv n sd i x count left budget kpV j:Nat)(hj:j<23) :
    (row tv n sd i x count left budget kpV)[Dist.qb1 j]! =0 := by
  rw [core_cell _ _ _ _ _ _ _ _ _ _ (by unfold Dist.qb1;omega)
    (by unfold Dist.qb1;omega) (by unfold Dist.qb1;omega) (by unfold Dist.qb1;omega)]
  exact high_miss _ _ _ _ _ _ _ _ _ _ (by unfold Dist.qb1;omega)

theorem unused_remainder_bits (tv n sd i x count left budget kpV j:Nat)(hj:j<6) :
    (row tv n sd i x count left budget kpV)[Dist.rb1 j]! =0 := by
  rw [core_cell _ _ _ _ _ _ _ _ _ _ (by unfold Dist.rb1;omega)
    (by unfold Dist.rb1;omega) (by unfold Dist.rb1;omega) (by unfold Dist.rb1;omega)]
  exact high_miss _ _ _ _ _ _ _ _ _ _ (by unfold Dist.rb1;omega)

theorem quotients (tv n sd i x count left budget kpV:Nat) :
    (row tv n sd i x count left budget kpV)[Dist.q1]! =0 ∧
    (row tv n sd i x count left budget kpV)[Dist.r1]! =0 ∧
    (row tv n sd i x count left budget kpV)[Dist.q2]! =average count left ∧
    (row tv n sd i x count left budget kpV)[Dist.r2]! =remainder count left := by
  rw [core_cell _ _ _ _ _ _ _ _ _ Dist.q1 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.r1 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.q2 (by decide) (by decide) (by decide) (by decide),
    core_cell _ _ _ _ _ _ _ _ _ Dist.r2 (by decide) (by decide) (by decide) (by decide)]
  simp [core,lookup,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
end ZkFormal.NearV3.Candidates.ProcDistShardScalarCells
