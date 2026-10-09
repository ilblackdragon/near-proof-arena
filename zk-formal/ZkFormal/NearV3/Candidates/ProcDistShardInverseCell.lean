import ZkFormal.NearV3.Candidates.ProcDistShardControlCells
import ZkFormal.NearV3.Candidates.ProcDistIndexTest
namespace ZkFormal.NearV3.Candidates.ProcDistShardInverseCell
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistShardRow ProcDistShardCells
attribute [local irreducible] ProcDistShardRow.row finv fsub

private theorem last_lookup (xs:List (Nat×Nat))(col value init:Nat) :
    lookup (xs++[(col,value)]) col init=value := by
  simp [append,lookup]

theorem cell (tv n sd i x count left budget kpV:Nat) :
    (row tv n sd i x count left budget kpV)[Dist.ig1]! =finv (fsub i (n-1)) := by
  have hcore : lookup (core tv n sd i x count left budget kpV) Dist.ig1 0=finv (fsub i (n-1)) :=
    last_lookup ((core tv n sd i x count left budget kpV).take 31) Dist.ig1 (finv (fsub i (n-1))) 0
  exact (core_cell tv n sd i x count left budget kpV Dist.ig1 (by decide) (by decide) (by decide) (by decide)).trans hcore
end ZkFormal.NearV3.Candidates.ProcDistShardInverseCell
