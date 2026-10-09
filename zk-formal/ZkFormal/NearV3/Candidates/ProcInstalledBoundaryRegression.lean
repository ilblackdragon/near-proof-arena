import ZkFormal.NearV3.Assembly.SchedulerRunSelected
import ZkFormal.NearV3.Candidates.ProcEmptyRunRegression
namespace ZkFormal.NearV3.Candidates.ProcInstalledBoundaryRegression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def fallback : Run:=⟨0,0,0,0,[],[],#[],[],#[],[],[],[],0,⟨#[],#[],#[],#[],NearSpecV3.Rng.ofSeed []⟩⟩
def input (b : UInt8) : Input:=ProcEmptyRunRegression.pvInput b
def output (b : UInt8) (tau : Nat) : Run:=(ActualRun.run (input b) tau).toOption.getD fallback
def runs : List Run:=[output 0 0,output 1 1]

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
/-- Both corrected native executions succeed with PV86 and distinct seeds.
This is generator-level reachability, not a full accepted checkD0a fixture. -/
theorem native_zero : (ActualRun.run (input 0) 0).toOption.map (fun R=>(R.rounds.length,R.seed))=
    some (0,(input 0).seed) := by decide +kernel

theorem native_one : (ActualRun.run (input 1) 1).toOption.map (fun R=>(R.rounds.length,R.seed))=
    some (0,(input 1).seed) := by decide +kernel

theorem selected_member : ProcEmptyBoundaryRegression.rotation0∈
    (ProcPriorComparatorRoutedFamily.selected[10]!).constraints := by
  rw [Assembly.CodecDigest.routed_process_slot]
  simp only [Proc.table,Proc.constraints,List.mem_append]
  exact Or.inl (Or.inl (Or.inr ProcEmptyBoundaryRegression.rotation0_member))

theorem actual_boundary : ProcEmptyBoundaryRegression.rotation0.eval
    (ProcConcatGeometry.trace runs) 0 15 []=1 := by decide +kernel

theorem installed_not_local : ¬TableLocal (ProcPriorComparatorRoutedFamily.selected[10]!)
    (ProcConcatGeometry.trace runs) 0 [] := by
  intro h
  have hz:=h.constr 15 (by change 15<2^22;decide) _ selected_member
  rw [actual_boundary] at hz
  exact (by decide : (1:Fp)≠0) hz
end ZkFormal.NearV3.Candidates.ProcInstalledBoundaryRegression
