import ZkFormal.NearV3.Candidates.ProcEmptyBoundaryRegression
namespace ZkFormal.NearV3.Candidates.ProcEmptyRunRegression
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def input (b : UInt8) : Input :=
  { ids := [], p := ⟨0,0,0,0,0⟩, allowed := #[], raw := [],
    seed := b :: List.replicate 31 0, ash := List.replicate 32 0,
    prev := ⟨[],List.replicate 32 0⟩ }

/-- The actual native generator accepts empty processing runs with distinct seeds.
This does not establish a full accepted checkD0a witness. -/
theorem run_zero : (Gen.run (input 0) 0).toOption.map (fun R=>(R.rounds.length,R.seed))=
    some (0,(input 0).seed) := by decide +kernel

theorem run_one : (Gen.run (input 1) 1).toOption.map (fun R=>(R.rounds.length,R.seed))=
    some (0,(input 1).seed) := by decide +kernel
def pvInput (b : UInt8) : Input :=
  { input b with ids := [0], p := ⟨100000,4500000,4194304,4194304,4500000⟩, allowed := #[true] }

theorem pv_params : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 1=
    some (pvInput 0).p := by decide +kernel

theorem pv_run_zero : (Gen.run (pvInput 0) 0).toOption.map (fun R=>(R.rounds.length,R.seed))=
    some (0,(pvInput 0).seed) := by decide +kernel

theorem pv_run_one : (Gen.run (pvInput 1) 1).toOption.map (fun R=>(R.rounds.length,R.seed))=
    some (0,(pvInput 1).seed) := by decide +kernel
end ZkFormal.NearV3.Candidates.ProcEmptyRunRegression
