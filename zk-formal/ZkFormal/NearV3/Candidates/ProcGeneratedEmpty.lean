import ZkFormal.NearV3.Candidates.ProcConcatLocal
import ZkFormal.NearV3.Candidates.ProcEmptyRunRegression
namespace ZkFormal.NearV3.Candidates.ProcGeneratedEmpty
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcConcatGeometry ProcEmptyRunRegression

theorem runData_empty (R : Run) (h : R.rounds=[]) : ProcData.RunData R := by
  constructor
  · simp [h]
  constructor
  · simp [h]
  · intro pre rd next rest he
    have : pre++rd::next::rest≠[] := by simp
    exact False.elim (this (he.symm.trans h))

theorem generated_zero : (Gen.run (pvInput 0) 0).toOption.map
    (fun R=>(R.tau,R.rounds.length,R.seed))=some (0,0,(pvInput 0).seed) := by decide +kernel

theorem generated_one : (Gen.run (pvInput 1) 1).toOption.map
    (fun R=>(R.tau,R.rounds.length,R.seed))=some (1,0,(pvInput 1).seed) := by decide +kernel

theorem pair_local (R S : Run) (hR : R.rounds=[]) (hS : S.rounds=[])
    (htR : R.tau=0) (htS : S.tau=1) (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (trace [R,S]) t pub := by
  apply ProcConcatLocal.proc_local
  · intro X hX
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hX
    rcases hX with rfl|rfl
    · exact runData_empty _ hR
    · exact runData_empty _ hS
  · intro X rest he
    simp only [List.cons.injEq] at he
    exact he.1 ▸ htR
  · intro pre X Y post he
    have hp : pre.length=0 := by have := congrArg List.length he; simp at this; omega
    have hp' : pre=[] := by simpa using hp
    subst pre
    simp only [List.nil_append,List.cons.injEq] at he
    rcases he with ⟨rfl,rfl,hpost⟩
    omega
  · simp [rows,procVs,keyVs,hR,hS]

/-- Actual PV86 Gen.run outputs, rather than fabricated Run records, render the
zero-round differing-seed boundary legally. This is not a checkD0a fixture. -/
theorem generated_pair_local (t : Nat) (pub : List Fp) :
    ∃ R S, Gen.run (pvInput 0) 0=.ok R ∧ Gen.run (pvInput 1) 1=.ok S ∧
      R.seed≠S.seed ∧ TableLocal ProcBoundaryRepair.table (trace [R,S]) t pub := by
  have h0 := generated_zero
  have h1 := generated_one
  cases he0 : Gen.run (pvInput 0) 0 with
  | error e => simp [he0,Except.toOption] at h0
  | ok R =>
    cases he1 : Gen.run (pvInput 1) 1 with
    | error e => simp [he1,Except.toOption] at h1
    | ok S =>
      simp only [he0,Except.toOption,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h0
      simp only [he1,Except.toOption,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h1
      refine ⟨R,S,rfl,rfl,?_,?_⟩
      · rw [h0.2.2,h1.2.2]
        decide
      · exact pair_local R S (by simpa using h0.2.1)
          (by simpa using h1.2.1) h0.1 h1.1 t pub
end ZkFormal.NearV3.Candidates.ProcGeneratedEmpty
