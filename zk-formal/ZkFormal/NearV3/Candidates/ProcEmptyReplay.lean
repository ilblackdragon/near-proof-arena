import ZkFormal.NearV3.Candidates.ProcRunProjection
import ZkFormal.NearV3.Candidates.ProcGeneratedEmpty
namespace ZkFormal.NearV3.Candidates.ProcEmptyReplay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcConcatGeometry

/-- Derive the local replay invariant directly from actual generator success for
an empty raw request list, for arbitrary previous state and seed. -/
theorem runData (I : Input) (tau : Nat) (R : Run)
    (hraw : I.raw=[]) (h : Gen.run I tau=.ok R) : ProcData.RunData R :=
  ProcGeneratedEmpty.runData_empty R (ProcRunProjection.run_empty_raw I tau R hraw h)

theorem row_length (R : Run) (h : R.rounds=[]) : (procVs R).length=16 := by
  simp [procVs,keyVs,h]

theorem rows_length (rs : List Run) (h : ∀R∈rs,R.rounds=[]) :
    (rows rs).length=16*rs.length := by
  induction rs with
  | nil => simp [rows]
  | cons R rs ih =>
    have hR := row_length R (h R (by simp))
    have hs := ih (fun S hS=>h S (by simp [hS]))
    change (procVs R ++ rows rs).length=16*(rs.length+1)
    rw [List.length_append,hR,hs]
    omega

/-- Native empty-request instance lists need only their ordinary instance clock
and the exact key-prefix row count. No RunData or AIR equation is assumed. -/
theorem native_list_local (rs : List Run)
    (hr : ∀R∈rs,∃I : Input,I.raw=[] ∧ Gen.run I R.tau=.ok R)
    (hfirst : ∀R rest,rs=R::rest → R.tau=0)
    (ht : ∀pre R S post,rs=pre++R::S::post → S.tau=R.tau+1)
    (hcount : 16*rs.length+1≤2^22) (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (trace rs) t pub := by
  have he : ∀R∈rs,R.rounds=[] := by
    intro R hR
    rcases hr R hR with ⟨I,hI,hg⟩
    exact ProcRunProjection.run_empty_raw I R.tau R hI hg
  apply ProcConcatLocal.proc_local rs
    (fun R hR=>ProcGeneratedEmpty.runData_empty R (he R hR)) hfirst ht
  simpa [rows_length rs he] using hcount
end ZkFormal.NearV3.Candidates.ProcEmptyReplay
