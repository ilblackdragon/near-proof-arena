import ZkFormal.NearV3.Candidates.ProcConcatActive
import ZkFormal.NearV3.Candidates.ProcConcatPadding
import ZkFormal.NearV3.Candidates.ProcConcatKind
namespace ZkFormal.NearV3.Candidates.ProcConcatLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcConcatGeometry

theorem groups (rs : List Run) (hd : ∀R∈rs,ProcData.RunData R)
    (ht : ∀pre R S post,rs=pre++R::S::post → S.tau=R.tau+1)
    (hcap : (rows rs).length+1≤2^22) (r t : Nat) (pub : List Fp) (hr : r<2^22) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval (trace rs) t r pub=0 := by
  by_cases ha : r<(rows rs).length
  · exact ProcConcatActive.active_groups rs hd ht hcap r t pub ha
  · exact ProcConcatPadding.padding_groups rs r t pub (by omega) hr

/-- Concatenate actual native process records at log22. Empty processing instances
remain in the witness, with independently bound seeds and no inactive separators. -/
theorem proc_local (rs : List Run) (hd : ∀R∈rs,ProcData.RunData R)
    (hfirst : ∀R rest,rs=R::rest → R.tau=0)
    (ht : ∀pre R S post,rs=pre++R::S::post → S.tau=R.tau+1)
    (hcap : (rows rs).length+1≤2^22) (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (trace rs) t pub := by
  refine ⟨by change 1≤22; decide,by change 22≤22; decide,?_,?_⟩
  · intro r hr
    change ∀e∈Proc.cKind++ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval (trace rs) t r pub=0
    have hk := ProcConcatKind.kind_constraints rs hfirst hcap t r pub hr
    have hg := groups rs hd ht hcap r t pub hr
    simp only [List.forall_mem_append] at hg ⊢
    exact ⟨⟨⟨hk,hg.1.1⟩,hg.1.2⟩,hg.2⟩
  · intro r _
    exact ProcConcatRows.trace_bits rs t r pub

theorem empty_local (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (trace []) t pub := by
  apply proc_local []
  · simp
  · simp
  · intro pre R S post he
    have : pre++R::S::post≠[] := by simp
    exact False.elim (this he.symm)
  · decide
end ZkFormal.NearV3.Candidates.ProcConcatLocal
