import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualRequestCount
namespace ZkFormal.NearV3.Candidates.ProcActualNativeSequence
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Execute the actual native generator with contiguous transition ordinals. -/
def runInputs : List Input → Nat → Except String (List Run)
  | [],_ => .ok []
  | I::is,tau => do
    let R ← ActualRun.run I tau
    let rs ← runInputs is (tau+1)
    return R::rs

def Stamped (tau : Nat) (rs : List Run) : Prop :=
  ∀pre R post,rs=pre++R::post → R.tau=tau+pre.length

theorem stamped_cons (tau : Nat) (R : Run) (rs : List Run)
    (hR : R.tau=tau) (hrs : Stamped (tau+1) rs) : Stamped tau (R::rs) := by
  intro pre S post h
  cases pre with
  | nil => cases h; simpa using hR
  | cons x pre =>
    simp only [List.cons_append,List.cons.injEq] at h
    have hh := hrs pre S post h.2
    simp only [List.length_cons]
    omega

theorem sequence_spec (is : List Input) (tau : Nat) (rs : List Run)
    (h : runInputs is tau=.ok rs) :
    rs.length=is.length ∧ Stamped tau rs ∧
    ∀R∈rs,∃I∈is,ActualRun.run I R.tau=.ok R := by
  induction is generalizing tau rs with
  | nil => simp only [runInputs,Except.ok.injEq] at h; subst rs; simp [Stamped]
  | cons I is ih =>
    simp only [runInputs] at h
    cases he : ActualRun.run I tau with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok R =>
      cases ht : runInputs is (tau+1) with
      | error e => simp only [he,ht,bind,Except.bind] at h; cases h
      | ok rest =>
        simp only [he,ht,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
        subst rs
        have hs := ih (tau+1) rest ht
        have hf := (ProcActualRunProjection.run_fields I tau R he).1
        refine ⟨by simp [hs.1],stamped_cons tau R rest hf hs.2.1,?_⟩
        intro S hS
        simp only [List.mem_cons] at hS
        rcases hS with rfl|hS
        · exact ⟨I,by simp,by simpa [hf] using he⟩
        · rcases hs.2.2 S hS with ⟨J,hJ,hJrun⟩
          exact ⟨J,by simp [hJ],hJrun⟩

theorem first_tau (rs : List Run) (h : Stamped 0 rs) :
    ∀R rest,rs=R::rest → R.tau=0 := by
  intro R rest he
  simpa using h [] R rest he

theorem next_tau (rs : List Run) (h : Stamped 0 rs) :
    ∀pre R S post,rs=pre++R::S::post → S.tau=R.tau+1 := by
  intro pre R S post he
  have hR := h pre R (S::post) he
  have hS := h (pre++[R]) S post (by simpa [List.append_assoc] using he)
  simp only [List.length_append,List.length_cons,List.length_nil] at hS
  omega

/-- Successful native sequence execution supplies ordinal continuity and the
entire process witness. Only native input well-formedness and batch count remain. -/
theorem sequence_local (is : List Input) (rs : List Run)
    (h : runInputs is 0=.ok rs) (hc : is.length≤33)
    (hi : ∀I∈is,
      NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p ∧
      I.ids.length≤64 ∧ I.raw.length≤4096)
    (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub := by
  have hs := sequence_spec is 0 rs h
  apply ProcActualNativeBudget.native_local rs (by omega) ?_ (first_tau rs hs.2.1) (next_tau rs hs.2.1) t pub
  intro R hR
  rcases hs.2.2 R hR with ⟨I,hI,hr⟩
  have hIok := hi I hI
  have hC := ProcActualRequestCount.run_count I R.tau R hr
  exact ⟨I,hIok.1,hr,hIok.2.1,by omega⟩
end ZkFormal.NearV3.Candidates.ProcActualNativeSequence
