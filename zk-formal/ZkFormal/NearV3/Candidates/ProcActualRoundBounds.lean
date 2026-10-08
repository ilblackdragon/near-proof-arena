import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualReplayEntries
import ZkFormal.NearV3.Candidates.ExceptVisited
namespace ZkFormal.NearV3.Candidates.ProcActualRoundBounds
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayChain

set_option maxHeartbeats 600000 in
theorem run_decreases (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R) :
    ∀rd∈R.rounds,rd.K=0 ∨ rd.K<rd.Kq := by
  unfold ActualRun.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    refine ExceptVisited.array_visited (β := Array (Nat×Nat×Nat)) (ε := String) _ ?f (fun rd : Gen.RoundD=>rd.K=0 ∨ rd.K<rd.Kq) ?step ?b ?out ?loop
    case loop => assumption
    case step =>
      intro rd hrd s out ho
      repeat first | cases ho | split at ho
      all_goals repeat first | cases ho | split at ho
      all_goals first
        | have hc : check (decide (rd.K<rd.Kq)) "round keys not decreasing"=.ok () := by assumption
          exact ⟨Or.inr (ProcActualReplayDecisions.check_lt _ _ _ hc),_,rfl⟩
        | have hz : (rd.K != 0) ≠ true := by assumption
          have hz' : rd.K=0 := by simpa using hz
          exact ⟨Or.inl hz',_,rfl⟩

/-- Cursor stamping and the generator's checked strict decrease give canonical
field-sized round keys, including zero rounds. -/
theorem stamped_key_bound {T kp Kq zq : Nat} {rs : List Gen.RoundD}
    (hs : Stamped T kp Kq zq rs) (hd : ∀rd∈rs,rd.K=0 ∨ rd.K<rd.Kq) :
    Kq≤Proc.KSENT ∧ ∀rd∈rs,rd.K<Proc.KSENT := by
  induction hs with
  | nil => exact ⟨Nat.le_refl _,by simp⟩
  | @snoc T kp Kq zq rs hs K z L kend es ih =>
    have hprev := ih (fun rd hr=>hd rd (by simp [hr]))
    have hcur := hd ⟨K,z,T,L,kp,kend,Kq,zq,es⟩ (by simp)
    have hlt : K<Proc.KSENT := by
      rcases hcur with hh|hh
      · change K=0 at hh
        rw [hh]
        decide
      · change K<Kq at hh
        omega
    refine ⟨by omega,?_⟩
    intro rd hr
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with hr|rfl
    · exact hprev.2 rd hr
    · exact hlt

theorem run_key_lt (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R) :
    ∀rd∈R.rounds,rd.K<P := by
  rcases run_stamped I tau R h with ⟨T,kp,Kq,zq,hs⟩
  have hb := (stamped_key_bound hs (run_decreases I tau R h)).2
  intro rd hr
  exact Nat.lt_trans (hb rd hr) (by decide)
end ZkFormal.NearV3.Candidates.ProcActualRoundBounds
