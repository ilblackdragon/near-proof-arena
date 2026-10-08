import ZkFormal.NearV3.Candidates.ProcModelRoundShape
namespace ZkFormal.NearV3.Candidates.ProcModelClock
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcModelEntryShape

theorem stamped_concat (start : Nat) (xs ys : List Step)
    (hx : Stamped start xs) (hy : Stamped (start+xs.length) ys) : Stamped start (xs++ys) := by
  intro i hi
  by_cases hil : i<xs.length
  · rw [List.getElem_append_left hil]
    exact hx i hil
  · have hiy : i-xs.length<ys.length := by simp only [List.length_append] at hi; omega
    rw [List.getElem_append_right (by omega)]
    have hh := hy (i-xs.length) hiy
    omega

theorem trace_flat {start : Nat} {rs : List Round} {last : Nat}
    (h : ProcModelRoundShape.Trace start rs last) :
    last=start+(rs.flatMap Round.steps).length ∧ Stamped start (rs.flatMap Round.steps) ∧
    ∀rd∈rs,rd.steps.length=rd.bucket.length := by
  induction h with
  | nil => exact ⟨by simp,by simp [Stamped],by simp⟩
  | @snoc rs t h rd ht hc hs ih =>
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    refine ⟨by simp only [List.length_append]; omega,?_,?_⟩
    · apply stamped_concat start _ _ ih.2.1
      simpa only [←ih.1] using hs
    · intro r hr
      simp only [List.mem_append,List.mem_singleton] at hr
      rcases hr with hr|rfl
      · exact ih.2.2 r hr
      · exact hc

theorem process_clock (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    Stamped reqs.length (rs.flatMap Round.steps) ∧ ∀rd∈rs,rd.steps.length=rd.bucket.length := by
  obtain ⟨last,ht⟩ := ProcModelRoundShape.process_trace n allowed reqs st0 st fuel rs h
  exact (trace_flat ht).2

theorem process_time_check (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs))
    (i : Nat) (hi : i<(rs.flatMap Round.steps).length) :
    Gen.check (((rs.flatMap Round.steps)[i]).t==reqs.length+i) "model time"=.ok () := by
  have hh := (process_clock n allowed reqs st0 st fuel rs h).1 i hi
  simp [hh,Gen.check,pure,Except.pure]
end ZkFormal.NearV3.Candidates.ProcModelClock
