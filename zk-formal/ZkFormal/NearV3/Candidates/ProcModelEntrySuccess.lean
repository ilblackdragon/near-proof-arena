import ZkFormal.NearV3.Candidates.ProcModelStep
import ZkFormal.NearV3.Sched.Spec.Granted
namespace ZkFormal.NearV3.Candidates.ProcModelEntrySuccess
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

/-- Positive native increments and the pending-key/current-allowance invariant
make the model's re-push decrease check succeed, including allowance zero. -/
theorem repush_decreases (K inc : Nat) (hi : 0<inc) :
    K-inc<K ∨ K=0 ∧ K-inc=0 := by omega

theorem entry_success (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (acc : ProcModelStep.EntryAcc)
    (hl : reqs.toArray[v/64]!.link<acc.2.1.al.size)
    (hk : acc.2.1.al[reqs.toArray[v/64]!.link]! = K)
    (hi : 0<reqs.toArray[v/64]!.incs.getD (v%64) 0) :
    ∃next,ProcModelStep.entryStep n allowed reqs K z v acc=.ok (.yield next) := by
  have hu : (acc.2.1.al.set! reqs.toArray[v/64]!.link (acc.2.1.al[reqs.toArray[v/64]!.link]! - reqs.toArray[v/64]!.incs.getD (v%64) 0))[reqs.toArray[v/64]!.link]! = K-reqs.toArray[v/64]!.incs.getD (v%64) 0 := by
    rw [Array.getElem!_set!_self _ _ _ hl,hk]
  have hd : ((K-reqs.toArray[v/64]!.incs.getD (v%64) 0<K) ||
      (K==0 && K-reqs.toArray[v/64]!.incs.getD (v%64) 0==0))=true := by
    simpa only [Bool.or_eq_true,decide_eq_true_eq,Bool.and_eq_true,beq_iff_eq] using
      repush_decreases K _ hi
  by_cases hok : (allowed[reqs.toArray[v/64]!.link]! &&
      decide (reqs.toArray[v/64]!.incs.getD (v%64) 0≤acc.2.1.sb[reqs.toArray[v/64]!.link/n]!) &&
      decide (reqs.toArray[v/64]!.incs.getD (v%64) 0≤acc.2.1.rb[reqs.toArray[v/64]!.link%n]!))=true
  · simp only [ProcModelStep.entryStep,hok,ite_true,hu,hd,Bool.not_true,
      Bool.false_eq_true,ite_false,Bool.true_and]
    split <;> simp [bind,Except.bind,pure,Except.pure]
  · simp only [ProcModelStep.entryStep,hok,ite_false]
    have hf : (allowed[reqs.toArray[v/64]!.link]! &&
      decide (reqs.toArray[v/64]!.incs.getD (v%64) 0≤acc.2.1.sb[reqs.toArray[v/64]!.link/n]!) &&
      decide (reqs.toArray[v/64]!.incs.getD (v%64) 0≤acc.2.1.rb[reqs.toArray[v/64]!.link%n]!))=false := by
      exact Bool.eq_false_iff.mpr hok
    simp [hf,bind,Except.bind,pure,Except.pure]
end ZkFormal.NearV3.Candidates.ProcModelEntrySuccess
