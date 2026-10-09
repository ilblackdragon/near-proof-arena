import ZkFormal.NearV3.Candidates.ProcActualRequestCount
namespace ZkFormal.NearV3.Candidates.ProcActualConversionSuccess
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def RawValid (I : Input) : Prop :=
  ∀q∈I.raw,q.bm.length=5 ∧ q.s<I.ids.length ∧ q.r<I.ids.length

theorem step_success (I : Input) (q : RawReq) (cv : Array CReq)
    (hb : q.bm.length=5) (hs : q.s<I.ids.length) (hr : q.r<I.ids.length) :
    ∃next,ProcActualConverted.step I q cv=.ok (.yield next) := by
  by_cases ht : (setBits q.bm).isEmpty=true
  all_goals simp [ProcActualConverted.step,ht,check,hb,hs,hr,bind,Except.bind,pure,Except.pure]

theorem loop_success (I : Input) (qs : List RawReq) (cv : Array CReq)
    (hq : ∀q∈qs,q.bm.length=5 ∧ q.s<I.ids.length ∧ q.r<I.ids.length) :
    ∃out,forIn qs cv (ProcActualConverted.step I)=.ok out := by
  induction qs generalizing cv with
  | nil => exact ⟨cv,rfl⟩
  | cons q qs ih =>
    have hh := hq q (by simp)
    obtain ⟨next,hn⟩ := step_success I q cv hh.1 hh.2.1 hh.2.2
    obtain ⟨out,ho⟩ := ih next (fun x hx=>hq x (by simp [hx]))
    exact ⟨out,by simp only [List.forIn_cons,hn,bind,Except.bind]; exact ho⟩

theorem conversion_success (I : Input) (h : RawValid I) :
    ∃out,forIn I.raw #[] (ProcActualConverted.step I)=.ok out ∧ out.size≤I.raw.length := by
  obtain ⟨out,ho⟩ := loop_success I I.raw #[] h
  exact ⟨out,ho,ProcActualRequestCount.loop_count I out ho⟩
end ZkFormal.NearV3.Candidates.ProcActualConversionSuccess
