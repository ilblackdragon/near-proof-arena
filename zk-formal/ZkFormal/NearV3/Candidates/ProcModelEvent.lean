import ZkFormal.NearV3.Candidates.ProcGrantAgreement
namespace ZkFormal.NearV3.Candidates.ProcModelEvent
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

/-- Exact event recorded by a successful process entry. -/
def event (n : Nat) (allowed : Array Bool) (reqs : List Req) (v t : Nat) (st : PState) : Step :=
  let q := reqs.toArray[v/64]!
  let inc := q.incs.getD (v%64) 0
  let ok := allowed[q.link]! && decide (inc≤st.sb[q.link/n]!) && decide (inc≤st.rb[q.link%n]!)
  ⟨t,v,q.link,inc,v%64+1==q.incs.length,ok,
    (ProcGrantAgreement.modelGrant n allowed q.link inc st).al[q.link]!⟩

/-- The model appends the exact event, including denied grants and re-pushes. -/
theorem entry_emits (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out => out.2.2.2=s.2.2.2++[event n allowed reqs v s.2.2.1 s.2.1]) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals simp_all only [ExceptLoop.StepInv,event,ProcGrantAgreement.modelGrant,Bool.false_and,Bool.false_eq_true,ite_true,ite_false]
/-- Fields checked by the replay generator for a converted request. -/
def replayEvent (allowed : Array Bool) (c : CReq) (v t : Nat) (st : PState) : Step :=
  let inc := c.incs[v%64]!
  let ok := decide (inc≤st.sb[c.s]!) && decide (inc≤st.rb[c.r]!) && allowed[c.link]!
  ⟨t,v,c.link,inc,decide (c.incs.length-v%64-1=0),ok,
    if ok then st.al[c.link]!-inc else st.al[c.link]!⟩

/-- Native model and replay event fields agree at valid converted coordinates. -/
theorem event_eq_replay (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (c : CReq) (v t : Nat) (st : PState)
    (hq : reqs.toArray[v/64]! =⟨c.link,c.incs⟩)
    (hr : c.r<n) (hc : c.link=c.s*n+c.r)
    (hj : v%64<c.incs.length) (ha : c.link<st.al.size) :
    event n allowed reqs v t st=replayEvent allowed c v t st := by
  obtain ⟨hd,hm⟩ := ProcGrantAgreement.coordinates n c.s c.r c.link hr hc
  have hlast : (v%64+1==c.incs.length)=decide (c.incs.length-v%64-1=0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    omega
  have hinc : c.incs.getD (v%64) 0=c.incs[v%64]! := by simp [List.getD,getElem!_def,hj]
  simp only [event,hq,hd,hm,hinc,hlast,replayEvent,ProcGrantAgreement.modelGrant]
  cases hS : decide (c.incs[v%64]!≤st.sb[c.s]!) <;>
    cases hR : decide (c.incs[v%64]!≤st.rb[c.r]!) <;>
    cases hA : allowed[c.link]! <;>
    simp [hd,hm,hS,hR,hA,getElem!_set!_self,ha]

end ZkFormal.NearV3.Candidates.ProcModelEvent
