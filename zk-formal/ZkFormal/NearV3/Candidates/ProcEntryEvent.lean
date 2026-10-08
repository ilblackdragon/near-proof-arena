import ZkFormal.NearV3.Candidates.ProcConvertedLinks
namespace ZkFormal.NearV3.Candidates.ProcEntryEvent
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler ProcGrantAgreement
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def event (n : Nat) (allowed : Array Bool) (q : Req) (v t : Nat) (st : PState) : Step :=
  let inc := q.incs.getD (v%64) 0
  ⟨t,v,q.link,inc,v%64+1==q.incs.length,
    allowed[q.link]! && decide (inc≤st.sb[q.link/n]!) && decide (inc≤st.rb[q.link%n]!),
    (modelGrant n allowed q.link inc st).al[q.link]!⟩

theorem entry_event (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>out.2.2.2=s.2.2.2++[event n allowed reqs.toArray[v/64]! v s.2.2.1 s.2.1]) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals simp_all only [ExceptLoop.StepInv,event,modelGrant,Bool.false_eq_true,ite_true,ite_false]

theorem last_eq_rem (j len : Nat) (hj : j<len) : (j+1==len)=(len-j-1==0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  omega

def replayEvent (allowed : Array Bool) (c : CReq) (v t : Nat) (st : PState) : Step :=
  let inc := c.incs[v%64]!
  let ok := decide (inc≤st.sb[c.s]!) && decide (inc≤st.rb[c.r]!) && allowed[c.link]!
  ⟨t,v,c.link,inc,c.incs.length-v%64-1==0,ok,
    if ok then st.al[c.link]!-inc else st.al[c.link]!⟩

/-- All compared event fields agree with the generator expression at a valid
native request increase. The link-array bound is an ordinary state-shape fact. -/
theorem selected_event (I : Input) (cv : Array CReq)
    (h : forIn I.raw #[] (ProcConverted.step I)=.ok cv)
    (v t : Nat) (hi : v/64<cv.size) (hj : v%64<cv[v/64]!.incs.length)
    (st : PState) (hl : cv[v/64]!.link<st.al.size) :
    event I.ids.length I.allowed (ProcConversionExact.view cv).toArray[v/64]! v t st=
      replayEvent I.allowed cv[v/64]! v t st := by
  rw [ProcConvertedLinks.view_get cv (v/64) hi]
  have hlinks := ProcConvertedLinks.indexed_link I cv h (v/64) hi
  have hmem : cv[v/64]!∈cv.toList := by
    rw [getElem!_pos cv (v/64) hi]
    exact List.mem_iff_getElem.mpr ⟨v/64,hi,Array.getElem_toList hi⟩
  have hr := (ProcConvertedFacts.loop_facts I cv h _ hmem).2.1
  obtain ⟨hd,hm⟩ := coordinates _ _ _ _ hr hlinks
  have hinc : cv[v/64]!.incs.getD (v%64) 0=cv[v/64]!.incs[v%64]! := by
    simp [List.getD_eq_getElem?_getD,getElem!_pos cv[v/64]!.incs (v%64) hj,List.getElem?_eq_getElem hj]
  have hlast := last_eq_rem (v%64) _ hj
  unfold event replayEvent
  simp only [hinc,hd,hm,hlast]
  cases hS : decide (cv[v/64]!.incs[v%64]!≤st.sb[cv[v/64]!.s]!) <;>
    cases hR : decide (cv[v/64]!.incs[v%64]!≤st.rb[cv[v/64]!.r]!) <;>
    cases hL : I.allowed[cv[v/64]!.link]! <;>
    simp only [modelGrant,hd,hm,hS,hR,hL,Bool.false_and,Bool.and_false,
      Bool.true_and,Bool.and_true,Bool.false_eq_true,ite_false,ite_true,
      Array.getElem!_set!_self _ _ _ hl]

theorem entry_replay_event (I : Input) (cv : Array CReq)
    (hc : forIn I.raw #[] (ProcConverted.step I)=.ok cv)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (hi : v/64<cv.size) (hj : v%64<cv[v/64]!.incs.length)
    (hl : cv[v/64]!.link<s.2.1.al.size)
    (h : ProcModelStep.entryStep I.ids.length I.allowed (ProcConversionExact.view cv) K z v s=.ok out) :
    ExceptLoop.StepInv (fun out=>out.2.2.2=s.2.2.2++[replayEvent I.allowed cv[v/64]! v s.2.2.1 s.2.1]) out := by
  have he := entry_event I.ids.length I.allowed (ProcConversionExact.view cv) K z v s out h
  have hv := selected_event I cv hc v s.2.2.1 hi hj s.2.1 hl
  cases out <;> simpa only [ExceptLoop.StepInv,hv] using he
end ZkFormal.NearV3.Candidates.ProcEntryEvent
