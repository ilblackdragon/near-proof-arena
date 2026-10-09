import ZkFormal.NearV3.Candidates.ProcActualConversionExact
namespace ZkFormal.NearV3.Candidates.ProcActualCoreReplay
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

abbrev initial := ProcActualInput.initial
abbrev process := ProcActualInput.process

/-- The two model calls inside the generator necessarily have identical rounds;
this does not postulate agreement with the external native scheduler. -/
theorem core_rounds (I : Input) (st : PState) (rs : List Round) (ev : Ev)
    (hp : process I=.ok (st,rs))
    (hc : ActualRun.coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev=.ok ev) : ev.rounds=rs := by
  unfold process ProcActualInput.process ProcActualInput.initial at hp
  unfold ActualRun.coreEv at hc
  simp only [hp,bind,Except.bind] at hc
  cases hd : distributeEv I.ids.length I.allowed st.sb st.rb
      (linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).cntS
      (linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).cntR with
  | error e => simp only [hd] at hc; cases hc
  | ok out =>
    rcases out with ⟨gd,sord,rord⟩
    simp only [hd,pure,Except.pure,Except.ok.injEq] at hc
    subst ev
    rfl

def roundCheck (a b : Round) : Except String (ForInStep Unit) := do
  check (a.key==b.key && a.z==b.z && a.shuffled==b.shuffled &&
    a.steps.map (fun s=>(s.t,s.v,s.ok,s.aOut)) == b.steps.map (fun s=>(s.t,s.v,s.ok,s.aOut)))
    "coreEv round differs"
  return .yield ()

theorem roundCheck_self (a : Round) : roundCheck a a=.ok (.yield ()) := by
  simp [roundCheck,check,bind,Except.bind,pure,Except.pure]

theorem roundChecks_self (rs : List Round) :
    forIn (rs.zip rs) () (fun ab _=>roundCheck ab.1 ab.2)=.ok () := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simpa only [List.zip_cons_cons,List.forIn_cons,roundCheck_self,bind,Except.bind] using ih

theorem checked_core_rounds (I : Input) (st : PState) (rs : List Round) (ev : Ev)
    (hp : process I=.ok (st,rs))
    (hc : ActualRun.coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev=.ok ev) :
    check (ev.rounds.length==rs.length) "coreEv rounds differ"=.ok () ∧
    forIn (ev.rounds.zip rs) () (fun ab _=>roundCheck ab.1 ab.2)=.ok () := by
  rw [core_rounds I st rs ev hp hc]
  exact ⟨by simp [check,pure,Except.pure],roundChecks_self rs⟩
end ZkFormal.NearV3.Candidates.ProcActualCoreReplay
