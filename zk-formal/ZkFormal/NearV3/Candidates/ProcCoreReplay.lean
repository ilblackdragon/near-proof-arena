import ZkFormal.NearV3.Candidates.ProcConversionExact
namespace ZkFormal.NearV3.Candidates.ProcCoreReplay
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def initial (I : Input) : PState :=
  let lp := linkPass I.ids.length I.p I.allowed (a0Src I.ids I.prev)
  ⟨lp.sb,lp.rb,lp.a2,lp.g2,NearSpecV3.Rng.ofSeed I.seed⟩

def process (I : Input) : Except String (PState×List Round) :=
  let reqs := convRaw I.p I.ids.length I.raw
  processEv I.ids.length I.allowed reqs (initial I) (1+(reqs.map (·.incs.length)).sum)

/-- The two model calls inside the generator necessarily have identical rounds;
this does not postulate agreement with the external native scheduler. -/
theorem core_rounds (I : Input) (st : PState) (rs : List Round) (ev : Ev)
    (hp : process I=.ok (st,rs))
    (hc : coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev=.ok ev) : ev.rounds=rs := by
  unfold process initial at hp
  unfold coreEv at hc
  simp only [hp,bind,Except.bind] at hc
  cases hd : distributeEv I.ids.length I.allowed st.sb st.rb
      (linkPass I.ids.length I.p I.allowed (a0Src I.ids I.prev)).cntS
      (linkPass I.ids.length I.p I.allowed (a0Src I.ids I.prev)).cntR with
  | error e => simp only [hd,bind,Except.bind] at hc; cases hc
  | ok out =>
    rcases out with ⟨gd,sord,rord⟩
    simp only [hd,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at hc
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
    (hc : coreEv I.ids I.p I.allowed I.raw I.seed I.ash I.prev=.ok ev) :
    check (ev.rounds.length==rs.length) "coreEv rounds differ"=.ok () ∧
    forIn (ev.rounds.zip rs) () (fun ab _=>roundCheck ab.1 ab.2)=.ok () := by
  rw [core_rounds I st rs ev hp hc]
  exact ⟨by simp [check,pure,Except.pure],roundChecks_self rs⟩
end ZkFormal.NearV3.Candidates.ProcCoreReplay
