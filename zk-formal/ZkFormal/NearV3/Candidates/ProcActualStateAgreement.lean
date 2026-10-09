import ZkFormal.NearV3.Candidates.ProcActualNativeResult
import ZkFormal.NearV3.Candidates.ProcActualRun
namespace ZkFormal.NearV3.Candidates.ProcActualStateAgreement
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

/-- Distribution changes grants only, even without array-shape assumptions. -/
theorem grant_fold_allowance (ls : List Nat) (g : Array (Option Nat)) (st : St) :
    (ls.foldl (fun st l => match g[l]! with
      | some b => grantMore st l b | none => st) st).allowance=st.allowance := by
  induction ls generalizing st with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldl_cons,ih]
    cases g[l]! <;> simp [grantMore]

theorem distribute_allowance (n : Nat) (allowed : Array Bool) (st : St) :
    (distribute n allowed st).allowance=st.allowance := by
  unfold distribute
  exact grant_fold_allowance _ _ _

/-- The emitted state bytes agree with native reconstruction for the same
successful process. Distribution success is still an explicit premise. -/
theorem core_state (sp : SchedPub) (prev : NearSpec.Bandwidth.State)
    (st : PState) (rs : List Round) (ev : Ev)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hc : ActualRun.coreEv sp.ids sp.params sp.allowed (instOf sp).raw
      sp.seed sp.allShardsHash prev=.ok ev) :
    ev.state=(ProcActualNativeResult.finish sp prev (ProcNativeGrant.native st)).state := by
  unfold ProcActualInput.process ProcActualInput.initial ProcPreparedSequence.input at hp
  unfold ActualRun.coreEv at hc
  simp only [hp,bind,Except.bind] at hc
  cases hd : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR with
  | error e => simp only [hd] at hc; cases hc
  | ok out =>
    rcases out with ⟨gd,sord,rord⟩
    simp only [hd,pure,Except.pure,Except.ok.injEq] at hc
    subst ev
    simp only [ProcActualNativeResult.finish,distribute_allowance,ProcNativeGrant.native]
/-- Native core success fixes the poststate bytes of every successful corrected
core event for the same decoded prior state. No canonical-prior premise. -/
theorem scheduled_state (ctx : NearSpecV3.ApplyCtx) (sp : SchedPub)
    (hs : SchedPubOk sp) (hpub : NearSpecV3.schedPub ctx=some sp)
    (oldBytes : Option NearSpec.Bytes) (out : Output) (h : runCore sp oldBytes=some out)
    (prev : NearSpec.Bandwidth.State)
    (hprev : ProcActualCore.decodePrevious oldBytes=some prev) (ev : Ev)
    (hc : ActualRun.coreEv sp.ids sp.params sp.allowed (instOf sp).raw
      sp.seed sp.allShardsHash prev=.ok ev) : ev.state=out.state := by
  obtain ⟨prev',st,rs,hprev',hp,ho⟩ :=
    ProcActualNativeResult.scheduled_process_output ctx sp hs hpub oldBytes out h
  have he : prev'=prev := Option.some.inj (hprev'.symm.trans hprev)
  subst prev'
  rw [core_state sp prev st rs ev hp hc,ho]

end ZkFormal.NearV3.Candidates.ProcActualStateAgreement
