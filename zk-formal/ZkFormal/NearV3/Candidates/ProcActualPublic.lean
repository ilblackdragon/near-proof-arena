import ZkFormal.NearV3.Candidates.ProcActualCore
import ZkFormal.NearV3.Candidates.ProcPreviousStateRegression
namespace ZkFormal.NearV3.Candidates.ProcActualPublic
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched

theorem pubOf_fields (cfg : Config) (cc : CongestionConfig) (ids : List Nat)
    (congestion : List (Nat×CongestionInfo×Nat)) (requests : List (Nat×List BandwidthRequest))
    (seed : Bytes) (sp : SchedPub) (h : pubOf cfg cc ids congestion requests seed=some sp) :
    sp.allowed.size=sp.ids.length*sp.ids.length ∧ sp.values=requestValues sp.params := by
  unfold pubOf at h
  dsimp only at h
  split at h
  · cases h
  · cases hp : Params.calculate cfg ids.length with
    | none => simp [hp,bind,Option.bind] at h
    | some p =>
      simp only [hp,bind,Option.bind,Option.some.injEq] at h
      subst sp
      exact ⟨by simp,rfl⟩

theorem schedPub_fields (ctx : ApplyCtx) (sp : SchedPub) (h : schedPub ctx=some sp) :
    sp.allowed.size=sp.ids.length*sp.ids.length ∧ sp.values=requestValues sp.params :=
  pubOf_fields _ _ _ _ _ _ sp h

/-- Actual prepared scheduler public input and successful native core execution
construct the repaired process without canonical previous-state restrictions. -/
theorem scheduled_process_exists (ctx : ApplyCtx) (sp : SchedPub) (hs : SchedPubOk sp)
    (hpub : schedPub ctx=some sp) (oldBytes : Option Bytes) (out : Output)
    (h : runCore sp oldBytes=some out) :
    ∃prev st rs,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs) :=
  ProcActualCore.process_exists sp hs (schedPub_fields ctx sp hpub).1
    (schedPub_fields ctx sp hpub).2 oldBytes out h

/-- The repaired input reads the actual foreign-ID regression exactly as native
execution does, while preserving its original previous-state bytes. -/
theorem regression_allowance :
    (ProcActualInput.allowances ProcPreviousStateRegression.pub.ids ProcPreviousStateRegression.previous)[0]! =0 := by decide +kernel

theorem regression_initial :
    (ProcActualInput.initial ProcPreviousStateRegression.input).al[0]! =2250000 := by decide +kernel

theorem regression_original_bytes :
    ProcPreviousStateRegression.input.prev.encode=ProcPreviousStateRegression.previous.encode := rfl
end ZkFormal.NearV3.Candidates.ProcActualPublic
