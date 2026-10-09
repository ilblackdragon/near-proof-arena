import ZkFormal.NearV3.Candidates.ProcActualAfterMemoryReduction
import ZkFormal.NearV3.Candidates.ProcDistGridAgreement
namespace ZkFormal.NearV3.Candidates.ProcActualNativeFinish
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Event distribution exists for the exact original-prior link-pass counts;
no process-success or final-generator premise is needed for this stage. -/
theorem distribution_exists (I : Input) (st : PState) :
    ∃gd sord rord,distributeEv I.ids.length I.allowed st.sb st.rb
      (linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).cntS
      (linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).cntR =
        .ok (gd,sord,rord) := by
  obtain ⟨⟨gd,sord,rord⟩,hh⟩ := ProcDistEventTotal.link_pass_exists I.ids.length I.p I.allowed
    (ProcActualInput.allowances I.ids I.prev) st.sb st.rb
  exact ⟨gd,sord,rord,hh⟩

/-- Native output agreement applies to the same decoded previous state and
same successful process, by determinism of decoding and execution. -/
theorem process_finish (ctx : ApplyCtx) (sp : SchedPub) (hs : SchedPubOk sp)
    (hpub : schedPub ctx=some sp) (oldBytes : Option Bytes) (nativeOut : Output)
    (hcore : runCore sp oldBytes=some nativeOut) (prev : Bandwidth.State)
    (hprev : ProcActualCore.decodePrevious oldBytes=some prev) (st : PState) (rs : List Round)
    (hp : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ProcActualNativeResult.finish sp prev (ProcNativeGrant.native st)=nativeOut := by
  obtain ⟨prev',st',rs',hprev',hp',hout⟩ :=
    ProcActualNativeResult.scheduled_process_output ctx sp hs hpub oldBytes nativeOut hcore
  have he := Option.some.inj (hprev'.symm.trans hprev)
  subst prev'
  have he := Except.ok.inj (hp'.symm.trans hp)
  have hst := congrArg Prod.fst he
  change st'=st at hst
  subst st'
  exact hout

/-- A successful prepared prefix supplies the process identity needed to bind
native finish, without changing the prefix's state witness. -/
theorem prefix_finish (ctx : ApplyCtx) (sp : SchedPub) (hs : SchedPubOk sp)
    (hpub : schedPub ctx=some sp) (oldBytes : Option Bytes) (nativeOut : Output)
    (hcore : runCore sp oldBytes=some nativeOut) (prev : Bandwidth.State)
    (hprev : ProcActualCore.decodePrevious oldBytes=some prev)
    (cv : Array CReq) (st : PState) (rs : List Round) (ev : Ev)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev)) :
    ProcActualNativeResult.finish sp prev (ProcNativeGrant.native st)=nativeOut :=
  process_finish ctx sp hs hpub oldBytes nativeOut hcore prev hprev st rs
    (ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev hprefix).2
end ZkFormal.NearV3.Candidates.ProcActualNativeFinish
