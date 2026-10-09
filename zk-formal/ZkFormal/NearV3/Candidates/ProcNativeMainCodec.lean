import ZkFormal.NearV3.Candidates.ProcNativeForwardChunk
import ZkFormal.NearV3.Candidates.ProcActualSegmentGrant
import ZkFormal.NearV3.Candidates.ProcActualNativeFinish
import ZkFormal.NearV3.Assembly.SchedulerStateSize
namespace ZkFormal.NearV3.Candidates.ProcNativeMainCodec
open NearSpec NearSpecV3 NearSpecV3.Scheduler
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly

/-- Native main-chunk acceptance constructs corrected scheduler and codec
outputs. Forwarding bounds come from this execution, not a supplied guard. -/
theorem native_main {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (ctx : ApplyCtx) (sp : SchedPub)
    (hsp : sp∈p.sched) (hpub : schedPub ctx=some sp) (hids : ctx.layout.shardIds.Nodup)
    (t : PTrie) (receipts : List Receipt) (out : MainOut)
    (hchunk : applyNewChunk prims ctx t receipts=.ok out) (vid : Nat) :
    ∃old prev R gd result,
      readKey t keyBwState "bandwidth scheduler state"=.ok old ∧
      ProcActualCore.decodePrevious old=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) 0=.ok R ∧
      ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gd
        (fwdLinks ctx out.outgoing)=.ok result := by
  obtain ⟨mid,so,hstep,hbound⟩ := ProcNativeForwardChunk.chunk_demand_grant prims ctx t receipts out hchunk
  obtain ⟨old,sp',nativeOut,hread,hpub',hcore,hso,_⟩ := schedStep_complete hstep
  have he := Option.some.inj (hpub'.symm.trans hpub)
  subst sp'
  have hs := prepD0_sched hp sp hsp
  obtain ⟨prev,cv,st,rs,ev,hprev,hprefix,_,_⟩ :=
    ProcActualPrefix.prepared_prefix hp sp hsp ctx hpub old nativeOut hcore
  obtain ⟨R,hr⟩ := ProcActualPreparedGenerator.run_success sp hs prev 0 cv st rs ev hprefix
  obtain ⟨gd,sord,rord,hgd⟩ := ProcActualNativeFinish.distribution_exists (ProcPreparedSequence.input sp prev) st
  have hfinish := ProcActualNativeFinish.prefix_finish ctx sp hs hpub old nativeOut hcore prev hprev cv st rs ev hprefix
  have hidsEq := ZkFormal.NearV3.Assembly.schedPub_ids hpub
  have hdem : ProcPriorCodecForwardBound.Demands R gd (fwdLinks ctx out.outgoing) := by
    apply ProcPriorCodecForwardBound.native_links
    intro o ho d hd r hri
    have hg := ProcActualSegmentGrant.native_lookup sp hs (ProcActualPublic.schedPub_fields ctx sp hpub).1
      prev 0 cv rs st ev R gd sord rord hprefix hr hgd (by rwa [hidsEq])
      ctx.own d.1 o r (by rwa [hidsEq]) (by rwa [hidsEq])
    rw [hfinish,hidsEq] at hg
    have hb := hbound d hd
    rw [←hso] at hb
    change d.2≤((nativeOut.granted.find? (·.1==(ctx.own,d.1))).map Prod.snd).getD 0 at hb
    rwa [hg] at hb
  obtain ⟨result,hresult⟩ := ProcPriorCodecForwardBound.decoded_codec sp hs old prev hprev 0 R hr vid gd _ (fun _=>hdem)
  exact ⟨old,prev,R,gd,result,hread,hprev,hr,hresult⟩
end ZkFormal.NearV3.Candidates.ProcNativeMainCodec
