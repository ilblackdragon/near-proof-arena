import ZkFormal.NearV3.Candidates.ProcNativeMainCodec
import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks
namespace ZkFormal.NearV3.Candidates.ProcNativeCodecBlock
open NearSpec NearSpecV3 ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest

/-- Construct the operational codec block consumed by DIGEST assembly from
successful native main execution and its validated scheduler-upsert witness. -/
theorem main_block {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (w : SchedulerUpsertWitness) (hw : w.Valid)
    (sp : Scheduler.SchedPub) (hsp : sp∈p.sched) (hpub : schedPub w.ctx=some sp)
    (receipts : List Receipt) (out : MainOut)
    (hc : applyNewChunk prims w.ctx w.pre receipts=.ok out) (vid : Nat) :
    ∃b : NativeBlock,b.Valid ∧ b.witness=w ∧ b.pub=sp ∧ b.vid=vid ∧
      b.forwarded=fwdLinks w.ctx out.outgoing ∧ b.run.tau=0 ∧ b.run.n≤64 := by
  obtain ⟨old,prev,R,gd,result,hread,hprev,hr,hresult⟩ :=
    ProcNativeMainCodec.native_main hp w.ctx sp hsp hpub w.pre receipts out hc vid
  refine ⟨⟨w,sp,old,prev,R,vid,gd,fwdLinks w.ctx out.outgoing,result⟩,
    ⟨hw,hread,hpub,hprev,hresult⟩,rfl,rfl,rfl,rfl,?_,?_⟩
  · exact (ProcActualRunProjection.run_fields _ 0 R hr).1
  · have hn := (ProcActualRunProjection.run_fields _ 0 R hr).2.1
    rw [hn]
    exact (prepD0_sched hp sp hsp).n64
/-- Native execution also constructs the scheduler-upsert witness required by
assembly; neither block validity nor witness validity is assumed. -/
theorem main_block_exists {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (ctx : ApplyCtx) (sp : Scheduler.SchedPub)
    (hsp : sp∈p.sched) (hpub : schedPub ctx=some sp)
    (pre : PTrie) (receipts : List Receipt) (out : MainOut)
    (hc : applyNewChunk prims ctx pre receipts=.ok out) (vid : Nat) :
    ∃b : NativeBlock,b.Valid ∧ b.witness.ctx=ctx ∧ b.witness.pre=pre ∧
      b.pub=sp ∧ b.vid=vid ∧ b.forwarded=fwdLinks ctx out.outgoing ∧
      b.run.tau=0 ∧ b.run.n≤64 := by
  obtain ⟨mid,so,_,hstep,_⟩ := ProcNativeForwardChunk.chunk_forward prims ctx pre receipts out hc
  obtain ⟨_,_,_,_,_,_,_,hu⟩ := schedStep_complete hstep
  obtain ⟨run,hr,he⟩ := Render.UpsGen.traceUpsert_complete hu
  let w : SchedulerUpsertWitness := ⟨ctx,pre,so.state,run⟩
  have hw : w.Valid := ⟨hr,so,by simpa only [w,he] using hstep,rfl⟩
  obtain ⟨b,hb,hw',hsp',hvid,hf,ht,hn⟩ := main_block hp w hw sp hsp hpub receipts out hc vid
  exact ⟨b,hb,by rw [hw'],by rw [hw'],hsp',hvid,hf,ht,hn⟩
end ZkFormal.NearV3.Candidates.ProcNativeCodecBlock
