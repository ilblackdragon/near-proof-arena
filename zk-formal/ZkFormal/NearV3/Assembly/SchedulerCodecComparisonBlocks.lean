import ZkFormal.NearV3.Candidates.ProcNativeCodecComparisonWitness
import ZkFormal.NearV3.Assembly.SchedulerCodecRepairedDigests
import ZkFormal.NearV3.Assembly.SchedulerSizedWitness

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 NearSpecV3.Scheduler Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The native main execution supplies a concrete block, its operational
scheduler witness, and local legality of these same generated rows. -/
theorem native_main_comparison_block {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (ctx : ApplyCtx) (sp : SchedPub)
    (hsp : sp∈p.sched) (hpub : schedPub ctx=some sp)
    (pre : PTrie) (receipts : List Receipt) (out : MainOut)
    (hchunk : applyNewChunk prims ctx pre receipts=.ok out) (vid : Nat) :
    ∃ b : NativeBlock,
      schedulerUpsertWitness ctx pre=.ok b.witness ∧
      b.witness.pre=pre ∧ b.witness.ctx=ctx ∧ b.pub=sp ∧ b.vid=vid ∧
      b.forwarded=fwdLinks ctx out.outgoing ∧ b.Valid ∧
      ActualRun.run (ProcPreparedSequence.input b.pub b.old) 0=.ok b.run ∧
      b.run.tau=0 ∧ b.run.n≤64 ∧
      (∀q∈b.output.cmps, Sched.Complete.CmpOk q) ∧
      ∀ (time : Nat) (pub : List Fp), TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace b.output.rows codecPad) time pub := by
  obtain ⟨old,prev,R,gd,result,hread,hdecode,hr,hgen,hcmps,hlocal⟩ :=
    ProcNativeCodecComparisonWitness.native_main hp ctx sp hsp hpub pre receipts out hchunk vid
  obtain ⟨_,_,_,hsched,_,_⟩ := Qv.applyNewChunk_queue_reads hchunk
  obtain ⟨u,hu,hpre,hvalid⟩ := schedStep_upsert_witness hsched
  have hctx := schedulerUpsertWitness_ctx hu
  have hfields := ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) 0 R hr
  have hn : R.n≤64 := by
    rw [hfields.2.1]
    exact (prepD0_sched hp sp hsp).n64
  let b : NativeBlock := ⟨u,sp,old,prev,R,vid,gd,fwdLinks ctx out.outgoing,result⟩
  have hb : b.Valid := by
    refine ⟨hvalid,?_,?_,hdecode,hgen⟩
    · change readKey u.pre keyBwState _=.ok old
      rw [hpre]; exact hread
    · change schedPub u.ctx=some sp
      rw [hctx]; exact hpub
  exact ⟨b,hu,hpre,hctx,rfl,rfl,rfl,hb,hr,hfields.1,hn,hcmps,hlocal⟩

/-- An actual missing-chunk call supplies the block at its prepared index,
including local legality and the identical operational upsert witness. -/
theorem native_missing_comparison_block {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (tau : Nat)
    (hindex : p.sched[tau]?=some sp) (ht : tau≠0)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (pre post : PTrie) (hchunk : applyMissingChunk prims ctx pre=.ok post) (vid : Nat) :
    ∃ b : NativeBlock,
      schedulerUpsertWitness ctx pre=.ok b.witness ∧
      b.witness.pre=pre ∧ b.witness.ctx=ctx ∧ b.pub=sp ∧ b.vid=vid ∧
      b.forwarded=[] ∧ b.Valid ∧
      ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau=.ok b.run ∧
      b.run.tau=tau ∧ b.run.n≤64 ∧
      (∀q∈b.output.cmps, Sched.Complete.CmpOk q) ∧
      ∀ (time : Nat) (pub : List Fp), TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace b.output.rows codecPad) time pub := by
  obtain ⟨old,prev,R,gd,result,hread,hdecode,hr,hgen,hcmps,hlocal⟩ :=
    ProcNativeCodecComparisonWitness.missing_chunk hp sp tau hindex ht ctx hpub pre post hchunk vid
  have hh := hchunk
  unfold applyMissingChunk at hh
  obtain ⟨_,_,hh⟩ := ReexecV3D0.bind_ok' hh
  obtain ⟨⟨mid,so⟩,hsched,_⟩ := ReexecV3D0.bind_ok' hh
  obtain ⟨u,hu,hpre,hvalid⟩ := schedStep_upsert_witness hsched
  have hctx := schedulerUpsertWitness_ctx hu
  have hfields := ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tau R hr
  have hn : R.n≤64 := by
    rw [hfields.2.1]
    exact (prepD0_sched hp sp (List.mem_iff_getElem?.mpr ⟨tau,hindex⟩)).n64
  let b : NativeBlock := ⟨u,sp,old,prev,R,vid,gd,[],result⟩
  have hb : b.Valid := by
    refine ⟨hvalid,?_,?_,hdecode,hgen⟩
    · change readKey u.pre keyBwState _=.ok old
      rw [hpre]; exact hread
    · change schedPub u.ctx=some sp
      rw [hctx]; exact hpub
  exact ⟨b,hu,hpre,hctx,rfl,rfl,rfl,hb,hr,hfields.1,hn,hcmps,hlocal⟩
end ZkFormal.NearV3.Assembly.CodecDigest
