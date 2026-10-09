import ZkFormal.NearV3.Candidates.ProcNativeMainCodecLocal
import ZkFormal.NearV3.Assembly.SchedulerCodecRepairedDigests
import ZkFormal.NearV3.Assembly.SchedulerSizedWitness

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 NearSpecV3.Scheduler Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The native main execution supplies a concrete block, its operational
scheduler witness, and local legality of these same generated rows. -/
theorem native_main_block {cb : Bytes} {hint : Hint} {p : Prep}
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
      ∀ (time : Nat) (pub : List Fp), TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace b.output.rows codecPad) time pub := by
  obtain ⟨old,prev,R,gd,result,hread,hdecode,hr,hgen,hlocal⟩ :=
    ProcNativeMainCodecLocal.native_main hp ctx sp hsp hpub pre receipts out hchunk vid
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
  exact ⟨b,hu,hpre,hctx,rfl,rfl,rfl,hb,hr,hfields.1,hn,hlocal⟩

/-- For a concrete main block, the repaired physical table consumes exactly
its native sanity digest. This is independent of multi-block splicing. -/
theorem main_block_digest_count (b : NativeBlock) (hb : b.Valid)
    (ht : b.run.tau=0) (hn : b.run.n≤64) (time : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace b.output.rows codecPad) time pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests [schedulerSanityJob 0 b.witness]).map Msg.toFp).count msg := by
  have hh := native_codec_digest_count [b] (by simp) (by simpa using And.intro hb hn)
    (by
      intro i x hx
      cases i with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hx
                subst x; exact ht
      | succ i => simp at hx) time pub msg
  rw [repaired_digest_count]
  simpa [nativeBlockRows,schedulerSanityJobs] using hh

end ZkFormal.NearV3.Assembly.CodecDigest
