import ZkFormal.NearV3.Assembly.SchedulerCodecMainBlock
import ZkFormal.NearV3.Candidates.ProcNativeNonmainCodecLocal
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 NearSpecV3.Scheduler Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- An actual missing-chunk call supplies the block at its prepared index,
including local legality and the identical operational upsert witness. -/
theorem native_missing_block {cb : Bytes} {hint : Hint} {p : Prep}
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
      ∀ (time : Nat) (pub : List Fp), TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace b.output.rows codecPad) time pub := by
  obtain ⟨old,prev,R,gd,result,hread,hdecode,hr,hgen,hlocal⟩ :=
    ProcNativeNonmainCodecLocal.missing_chunk hp sp tau hindex ht ctx hpub pre post hchunk vid
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
  exact ⟨b,hu,hpre,hctx,rfl,rfl,rfl,hb,hr,hfields.1,hn,hlocal⟩
end ZkFormal.NearV3.Assembly.CodecDigest
