import ZkFormal.NearV3.Candidates.ProcNativeMainCodecWitness
import ZkFormal.NearV3.Candidates.ProcCodecNativeLocal
namespace ZkFormal.NearV3.Candidates.ProcNativeNonmainCodecLocal
open NearSpec NearSpecV3 NearSpecV3.Scheduler
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly

/-- A prepared scheduler instance index is an actual field element; no external
timestamp bound is needed. Preparation bounds all main/implicit calls by 33. -/
theorem index_bound {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (tau : Nat) (sp : SchedPub)
    (hindex : p.sched[tau]?=some sp) : tau<ZkFormal.Algebra.P := by
  have hi := (List.getElem?_eq_some_iff.mp hindex).1
  have hl := ZkFormal.NearV3.Sched.prepD0_len hp
  have hP : 33<ZkFormal.Algebra.P := by decide +kernel
  omega

/-- Non-main native scheduler acceptance constructs both corrected generators
and full Codec local validity with the exact same process/distribution state. -/
theorem native_nonmain {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (tau : Nat)
    (hindex : p.sched[tau]?=some sp) (ht : tau≠0)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (old : Option Bytes) (nativeOut : Output) (hcore : runCore sp old=some nativeOut)
    (vid : Nat) (fwd : List (Nat×Nat)) :
    ∃prev cv st rs ev R gd sord rord result,
      ProcActualCore.decodePrevious old=some prev ∧
      ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev) ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R ∧
      distributeEv sp.ids.length sp.allowed st.sb st.rb
        (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
        (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
          =.ok (gd,sord,rord) ∧
      ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gd fwd=.ok result ∧
      ∀(traceTime : Nat) (pub : List Fp),
        ZkFormal.Near.TableLocal ProcPriorCodecActual.table
          (SchedHeight.trace result.rows codecPad) traceTime pub := by
  have hsp : sp∈p.sched := List.mem_iff_getElem?.mpr ⟨tau,hindex⟩
  have hs := prepD0_sched hp sp hsp
  have ha := (ProcActualPublic.schedPub_fields ctx sp hpub).1
  obtain ⟨prev,cv,st,rs,ev,hprev,hprefix,_,_⟩ :=
    ProcActualPrefix.prepared_prefix hp sp hsp ctx hpub old nativeOut hcore
  obtain ⟨R,hr⟩ := ProcActualPreparedGenerator.run_success sp hs prev tau cv st rs ev hprefix
  obtain ⟨gd,sord,rord,hgd⟩ := ProcActualNativeFinish.distribution_exists (ProcPreparedSequence.input sp prev) st
  have hτ := (ProcActualRunProjection.run_fields _ tau R hr).1
  obtain ⟨result,hcodec⟩ := ProcPriorCodecNativeTotal.decoded_codec_success sp hs old prev hprev tau R hr vid gd fwd
    (by intro k hk hz; exact (ht (hτ.symm.trans hz)).elim)
  refine ⟨prev,cv,st,rs,ev,R,gd,sord,rord,result,hprev,hprefix,hr,hgd,hcodec,?_⟩
  intro traceTime pub
  exact ProcCodecNativeLocal.table sp hs ha prev tau cv rs st ev R gd sord rord hprefix hr hgd
    old.isSome vid fwd result hcodec (by rw [hτ]; exact index_bound hp tau sp hindex) traceTime pub

/-- The accepted missing-chunk transition supplies the real trie read and
native scheduler execution. Its scheduler index supplies the timestamp bound. -/
theorem missing_chunk {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (tau : Nat)
    (hindex : p.sched[tau]?=some sp) (ht : tau≠0)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (pre post : PTrie) (hchunk : applyMissingChunk prims ctx pre=.ok post) (vid : Nat) :
    ∃old prev R gd result,
      readKey pre keyBwState "bandwidth scheduler state"=.ok old ∧
      ProcActualCore.decodePrevious old=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R ∧
      ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gd []=.ok result ∧
      ∀(traceTime : Nat) (pub : List Fp),
        ZkFormal.Near.TableLocal ProcPriorCodecActual.table
          (SchedHeight.trace result.rows codecPad) traceTime pub := by
  unfold applyMissingChunk at hchunk
  obtain ⟨_,_,hchunk⟩ := ReexecV3D0.bind_ok' hchunk
  obtain ⟨⟨mid,so⟩,hstep,_⟩ := ReexecV3D0.bind_ok' hchunk
  obtain ⟨old,sp',nativeOut,hread,hpub',hcore,_,_⟩ := schedStep_complete hstep
  have he := Option.some.inj (hpub'.symm.trans hpub)
  subst sp'
  obtain ⟨prev,cv,st,rs,ev,R,gd,sord,rord,result,hprev,hprefix,hr,hgd,hcodec,hlocal⟩ :=
    native_nonmain hp sp tau hindex ht ctx hpub old nativeOut hcore vid []
  exact ⟨old,prev,R,gd,result,hread,hprev,hr,hcodec,hlocal⟩
end ZkFormal.NearV3.Candidates.ProcNativeNonmainCodecLocal
