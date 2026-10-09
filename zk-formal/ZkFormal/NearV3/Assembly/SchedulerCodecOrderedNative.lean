import ZkFormal.NearV3.Assembly.SchedulerCodecImplicitBlocks
import ZkFormal.NearV3.Candidates.ProcCodecNativeConcatLocal
import ZkFormal.NearV3.Assembly.NativeTrace
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 NearSpecV3.Scheduler Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Main and missing chunks construct one ordered list of actual Codec blocks.
Each timestamp is the real prepared index, and all block premises are derived. -/
theorem native_ordered_blocks {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length=k.implicitBlks.length) (vids : Nat→Nat) :
    ∃main : NativeBlock,∃tail : List NativeBlock,
      tail.length=steps.length ∧
      schedulerUpsertWitness (m.ctx k) m.pre=.ok main.witness ∧
      main.witness.pre=m.pre ∧
      (∀i e b,steps[i]?=some e→tail[i]?=some b→MissingBlockAt k vids (1+i) e b) ∧
      ∀(i : Nat) (b : NativeBlock),(main::tail)[i]?=some b→b.Valid ∧ b.run.n≤64 ∧ b.run.tau=i ∧
        ∀time pub,TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) time pub := by
  obtain ⟨sp,hsp,hpub⟩ := prepD0_context_index hp hw hm 0 (m.ctx k) rfl
  obtain ⟨b,hb,hpre,hctx,hpub',hvid,hf,hvalid,hr,htau,hn,hlocal⟩ :=
    native_main_block hp (m.ctx k) sp (List.mem_iff_getElem?.mpr ⟨0,hsp⟩) hpub
      m.pre (appliedReceipts k w) m.result hm.run (vids 0)
  obtain ⟨bs,hbs,hAt⟩ := native_implicit_blocks hp hw hm hv hlen vids
  refine ⟨b,bs,hbs,hb,hpre,hAt,?_⟩
  intro i x hx
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hx
    subst x
    exact ⟨hvalid,hn,htau,hlocal⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hx
    have hi : i<steps.length := by
      have hh := (List.getElem?_eq_some_iff.mp hx).1
      omega
    let e := steps[i]
    have he : steps[i]?=some e := List.getElem?_eq_getElem hi
    have hh := hAt i e x he hx
    exact ⟨hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.1,
      by simpa [Nat.add_comm] using hh.2.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.2⟩

/-- Actual accepted native execution yields a locally legal corrected Codec
trace at the shared log22 clock, with at most32 blocks and no Local premise. -/
theorem accepted_codec_table {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (vids : Nat→Nat) :
    ∃bs : List NativeBlock,bs.length≤32 ∧
      (∀b∈bs,b.Valid ∧ b.run.n≤64) ∧
      (∀(i : Nat) (b : NativeBlock),bs[i]?=some b→b.run.tau=i) ∧
      ∀time pub,TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub := by
  obtain ⟨m,steps,last,hm,_,hv,hlen,hcount,_,_⟩ := checkD0a_native_trace hk hw h
  obtain ⟨main,tail,htail,_,_,_,hb⟩ := native_ordered_blocks hp hk hm hv hlen vids
  have hlen' : (main::tail).length≤32 := by simp only [List.length_cons]; omega
  have hvalid : ∀b∈main::tail,b.Valid ∧ b.run.n≤64 ∧
      TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 [] := by
    intro b hmem
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hmem
    have hh := hb i b hi
    exact ⟨hh.1,hh.2.1,hh.2.2.2 0 []⟩
  have horder : ∀(i : Nat) (b : NativeBlock),(main::tail)[i]?=some b→b.run.tau=i := fun i b hi=>(hb i b hi).2.2.1
  exact ⟨main::tail,hlen',fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩,horder,
    ProcCodecNativeConcatLocal.indexed_table _ (by omega) hvalid horder⟩

/-- Local legality and exact physical sanity-DIGEST conservation refer to the
same accepted native block list; no digest or local witness is supplied. -/
theorem accepted_codec_local_digest {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (vids : Nat→Nat) :
    ∃bs : List NativeBlock,bs.length≤32 ∧
      (∀b∈bs,b.Valid ∧ b.run.n≤64) ∧
      (∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i) ∧
      (∀time pub,TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub) ∧
      ∀time pub msg,tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub B_DIGEST false msg=
        ((Sha.Gen.expectedDigests (schedulerSanityJobs 0 (bs.map NativeBlock.witness))).map Msg.toFp).count msg := by
  obtain ⟨bs,hlen,hvalid,horder,hlocal⟩ := accepted_codec_table hp hk hw h vids
  refine ⟨bs,hlen,hvalid,horder,hlocal,?_⟩
  intro time pub msg
  rw [repaired_digest_count]
  exact native_codec_digest_count bs hlen hvalid horder time pub msg
end ZkFormal.NearV3.Assembly.CodecDigest
