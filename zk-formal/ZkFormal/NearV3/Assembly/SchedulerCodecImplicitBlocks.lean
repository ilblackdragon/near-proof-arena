import ZkFormal.NearV3.Assembly.SchedulerCodecMissingBlock
import ZkFormal.NearV3.Assembly.SchedulerPreparedContexts
import ZkFormal.NearV3.Assembly.ImplicitTraceReplay
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 NearSpecV3.Scheduler Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def implicitContext (k : WalkD0) (e : ImplicitStepV3) : ApplyCtx :=
  blockCtx k.L k.H.shardId k.slotB2.gasLimit e.block e.block.hdr.nextGasPrice

def MissingBlockAt (k : WalkD0) (vids : Nat→Nat) (tau : Nat)
    (e : ImplicitStepV3) (b : NativeBlock) : Prop :=
  schedulerUpsertWitness (implicitContext k e) e.pre=.ok b.witness ∧
  b.witness.pre=e.pre ∧ b.witness.ctx=implicitContext k e ∧ b.vid=vids tau ∧
  b.forwarded=[] ∧ b.Valid ∧ b.run.tau=tau ∧ b.run.n≤64 ∧
  ∀time pub,TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) time pub

/-- Construct every missing block in trace order. The indexed public lookup
is an ordinary prepared/native context correspondence, not an AIR premise. -/
theorem implicit_blocks {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {root : Bytes}
    {pairs : List (Blk×Transition)} {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k root pairs steps last) (tau : Nat) (ht : 0<tau)
    (vids : Nat→Nat)
    (hi : ∀i e,steps[i]?=some e→∃sp,p.sched[tau+i]?=some sp ∧ schedPub (implicitContext k e)=some sp) :
    ∃bs : List NativeBlock,bs.length=steps.length ∧
      ∀i e b,steps[i]?=some e→bs[i]?=some b→MissingBlockAt k vids (tau+i) e b := by
  induction hv generalizing tau with
  | nil => exact ⟨[],rfl,by intro i e b he; simp at he⟩
  | cons root block witness rest steps post last hrun hpost htail ih =>
    let e : ImplicitStepV3 := ⟨block,witness,root,partialTrie witness.values root [keyDelayedIdx,keyBwState],post⟩
    obtain ⟨sp,hindex,hpub⟩ := hi 0 e rfl
    simp only [Nat.add_zero] at hindex
    obtain ⟨b,hb,hpre,hctx,hsp,hvid,hf,hvalid,hr,htau,hn,hlocal⟩ :=
      native_missing_block hp sp tau hindex (by omega) (implicitContext k e) hpub e.pre post hrun (vids tau)
    obtain ⟨bs,hlen,hbs⟩ := ih (tau+1) (by omega) (by
      intro i x hx
      obtain ⟨sp,hs,hc⟩ := hi (i+1) x hx
      exact ⟨sp,by simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hs,hc⟩)
    refine ⟨b::bs,by simp [hlen],?_⟩
    intro i x y hx hy
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hx hy
      subst x; subst y
      exact ⟨hb,hpre,hctx,hvid,hf,hvalid,htau,hn,hlocal⟩
    | succ i =>
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hbs i x y hx hy

/-- Native trace order and successful preparation determine every implicit
scheduler public instance at its actual successor index. -/
theorem implicit_prepared_index {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length=k.implicitBlks.length) (i : Nat) (e : ImplicitStepV3)
    (he : steps[i]?=some e) :
    ∃sp,p.sched[1+i]?=some sp ∧ schedPub (implicitContext k e)=some sp := by
  have hc : k.implicitBlks.length≤w.implicit.length := by
    have hh := hv.length
    simp only [List.length_zip,hlen] at hh
    omega
  have hb := congrArg (List.map Prod.fst) hv.pairs
  rw [List.map_fst_zip hc] at hb
  simp only [List.map_map,Function.comp_def] at hb
  have hi : k.implicitBlks[i]?=some e.block := by
    rw [←hb,List.getElem?_map,he]
    rfl
  apply prepD0_context_index hp hw hm (1+i) (implicitContext k e)
  simp only [schedulerContexts,Nat.add_comm 1 i,List.getElem?_cons_succ,List.getElem?_map,hi,Option.map_some]
  rfl

theorem native_implicit_blocks {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length=k.implicitBlks.length) (vids : Nat→Nat) :
    ∃bs : List NativeBlock,bs.length=steps.length ∧
      ∀i e b,steps[i]?=some e→bs[i]?=some b→MissingBlockAt k vids (1+i) e b :=
  implicit_blocks hp hv 1 (by decide) vids (implicit_prepared_index hp hw hm hv hlen)
end ZkFormal.NearV3.Assembly.CodecDigest
