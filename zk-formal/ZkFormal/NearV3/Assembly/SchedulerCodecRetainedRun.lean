import ZkFormal.NearV3.Assembly.SchedulerCodecAllocatedIds
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 NearSpecV3.Scheduler Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Retain the native prepared index and the same process execution used to
construct the block, instead of forgetting them after local legality. -/
def PreparedRun (p : Prep) (tau : Nat) (b : NativeBlock) : Prop :=
  p.sched[tau]?=some b.pub ∧
  ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau=.ok b.run

theorem implicit_blocks_run {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {root : Bytes}
    {pairs : List (Blk×Transition)} {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k root pairs steps last) (tau : Nat) (ht : 0<tau)
    (vids : Nat→Nat)
    (hi : ∀i e,steps[i]?=some e→∃sp,p.sched[tau+i]?=some sp ∧ schedPub (implicitContext k e)=some sp) :
    ∃bs : List NativeBlock,bs.length=steps.length ∧
      ∀i e b,steps[i]?=some e→bs[i]?=some b→MissingBlockAt k vids (tau+i) e b ∧ PreparedRun p (tau+i) b := by
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
      exact ⟨⟨hb,hpre,hctx,hvid,hf,hvalid,htau,hn,hlocal⟩,by
        simpa only [Nat.add_zero] using (show PreparedRun p tau b from ⟨by rw [hsp];exact hindex,hr⟩)⟩
    | succ i =>
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hbs i x y hx hy

end ZkFormal.NearV3.Assembly.CodecDigest
