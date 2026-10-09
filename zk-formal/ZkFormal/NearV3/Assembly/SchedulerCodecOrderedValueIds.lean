import ZkFormal.NearV3.Assembly.SchedulerCodecOrderedNative
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 NearSpecV3.Scheduler Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
/-- Main and missing chunks construct one ordered list of actual Codec blocks.
Each timestamp is the real prepared index, and all block premises are derived. -/
theorem native_ordered_blocks_ids {cb : Bytes} {hint : Hint} {p : Prep}
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
      ∀(i : Nat) (b : NativeBlock),(main::tail)[i]?=some b→b.Valid ∧ b.run.n≤64 ∧ b.run.tau=i ∧ b.vid=vids i ∧
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
    exact ⟨hvalid,hn,htau,hvid,hlocal⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hx
    have hi : i<steps.length := by
      have hh := (List.getElem?_eq_some_iff.mp hx).1
      omega
    let e := steps[i]
    have he : steps[i]?=some e := List.getElem?_eq_getElem hi
    have hh := hAt i e x he hx
    exact ⟨hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.1,
      by simpa [Nat.add_comm] using hh.2.2.2.2.2.2.1,
      by simpa [Nat.add_comm] using hh.2.2.2.1,hh.2.2.2.2.2.2.2.2⟩

end ZkFormal.NearV3.Assembly.CodecDigest
