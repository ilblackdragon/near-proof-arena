import ZkFormal.NearV3.Assembly.NativeCapacity
import ZkFormal.NearV3.Assembly.ImplicitTraceReplay

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem implicit_run_root_length {ctx : ApplyCtx} {ws : List Bytes} {root : Bytes} {post : PTrie}
    (h : applyMissingChunk prims ctx (partialTrie ws root [keyDelayedIdx,keyBwState]) = .ok post) :
    root.length = 32 := by
  obtain ⟨v, hv⟩ := Qv.applyMissingChunk_delayed_read h
  have hd : (partialTrie ws root [keyDelayedIdx,keyBwState]).find keyDelayedIdx ≠ none := by
    rw [hv]; simp
  have hh := find_determinate_root_length _ keyDelayedIdx hd
  change (buildFor (mkStore ws) trieFuel root [keyDelayedIdx,keyBwState]).hashOf.length = 32 at hh
  rwa [built_hashOf_all] at hh

theorem ImplicitTraceValid.input_facts {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) : ∀ e ∈ steps,
    e.pre = partialTrie e.witness.values e.root [keyDelayedIdx,keyBwState] ∧
      e.root.length = 32 ∧ e.pre.wf = true := by
  induction h with
  | nil => intro e he; simp at he
  | cons root b t rest steps post last hrun hpost htail ih =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · have hr := implicit_run_root_length hrun
      exact ⟨rfl, hr, (built_spec t.values trieFuel root [keyDelayedIdx,keyBwState] hr).2.1⟩
    · exact ih e he

theorem checkD0a_native_trace {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ()) :
    ∃ m : MainExecutionV3, ∃ steps : List ImplicitStepV3, ∃ last : Bytes,
      m.NativeValid k w ∧
      traceImplicit k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) = .ok (steps,last) ∧
      ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      steps.length = k.implicitBlks.length ∧ steps.length ≤ 31 ∧
      (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P ∧
      (∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true) := by
  have hrel := (relD0a_iff B cb wb).mpr h
  have hgas : k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1, hk, decide_eq_true_eq] using hrel.2.1
  unfold checkD0a at h
  obtain ⟨u, hu, _⟩ := ReexecV3D0.bind_ok' h
  cases u
  obtain ⟨m,last,hm,hl,hcount,hbound⟩ := checkD0_native_steps hk hw hu
  obtain ⟨steps,ht,hv⟩ := checkedImplicitLoop_trace k _ _ _ hl
  have hlen : steps.length = k.implicitBlks.length := by
    rw [hv.length, List.length_zip, hcount, Nat.min_self]
  have hcap := nativeForest_inputs_capacity_from_run hm hgas (steps.map ImplicitStepV3.input)
    (by simp only [List.length_map]; omega)
  have htrees : implicitTrees (steps.map ImplicitStepV3.input) = steps.map ImplicitStepV3.pre := by
    simp only [implicitTrees, List.map_map, ImplicitStepV3.input, Function.comp_def]
    exact hv.pre_trees.symm
  rw [htrees] at hcap
  refine ⟨m,steps,last,hm,ht,hv,hlen,by omega,hcap,?_⟩
  intro t ht
  simp only [List.mem_cons, List.mem_map] at ht
  rcases ht with rfl | ⟨e,he,rfl⟩
  · rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  · exact (hv.input_facts e he).2.2

end ZkFormal.NearV3.Assembly
