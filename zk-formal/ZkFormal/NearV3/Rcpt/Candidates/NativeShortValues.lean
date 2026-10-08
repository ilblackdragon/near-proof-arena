import ZkFormal.NearV3.Rcpt.Candidates.NativeOccurrenceSha

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly Render.UpsGen

@[simp] theorem seedValues_count : ∀ vid bs, (seedValuesFrom vid bs).length=bs.length
  | _,[] => rfl
  | vid,_::bs => by simp [seedValuesFrom,seedValues_count (vid+1) bs]

private theorem forestValues_count (ts : List PTrie) (n : Nat)
    (h : ∀t∈ts,(valsOf t).length≤n) : (forestBytes ts).length≤n*ts.length := by
  induction ts with
  | nil => simp [forestBytes]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hh := ih (fun t ht => h t (by simp [ht]))
    simp only [forestBytes,List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one] at *
    omega

/-- All allocated values, not just nonduplicate representatives, satisfy this
native count bound. Every implicit prestate has at most its two queried values. -/
theorem native_forest_value_count {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hg : k.slotB2.gasLimit≤maxGasLimitD0) (hs : steps.length≤31) :
    (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).values.length≤134028 := by
  have hmain := hm.value_count hm.root_length hg
  have hi : ∀t∈steps.map ImplicitStepV3.pre,(valsOf t).length≤2 := by
    intro t ht
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
    rw [(hv.input_facts e he).1]
    exact partialTrie_value_count _ _ [keyDelayedIdx,keyBwState]
  have hh := forestValues_count _ 2 hi
  simp only [forestStoreViews,seedValues_count,forestBytes,List.flatMap_cons,
    List.length_append,List.length_map] at *
  omega

/-- The accepted checker supplies both count premises; no new acceptance guard. -/
theorem accepted_short_values {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B cb wb=.ok ()) :
    ∃m : MainExecutionV3, ∃steps : List ImplicitStepV3, ∃last : Bytes,
      m.NativeValid k w ∧
      ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      let vs := (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).values
      vs.length≤134028 ∧ shortCount (vs.map (fun v => v.bytes.length))≤134028 := by
  obtain ⟨m,steps,last,hm,_,hv,_,hs,_,_⟩ := checkD0a_native_trace hk hw hc
  have hrel := (relD0a_iff B cb wb).mpr hc
  have hg : k.slotB2.gasLimit≤maxGasLimitD0 := by
    simpa only [a1,hk,decide_eq_true_eq] using hrel.2.1
  have hn := native_forest_value_count hm hv hg hs
  refine ⟨m,steps,last,hm,hv,hn,?_⟩
  have hf := List.length_filter_le (fun n : Nat => decide (n<43))
    ((forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).values.map (fun v => v.bytes.length))
  simp only [List.length_map] at hf
  unfold shortCount
  omega

end ZkFormal.NearV3.Rcpt.Candidates
