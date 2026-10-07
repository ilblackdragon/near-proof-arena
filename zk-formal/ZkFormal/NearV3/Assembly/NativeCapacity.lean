import ZkFormal.NearV3.Assembly.NativeMain
import ZkFormal.NearV3.Assembly.StoreValueBounds
import ZkFormal.NearV3.Assembly.Compute

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem find_determinate_root_length (t : PTrie) (key : List Nat)
    (h : t.find key ≠ none) : t.hashOf.length = 32 := by
  cases t with
  | hash => exact False.elim (h rfl)
  | leaf => simp [PTrie.hashOf, sha256, ArenaCore.sha256_length]
  | ext => simp [PTrie.hashOf, sha256, ArenaCore.sha256_length]
  | branch v cs m => cases v <;> simp [PTrie.hashOf, sha256, ArenaCore.sha256_length]

theorem MainExecutionV3.NativeValid.root_length {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (h : m.NativeValid k w) : k.slotB2.prevStateRoot.length = 32 := by
  obtain ⟨_, _, v, _, _, hv⟩ := Qv.applyNewChunk_queue_reads h.run
  have hd : m.pre.find keyDelayedIdx ≠ none := by rw [hv.1]; simp
  have hh := find_determinate_root_length m.pre keyDelayedIdx hd
  rwa [h.preRoot] at hh

/-- The native 3MB main-store guard bounds the actual parsed buffered shard list. -/
theorem MainExecutionV3.NativeValid.buffered_count {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (h : m.NativeValid k w) (hr : k.slotB2.prevStateRoot.length = 32) :
    m.bufferedShards.length ≤ 125000 := by
  obtain ⟨v, hf, hp⟩ := h.buffered
  have hb : (w.main.values.map List.length).sum ≤ 3000000 := by
    simpa only [foldl_add_sum, Nat.zero_add] using h.storeBytes
  exact bufferedShards_store_bound hr hf hp hb

/-- Main value-ID capacity comes from native gas and authenticated byte budgets. -/
theorem MainExecutionV3.NativeValid.value_count {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (h : m.NativeValid k w) (hr : k.slotB2.prevStateRoot.length = 32)
    (hg : k.slotB2.gasLimit ≤ maxGasLimitD0) : (valsOf m.pre).length ≤ 133966 := by
  have hb := h.buffered_count hr
  have hgas : (m.ctx k).gasLimit ≤ maxGasLimitD0 := hg
  have hrs := applyNewChunk_receipt_bound h.run hgas
  have hv := partialTrie_value_count w.main.values k.slotB2.prevStateRoot
    (mainKeys (appliedReceipts k w) m.bufferedShards)
  have hf := List.length_filter_le
    (fun r : Receipt => r.predecessorId == AccountId.system && r.signerId == r.receiverId)
    (appliedReceipts k w)
  rw [h.pre]
  simp only [mainKeys, List.length_append, List.length_map, List.length_cons, List.length_nil] at hv ⊢
  omega

private theorem forestBytes_count (ts : List PTrie) (bound : Nat)
    (h : ∀ t ∈ ts, (valsOf t).length ≤ bound) :
    (forestBytes ts).length ≤ bound * ts.length := by
  induction ts with
  | nil => simp [forestBytes]
  | cons t ts ih =>
    have hh := h t (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [forestBytes, List.flatMap_cons, List.length_append] at *
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- All native transition value IDs fit the active AIR field; no Goldilocks assumption. -/
theorem nativeForest_capacity {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (h : m.NativeValid k w) (hr : k.slotB2.prevStateRoot.length = 32)
    (hg : k.slotB2.gasLimit ≤ maxGasLimitD0) (implicit : List PTrie)
    (hc : implicit.length ≤ 31) (hi : ∀ t ∈ implicit, (valsOf t).length ≤ 2) :
    (forestBytes (m.pre :: implicit)).length ≤ ZkFormal.Algebra.P := by
  have hm := h.value_count hr hg
  have ht := forestBytes_count implicit 2 hi
  simp only [forestBytes, List.flatMap_cons, List.length_append] at *
  unfold ZkFormal.Algebra.P
  omega

/-- Actual implicit builder inputs, in chronological order. -/
def implicitTrees (inputs : List (List Bytes × Bytes)) : List PTrie :=
  inputs.map (fun (ws, root) => partialTrie ws root [keyDelayedIdx, keyBwState])

theorem nativeForest_inputs_capacity {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (h : m.NativeValid k w) (hr : k.slotB2.prevStateRoot.length = 32)
    (hg : k.slotB2.gasLimit ≤ maxGasLimitD0) (inputs : List (List Bytes × Bytes))
    (hc : inputs.length ≤ 31) :
    (forestBytes (m.pre :: implicitTrees inputs)).length ≤ ZkFormal.Algebra.P := by
  apply nativeForest_capacity h hr hg (implicitTrees inputs)
  · simpa [implicitTrees] using hc
  · intro t ht
    obtain ⟨⟨ws, root⟩, _, rfl⟩ := List.mem_map.mp ht
    exact partialTrie_value_count ws root [keyDelayedIdx, keyBwState]

theorem nativeForest_inputs_capacity_from_run {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (h : m.NativeValid k w)
    (hg : k.slotB2.gasLimit ≤ maxGasLimitD0) (inputs : List (List Bytes × Bytes))
    (hc : inputs.length ≤ 31) :
    (forestBytes (m.pre :: implicitTrees inputs)).length ≤ ZkFormal.Algebra.P :=
  nativeForest_inputs_capacity h h.root_length hg inputs hc

end ZkFormal.NearV3.Assembly
