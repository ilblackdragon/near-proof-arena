import ZkFormal.NearV3.Render.Ups.TreeSplitMemoryBound
import ZkFormal.NearV3.Render.Ups.TreeValueMemoryDispatch

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Byte and memory completeness for an actual native leaf split part. The allocator
supplies the ordinary child-memory field and its surrounding byte/header bounds. -/
theorem leafSplitRun_byteMemory (k : List Nat) (old : Slot) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.leaf k old mem).wf=true) (hk : FixedSuffix key)
    (hne : k≠key) (hL : v.length<2^24) (baseI : UpsInst)
    (part : TreePart) (hpart : part∈(leafSplitRun k old mem key v).parts)
    (base Q : UpsPartI) (he : encodeTreePart base part=some Q)
    (hm : Q.mB=splitChildMemory (commonPrefix k key).length part)
    (hq : Q.qhk<2^22) (hp : Q.phk<2^22)
    (hchild : ∀ b∈(UpsGen.child (traceInstance baseI (leafSplitRun k old mem key v) v) Q).pb,b<256) :
    Nonempty (ByteMemoryInput (traceInstance baseI (leafSplitRun k old mem key v) v)
      (withMemorySign (traceInstance baseI (leafSplitRun k old mem key v) v) Q)) := by
  obtain ⟨data⟩ := leafSplitRun_byteInput k old mem key v hw hk hne baseI part hpart base Q he
  refine ⟨⟨data.withMemorySign,data.native_memOk he ?_ hq hp ?_ hchild ?_ ?_⟩⟩
  · change (leafSplitRun k old mem key v).terminal.ix<11
    cases (leafSplitRun k old mem key v).terminal <;> decide
  · simpa [L,traceInstance] using hL
  · rw [hm]
    exact leafSplitRun_childMemory_bound k key old mem v hw hk.length hL part hpart
  · exact leafSplitRun_memory k old mem key v hw hk hne hL baseI part hpart base Q he hm

/-- All four native extension split cases, with full-width source headers and modular
serialization of possibly overflowing native memory totals. -/
theorem extSplitRun_byteMemory (k : List Nat) (oldChild : PTrie) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.ext k oldChild mem).wf=true) (hk : FixedSuffix key)
    (hprefix : isPrefix k key=false) (hL : v.length<2^24) (baseI : UpsInst)
    (part : TreePart) (hpart : part∈(extSplitRun k oldChild mem key v).parts)
    (base Q : UpsPartI) (he : encodeTreePart base part=some Q)
    (hm : Q.mB=splitChildMemory (commonPrefix k key).length part)
    (hq : Q.qhk<2^22) (hp : Q.phk<2^22)
    (hchild : ∀ b∈(child (traceInstance baseI (extSplitRun k oldChild mem key v) v) Q).pb,b<256) :
    Nonempty (ByteMemoryInput (traceInstance baseI (extSplitRun k oldChild mem key v) v)
      (withMemorySign (traceInstance baseI (extSplitRun k oldChild mem key v) v) Q)) := by
  obtain ⟨data⟩ := extSplitRun_byteInput k oldChild mem key v hw hk hprefix baseI part hpart base Q he
  refine ⟨⟨data.withMemorySign,data.native_memOk he ?_ hq hp ?_ hchild ?_ ?_⟩⟩
  · change (extSplitRun k oldChild mem key v).terminal.ix<11
    cases (extSplitRun k oldChild mem key v).terminal <;> decide
  · simpa [L,traceInstance] using hL
  · rw [hm]
    exact extSplitRun_childMemory_bound k key oldChild mem v hw hk.length hL part hpart
  · exact extSplitRun_memory k oldChild mem key v hw hk hprefix hL baseI part hpart base Q he hm
end ZkFormal.NearV3.Render.UpsGen
