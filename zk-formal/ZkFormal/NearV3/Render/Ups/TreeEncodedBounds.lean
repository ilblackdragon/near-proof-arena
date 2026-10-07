import ZkFormal.NearV3.Render.Ups.TreeSplitMemoryInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem node_hplen_le_serialized (node : NodeV3) (post : Bool) :
    NodeGen3.hplenOf node≤(node.ser post).length := by
  cases node <;>
    simp [NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,NodeV3.ser,hpN,
      Render.NodeInfo.hexPrefix_len] <;> omega

/-- Header capacity follows from ordinary serialized byte lengths. -/
theorem encoded_header_bounds {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) : Q.qhk≤Q.q.length ∧ Q.phk≤Q.pb.length := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at he
  subst Q
  exact ⟨node_hplen_le_serialized _ false,node_hplen_le_serialized _ true⟩

/-- Encoding retains the allocator's native child-memory scalar. -/
theorem encodeTreePart_mB {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) : Q.mB=base.mB := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at he
  subst Q; rfl

/-- Fill split memory metadata from the actual source/output trees, then encode their bytes. -/
def encodeSplitPart (base : UpsPartI) (matched : Nat) (part : TreePart) : Option UpsPartI :=
  encodeTreePart {base with mB:=splitChildMemory matched part} part

theorem encodeSplitPart_memory {base Q : UpsPartI} {matched : Nat} {part : TreePart}
    (he : encodeSplitPart base matched part=some Q) : Q.mB=splitChildMemory matched part :=
  encodeTreePart_mB he

/-- The executable split encoder removes the child-memory assignment premise. Physical
row capacity and the surrounding source-byte table are separate allocator obligations. -/
theorem encode_leafSplit_byteMemory (k : List Nat) (old : Slot) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.leaf k old mem).wf=true) (hk : FixedSuffix key)
    (hne : k≠key) (hL : v.length<2^24) (baseI : UpsInst)
    (part : TreePart) (hpart : part∈(leafSplitRun k old mem key v).parts)
    (base Q : UpsPartI) (he : encodeSplitPart base (commonPrefix k key).length part=some Q)
    (hq : Q.q.length<2^22) (hp : Q.pb.length<2^22)
    (hchild : ∀ b∈(child (traceInstance baseI (leafSplitRun k old mem key v) v) Q).pb,b<256) :
    Nonempty (ByteMemoryInput (traceInstance baseI (leafSplitRun k old mem key v) v)
      (withMemorySign (traceInstance baseI (leafSplitRun k old mem key v) v) Q)) := by
  have hb := encoded_header_bounds he
  exact leafSplitRun_byteMemory k old mem key v hw hk hne hL baseI part hpart _ Q he
    (encodeSplitPart_memory he) (by omega) (by omega) hchild

theorem encode_extSplit_byteMemory (k : List Nat) (oldChild : PTrie) (mem : Nat) (key : List Nat)
    (v : Bytes) (hw : (PTrie.ext k oldChild mem).wf=true) (hk : FixedSuffix key)
    (hprefix : isPrefix k key=false) (hL : v.length<2^24) (baseI : UpsInst)
    (part : TreePart) (hpart : part∈(extSplitRun k oldChild mem key v).parts)
    (base Q : UpsPartI) (he : encodeSplitPart base (commonPrefix k key).length part=some Q)
    (hq : Q.q.length<2^22) (hp : Q.pb.length<2^22)
    (hchild : ∀ b∈(child (traceInstance baseI (extSplitRun k oldChild mem key v) v) Q).pb,b<256) :
    Nonempty (ByteMemoryInput (traceInstance baseI (extSplitRun k oldChild mem key v) v)
      (withMemorySign (traceInstance baseI (extSplitRun k oldChild mem key v) v) Q)) := by
  have hb := encoded_header_bounds he
  exact extSplitRun_byteMemory k oldChild mem key v hw hk hprefix hL baseI part hpart _ Q he
    (encodeSplitPart_memory he) (by omega) (by omega) hchild
end ZkFormal.NearV3.Render.UpsGen
