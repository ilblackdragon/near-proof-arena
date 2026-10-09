import ZkFormal.NearV3.Rcpt.Candidates.NodePostWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near NearSpec Render.UpsGen

/-- A same-length native value replacement changes exactly the post digest
window, preserving the original value ID and length encoding. -/
theorem native_slot_post (u : Inputs) (vid : Nat) (pre post : Bytes)
    (hu : u.value vid=some post) (hl : post.length=pre.length) :
    (slot u (viewSlot vid (.val pre))).bytes true=(Slot.val post).valueRef.map UInt8.toNat := by
  simp [slot,viewSlot,hu,NSlot3.bytes,Slot.valueRef,digest,hl,List.map_append]

theorem native_leaf_post (u : Inputs) (nid vid : Nat) (key : List Nat) (mem : Nat)
    (pre post : Bytes) (hu : u.value vid=some post) (hl : post.length=pre.length) :
    (node u (viewNode nid vid (.leaf key (.val pre) mem))).ser true=
      (nodeEnc (.leaf key (.val post) mem)).map UInt8.toNat := by
  simp only [viewNode,node,NodeV3.ser,native_slot_post u vid pre post hu hl]
  simp [nodeEnc,u32Bytes,hpN,List.map_append]

/-- Directly linked to successful native `PTrie.set`, not a synthetically
chosen post leaf. The length equality is the account-write invariant. -/
theorem native_leaf_set_post (u : Inputs) (nid vid : Nat) (key query : List Nat) (mem : Nat)
    (pre post : Bytes) (t' : PTrie)
    (hs : (PTrie.leaf key (.val pre) mem).set query post=some t')
    (hu : u.value vid=some post) (hl : post.length=pre.length) :
    (node u (viewNode nid vid (.leaf key (.val pre) mem))).ser true=
      (nodeEnc t').map UInt8.toNat := by
  simp only [PTrie.set] at hs
  split at hs
  · simp only [Slot.get,Option.map_some,Option.some.injEq] at hs
    subst t'
    exact native_leaf_post u nid vid key mem pre post hu hl
  · cases hs

/-- The implemented window update discharges final-view length/WF obligations
from the corresponding initial allocated view facts. -/
theorem updated_rows (u : Inputs) (ss : List NodeS3) (vs : List ValE) (h : NodeWf3 ss) :
    nodeValueShaRows (records u ss) vs=nodeValueShaRows ss vs := by
  unfold nodeValueShaRows
  rw [node_pair_rows _ (records_wf u ss h),node_pair_rows _ h,records_pre_lengths]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
