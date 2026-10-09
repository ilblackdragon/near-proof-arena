import ZkFormal.NearV3.Rcpt.Candidates.NativeChildPayload

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- Compact value payloads in the same original allocation. -/
def ValuePayloads (u : Inputs) (v : Nat) (as bs : List Bytes) : Prop :=
  ∀i a b,as[i]?=some a→bs[i]?=some b→ValuePayload u (v+i) a b

/-- A whole updated old-node encoding uses actual post subtree/value bytes.
Both written and unwritten value slots are covered by the same statement. -/
theorem node_payload_post (u : Inputs) (n v : Nat) {a b : PTrie}
    (hp : WriteTreePair a b) (hw : b.wf=true) (hn : isNode b=true)
    (hc : ChildPayloads u n (occs b))
    (hv : ValuePayloads u v (valsOf a) (valsOf b)) :
    (node u (viewNode n v a)).ser true=(nodeEnc b).map UInt8.toNat := by
  rw [←viewNode_ser n v b hw hn false]
  cases hp with
  | hash h=>simp [isNode] at hn
  | leaf k m hs=>
    cases hs with
    | ref l hh=>simp [node,viewNode,slot,viewSlot,NodeV3.ser,NSlot3.bytes]
    | val before after=>
      have hh:=hv 0 before after rfl rfl
      simp only [Nat.add_zero] at hh
      simp only [node,viewNode,NodeV3.ser,slot_payload_post u v before after hh,viewSlot_bytes]
  | ext k m hp=>
    have hh:=kid_payload_post u (n+1) hp hc.tail
    simp only [node,viewNode,NodeV3.ser,hh,viewKid_bytes]
  | branch m hvp hkids=>
    have hh:=kids_payload_post u (n+1) hkids hc.tail
    cases hvp with
    | none=>
      simp [node,viewNode,NodeV3.ser,bitmap,hh,viewKids_bitmap,viewKids_bytes,native_pair_bitmap hkids]
    | some hs=>
      cases hs with
      | ref l h=>simp [node,viewNode,slot,viewSlot,NodeV3.ser,NSlot3.bytes,bitmap,hh,viewKids_bitmap,viewKids_bytes,native_pair_bitmap hkids]
      | val before after=>
        have hv0:=hv 0 before after rfl rfl
        simp only [Nat.add_zero] at hv0
        simp [node,viewNode,NodeV3.ser,slot_payload_post u v before after hv0,
          viewSlot_bytes,bitmap,hh,viewKids_bitmap,viewKids_bytes,native_pair_bitmap hkids]

/-- The actual replay arrays directly instantiate every payload premise for
the root old-node record. Global-offset transport supplies descendant records. -/
theorem oldTreeInputs_root_bytes {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (hr : SizedAccountRun pre writes oldPost) (hw : oldPost.wf=true) (hn : isNode oldPost=true) :
    (node (oldTreeInputs pre oldPost writes) (viewNode 0 0 pre)).ser true=
      (nodeEnc oldPost).map UInt8.toNat := by
  apply node_payload_post _ 0 0 hr.forget.skeleton hw hn
  · intro i t hi
    simpa using oldTreeInputs_child hi
  · intro i a b ha hb
    simpa using oldTreeInputs_payload hr ha hb

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
