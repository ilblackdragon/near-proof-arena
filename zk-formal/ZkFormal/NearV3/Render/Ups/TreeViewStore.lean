import ZkFormal.NearV3.Render.Ups.TreeViewValues
import ZkFormal.NearV3.Link.Vals3

/-! The actual linked-view store, including modular value-id decoding, reuses the
verified occurrence allocator. Only value-id capacity is needed for that decoding. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render

theorem node_toRec3_congr (node : NodeV3) (f g : Nat → Nat)
    (h : ∀ vid len pre post written,node.value=some (vid,len,pre,post,written) → f vid=g vid) :
    node.toRec3 f=node.toRec3 g := by
  cases node with
  | leaf key slot mem =>
    cases slot with
    | ref => rfl
    | val len vid size pre post written =>
      simp [NodeV3.toRec3,NSlot3.toV3,h vid size pre post written rfl]
  | ext => rfl
  | branch slot kids mem =>
    cases slot with
    | none => rfl
    | some slot =>
      cases slot with
      | ref => rfl
      | val len vid size pre post written =>
        simp [NodeV3.toRec3,NSlot3.toV3,h vid size pre post written rfl]

@[simp] theorem seedValues_vid0 (bytes : List Bytes) : Link3.vid0 (seedValuesFrom 0 bytes)=0 := by
  cases bytes <;> rfl

theorem seedNodesT_modular_records (tau : Nat) (t : PTrie) (hw : t.wf=true)
    (hc : (valsOf t).length≤ZkFormal.Algebra.P) :
    Link3.recsOf (Link3.vpos (Link3.vid0 (seedValuesFrom 0 (valsOf t)))) (seedNodesT tau 0 0 0 t)=
      recsT tau 0 0 t := by
  rw [seedValues_vid0,←seedNodesT_records tau 0 0 0 t hw]
  unfold Link3.recsOf
  apply List.map_congr_left
  intro s hs
  apply congrArg (NodeRec3.mk s.tau)
  apply node_toRec3_congr
  intro vid len pre post written hv
  have hi : vid∈(seedNodesT tau 0 0 0 t).filterMap seedValueId :=
    List.mem_filterMap.mpr ⟨s,hs,by simp [seedValueId,hv]⟩
  rw [seedNodesT_valueIds] at hi
  have hb : vid<ZkFormal.Algebra.P := by simp only [List.mem_range'] at hi; omega
  simp [Link3.vpos,Nat.mod_eq_of_lt hb]

/-- Actual NodeS3 and ValE lists reconstruct the exact original trie through the
same modular value-position mapping used by the assembly interface. -/
theorem seedViews_modular_fullTree (tau : Nat) (t : PTrie) (hw : t.wf=true)
    (hn : isNode t=true) (hc : (valsOf t).length≤ZkFormal.Algebra.P) :
    fullTree
      (Link3.recsOf (Link3.vpos (Link3.vid0 (seedValuesFrom 0 (valsOf t)))) (seedNodesT tau 0 0 0 t))
      (Link3.valsOf3 (seedNodesT tau 0 0 0 t) (seedValuesFrom 0 (valsOf t))) 0=t := by
  rw [seedNodesT_modular_records tau t hw hc,seedValuesT_records]
  rw [←seedNodesT_records tau 0 0 0 t hw]
  exact seedNodesT_fullTree tau t hw hn

theorem seedViews_modular_store (tau : Nat) (t : PTrie) (hw : t.wf=true)
    (hn : isNode t=true) (hc : (valsOf t).length≤ZkFormal.Algebra.P) :
    storeOf
      (Link3.recsOf (Link3.vpos (Link3.vid0 (seedValuesFrom 0 (valsOf t)))) (seedNodesT tau 0 0 0 t))
      (Link3.valsOf3 (seedNodesT tau 0 0 0 t) (seedValuesFrom 0 (valsOf t))) tau=
        (occs t).map nodeEnc++valsOf t := by
  rw [seedNodesT_modular_records tau t hw hc,seedValuesT_records]
  exact storeOf_T hn

end ZkFormal.NearV3.Render.UpsGen
