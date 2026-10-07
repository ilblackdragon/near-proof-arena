import ZkFormal.NearV3.Render.Ups.TreeViewSeeds

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

@[simp] theorem viewKid_present (nid : Nat) (child : PTrie) : (viewKid nid child).present=true := by
  unfold viewKid; split <;> rfl

@[simp] theorem viewKids_bytes : ∀ nid kids post,
    (viewKids nid kids).flatMap (NKid.bytes post)=(Kids.hashes kids).map UInt8.toNat
  | _,.nil,_ => rfl
  | n,.none rest,post => by simpa [viewKids,NKid.bytes,Kids.hashes] using viewKids_bytes n rest post
  | n,.some child rest,post => by
    simp [viewKids,Kids.hashes,viewKids_bytes (n+tsize child) rest post]

@[simp] theorem viewKids_bitmap : ∀ nid kids, kidBitmap (viewKids nid kids)=kidsBitmap kids 0
  | _,.nil => rfl
  | n,.none rest => by
    simp [viewKids,kidBitmap_cons,NKid.present,kidsBitmap,runtime_bitmap_shift rest 1,viewKids_bitmap n rest]
  | n,.some child rest => by
    simp [viewKids,kidBitmap_cons,kidsBitmap,runtime_bitmap_shift rest 1,viewKids_bitmap (n+tsize child) rest]

/-- Revealing child/value IDs does not change the actual runtime serialized bytes. -/
theorem viewNode_ser (nid vid : Nat) (t : PTrie) (hw : t.wf=true) (hh : SmallNodeHeader t)
    (hn : isNode t=true) (post : Bool) : (viewNode nid vid t).ser post=(nodeEnc t).map UInt8.toNat := by
  cases t with
  | hash => simp [isNode] at hn
  | leaf key value mem => simp [viewNode,NodeV3.ser,nodeEnc,map_u32_small _ hh,hpN]
  | ext key child mem => simp [viewNode,NodeV3.ser,nodeEnc,map_u32_small _ hh,hpN]
  | branch value kids mem =>
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hl := (treeKids_wf kids 16 hw.1.2).1
    have hb := Link.kidBitmap_lt hl
    rw [treeKids_bitmap] at hb
    cases value <;> simp [viewNode,NodeV3.ser,nodeEnc,map_u16_small _ hb]

/-- The seeded actual views unfold to precisely the original revealed runtime tree. -/
theorem seedNodesT_fullTree (tau : Nat) (t : PTrie) (hw : t.wf=true) (hn : isNode t=true) :
    fullTree (Link3.recsOf id (seedNodesT tau 0 0 0 t)) (valsT tau t) 0=t := by
  rw [seedNodesT_records tau 0 0 0 t hw]
  apply fullTree_at
  cases t <;> simp_all [isNode,occs]

/-- The view record store is exactly the already-verified occurrence store. -/
theorem seedNodesT_store (tau : Nat) (t : PTrie) (hw : t.wf=true) (hn : isNode t=true) :
    storeOf (Link3.recsOf id (seedNodesT tau 0 0 0 t)) (valsT tau t) tau=
      (occs t).map nodeEnc++valsOf t := by
  rw [seedNodesT_records tau 0 0 0 t hw]
  exact storeOf_T hn

end ZkFormal.NearV3.Render.UpsGen
