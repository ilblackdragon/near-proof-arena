import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayTargets

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

def providerSlot (s : NSlot3) : NSlot3 := match s with
  | .ref _ _=>.ref [] []
  | .val _ i _ _ _ _=>.val [] i 0 [] [] false

def providerNode : NodeV3→NodeV3
  | .leaf k v _=>.leaf k (providerSlot v) []
  | .ext k c _=>.ext k (providerKid c) []
  | .branch v cs _=>.branch (v.map providerSlot) (cs.map providerKid) []

theorem write_providerSlot (v : Nat) {a b : Slot} (h : WriteSlotPair a b) :
    providerSlot (viewSlot v a)=providerSlot (viewSlot v b) := by
  cases h <;> rfl

theorem write_providerNode (n v : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    providerNode (viewNode n v a)=providerNode (viewNode n v b) := by
  cases h with
  | hash=>rfl
  | leaf k m h=>simp only [viewNode,providerNode,write_providerSlot v h]
  | ext k m h=>simp only [viewNode,providerNode,write_providerKid (n+1) h]
  | branch m h hs=>
    cases h with
    | none=>simp only [viewNode,providerNode,Option.map_none,write_providerKids (n+1) hs]
    | some h=>simp only [viewNode,providerNode,Option.map_some,write_providerSlot v h,write_providerKids (n+1) hs]

theorem providerNode_edges (s : NodeS3) (n : Nat) :
    edgesOf3 n {s with v:=providerNode s.v}=edgesOf3 n s := by
  cases hv:s.v with
  | leaf k v m=>cases v <;> simp [edgesOf3,hv,providerNode,providerSlot]
  | ext k c m=>cases c <;> cases hk:k.getLast? <;> simp [edgesOf3,hv,providerNode,providerKid,hk]
  | branch v cs m=>
    have hfn : (fun x : NKid×Nat => match (providerKid x.1,x.2) with
        | (.node _ _ cr _ _,j)=>some [n,0,j,cr,0,EK_DOWN]
        | _=>none)=
        (fun x : NKid×Nat => match x with
        | (.node _ _ cr _ _,j)=>some [n,0,j,cr,0,EK_DOWN]
        | _=>none) := by
      funext x
      obtain ⟨c,j⟩:=x
      cases c <;> rfl
    cases v with
    | none=>
      simp only [edgesOf3,hv,providerNode,Option.map_none,List.length_map,List.append_nil,
        List.zip_map_left,List.filterMap_map]
      congr 1
    | some v=>
      cases v <;> simp only [edgesOf3,hv,providerNode,Option.map_some,providerSlot,List.length_map,
        List.zip_map_left,List.filterMap_map,List.append_nil]
      all_goals first | (congr 1; funext x; obtain ⟨c,j⟩:=x; cases c <;> rfl) | skip
      all_goals (congr 2 <;> (funext x; obtain ⟨c,j⟩:=x; cases c <;> rfl))
    all_goals funext x; obtain ⟨c,j⟩:=x; cases c <;> rfl

theorem providerKid_present (c : NKid) : (providerKid c).present=c.present := by
  cases c <;> rfl

theorem providerKids_bitmap (cs : List NKid) : kidBitmap (cs.map providerKid)=kidBitmap cs := by
  simp only [kidBitmap,List.length_map,List.zip_map_left,List.map_map]
  congr 2
  funext x
  obtain ⟨c,j⟩:=x
  change (if (providerKid c).present then 2^j else 0)=(if c.present then 2^j else 0)
  rw [providerKid_present]

theorem providerNode_bmap (v : NodeV3) : (providerNode v).bmap=v.bmap := by
  cases v with
  | leaf=>rfl
  | ext=>rfl
  | branch v cs m=>simp [providerNode,NodeV3.bmap,providerKids_bitmap]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
