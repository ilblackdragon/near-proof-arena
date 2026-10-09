import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteSkeleton
import ZkFormal.NearV3.Rcpt.Candidates.NodePostChildren

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

def pairedSlot (vid : Nat) : Slot→Slot→NSlot3
  | .val a,.val b => .val ((u32 a.length).map UInt8.toNat) vid a.length
      (digest a) (digest b) (decide (a≠b))
  | a,_ => viewSlot vid a

def pairedKid (nid : Nat) (a b : PTrie) : NKid :=
  if isNode a then .node nid (nodeEnc a).length (viewTarget nid a)
    (a.hashOf.map UInt8.toNat) (b.hashOf.map UInt8.toNat)
  else .hash (a.hashOf.map UInt8.toNat)

def pairedKids : Nat→Kids→Kids→List NKid
  | _,.nil,_ => []
  | n,.none a,.none b => .none::pairedKids n a b
  | n,.some a as,.some b bs => pairedKid n a b::pairedKids (n+tsize a) as bs
  | n,a,_ => viewKids n a

def pairedNode (nid vid : Nat) : PTrie→PTrie→NodeV3
  | .leaf k a m,.leaf _ b _ => .leaf k (pairedSlot vid a b) ((u64 m).map UInt8.toNat)
  | .ext k a m,.ext _ b _ => .ext k (pairedKid (nid+1) a b) ((u64 m).map UInt8.toNat)
  | .branch a cs m,.branch b ds _ => .branch
      (match a,b with | some a,some b => some (pairedSlot vid a b) | a,_ => a.map (viewSlot vid))
      (pairedKids (nid+1) cs ds) ((u64 m).map UInt8.toNat)
  | a,_ => viewNode nid vid a

theorem pairedSlot_pre (vid : Nat) (a b : Slot) :
    (pairedSlot vid a b).bytes false=a.valueRef.map UInt8.toNat := by
  cases a <;> cases b <;> simp [pairedSlot,viewSlot,NSlot3.bytes,Slot.valueRef,digest]

theorem pairedSlot_post (vid : Nat) {a b : Slot} (h : WriteSlotPair a b)
    (hl : a.len=b.len) : (pairedSlot vid a b).bytes true=b.valueRef.map UInt8.toNat := by
  cases h <;> simp_all [pairedSlot,viewSlot,NSlot3.bytes,Slot.valueRef,Slot.len,digest]

theorem pairedKid_present (n : Nat) (a b : PTrie) :
    (pairedKid n a b).present=(viewKid n a).present := by
  unfold pairedKid viewKid
  split <;> rfl

theorem pairedKid_pre (n : Nat) (a b : PTrie) :
    (pairedKid n a b).bytes false=a.hashOf.map UInt8.toNat := by
  unfold pairedKid
  split <;> rfl

theorem pairedKid_post (n : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    (pairedKid n a b).bytes true=b.hashOf.map UInt8.toNat := by
  cases h <;> simp [pairedKid,isNode,NKid.bytes]

theorem pairedKids_post : ∀(n : Nat){a b : Kids},WriteKidsPair a b →
    (pairedKids n a b).flatMap (NKid.bytes true)=(Kids.hashes b).map UInt8.toNat
  | _,_,_,.nil => rfl
  | n,_,_,.none h => by simpa [pairedKids,NKid.bytes,Kids.hashes] using pairedKids_post n h
  | n,_,_,.some h hs => by
    simp only [pairedKids,List.flatMap_cons,pairedKid_post n h,Kids.hashes,List.map_append]
    rw [pairedKids_post _ hs]

theorem pairedKids_bitmap : ∀(n : Nat){a b : Kids},WriteKidsPair a b →
    kidBitmap (pairedKids n a b)=kidsBitmap b 0
  | _,_,_,.nil => rfl
  | n,_,_,.none h => by
    simp [pairedKids,kidBitmap_cons,NKid.present,kidsBitmap,runtime_bitmap_shift _ 1,pairedKids_bitmap n h]
  | n,_,_,.some h hs => by
    simp [pairedKids,kidBitmap_cons,pairedKid_present,kidsBitmap,runtime_bitmap_shift _ 1,
      pairedKids_bitmap _ hs]

def rootValueLen : PTrie→Nat
  | .leaf _ v _ => v.len
  | .branch (some v) _ _ => v.len
  | _ => 0

/-- Complete native post serialization, including branches. Only the value
length at this record is relevant; descendant hash windows are computed from
the actual paired post subtrees. -/
theorem pairedNode_post (nid vid : Nat) {a b : PTrie} (h : WriteTreePair a b)
    (hl : rootValueLen a=rootValueLen b) (hw : b.wf=true) (hn : isNode b=true) :
    (pairedNode nid vid a b).ser true=(nodeEnc b).map UInt8.toNat := by
  rw [←viewNode_ser nid vid b hw hn false]
  cases h with
  | hash h => simp [isNode] at hn
  | leaf k m hs =>
    simp only [pairedNode,viewNode,NodeV3.ser,pairedSlot_post vid hs hl,viewSlot_bytes]
  | ext k m hc =>
    simp only [pairedNode,viewNode,NodeV3.ser,pairedKid_post (nid+1) hc,viewKid_bytes]
  | branch m hv hcs =>
    cases hv with
    | none =>
      simp [pairedNode,viewNode,NodeV3.ser,pairedKids_bitmap _ hcs,pairedKids_post _ hcs]
    | some hs =>
      simp only [pairedNode,viewNode,NodeV3.ser,Option.map_some,pairedSlot_post vid hs hl,
        viewSlot_bytes,pairedKids_bitmap _ hcs,viewKids_bitmap,pairedKids_post _ hcs,viewKids_bytes]

theorem pairedKids_pre : ∀(n : Nat){a b : Kids},WriteKidsPair a b →
    (pairedKids n a b).flatMap (NKid.bytes false)=(Kids.hashes a).map UInt8.toNat
  | _,_,_,.nil => rfl
  | n,_,_,.none h => by simpa [pairedKids,NKid.bytes,Kids.hashes] using pairedKids_pre n h
  | n,_,_,.some h hs => by
    simp only [pairedKids,List.flatMap_cons,pairedKid_pre,Kids.hashes,List.map_append]
    rw [pairedKids_pre _ hs]

theorem native_pair_bitmap : ∀{a b : Kids},WriteKidsPair a b → ∀i,kidsBitmap a i=kidsBitmap b i
  | _,_,.nil,_ => rfl
  | _,_,.none h,i => native_pair_bitmap h (i+1)
  | _,_,.some _ hs,i => by simp only [kidsBitmap,native_pair_bitmap hs (i+1)]

/-- Pairing changes no byte in the node's prestate stream. -/
theorem pairedNode_pre (nid vid : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    (pairedNode nid vid a b).ser false=(viewNode nid vid a).ser false := by
  cases h with
  | hash h => rfl
  | leaf k m hs => simp [pairedNode,viewNode,NodeV3.ser,pairedSlot_pre]
  | ext k m hc => simp [pairedNode,viewNode,NodeV3.ser,pairedKid_pre]
  | branch m hv hcs =>
    cases hv with
    | none =>
      simp [pairedNode,viewNode,NodeV3.ser,pairedKids_bitmap _ hcs,pairedKids_pre _ hcs,
        native_pair_bitmap hcs 0]
    | some hs =>
      simp [pairedNode,viewNode,NodeV3.ser,pairedSlot_pre,pairedKids_bitmap _ hcs,
        pairedKids_pre _ hcs,native_pair_bitmap hcs 0]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
