import ZkFormal.NearV3.Render.Ups.EncodePart

/-! Reusing a post-state child/value window as an unchanged output slot. These ordinary
slot constructors preserve identifiers and make inherited pre/post bytes equal. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def snapshotKid : NKid → NKid
  | .none => .none
  | .hash h => .hash h
  | .node c l r _ post => .node c l r post post

def snapshotValue : NSlot3 → NSlot3
  | .ref len h => .ref len h
  | .val len id size _ post _ => .val len id size post post false

@[simp] theorem snapshotKid_bytes (k : NKid) (post : Bool) :
    (snapshotKid k).bytes post=k.bytes true := by
  cases k <;> cases post <;> rfl

@[simp] theorem snapshotKid_present (k : NKid) :
    (snapshotKid k).present=k.present := by cases k <;> rfl

@[simp] theorem snapshotKid_none (k : NKid) : snapshotKid k=.none ↔ k=.none := by
  cases k <;> simp [snapshotKid]

theorem snapshotKid_wf {k : NKid} (h : k.wf) : (snapshotKid k).wf := by
  cases k <;> simp_all [snapshotKid,NKid.wf]

@[simp] theorem snapshotValue_bytes (s : NSlot3) (post : Bool) :
    (snapshotValue s).bytes post=s.bytes true := by
  cases s <;> cases post <;> rfl

theorem snapshotValue_wf {s : NSlot3} (h : s.wf) : (snapshotValue s).wf := by
  cases s with
  | ref => exact h
  | val len id size pre post written =>
    exact ⟨h.1,h.2.2.1,h.2.2.1,fun _ => rfl,h.2.2.2.2⟩

@[simp] theorem snapshotKids_bytes (kids : List NKid) (post : Bool) :
    (kids.map snapshotKid).flatMap (NKid.bytes post)=kids.flatMap (NKid.bytes true) := by
  simp [List.flatMap_map,Function.comp_def]

@[simp] theorem snapshotKids_bitmap (kids : List NKid) :
    kidBitmap (kids.map snapshotKid)=kidBitmap kids := by
  simp only [kidBitmap,List.length_map,List.zip_map_left,List.map_map,Function.comp_def]
  simp

@[simp] theorem snapshotKids_windows (kids : List NKid) :
    (NodeGen3.branchWins (kids.map snapshotKid)).length=(NodeGen3.branchWins kids).length := by
  simp [NodeGen3.branchWins,List.zip_map_left,List.filter_map,Function.comp_def]

end ZkFormal.NearV3.Render.UpsGen
