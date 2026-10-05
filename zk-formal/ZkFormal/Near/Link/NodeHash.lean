import ZkFormal.Near.Link.Tree
import ZkFormal.Near.Spec.SoundTrie

/-!
# ZkFormal.Near.Link.NodeHash — hashing one extracted node

`nodeTree_hash`: the node hash of a record (with children built by `g`) is
`sha256` of the raw serialization the node table emits, when the windows are
the children's hashes and the value windows the value hashes.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem toBytes_hpN (k : List Nat) (b : Bool) : toBytes (hpN k b) = hexPrefix k b := by
  unfold hpN; exact toBytes_map_toNat _

def sel (post : Bool) (pre po : List Nat) : List Nat := if post then po else pre

theorem kidsOf_hash (g : Nat → PTrie) (post : Bool) : ∀ (kids : List NKid),
    (∀ kd ∈ kids, kd.wf) →
    (∀ c l r pre po, NKid.node c l r pre po ∈ kids → (g c).hashOf = toBytes (sel post pre po)) →
    Kids.hashes (kidsOf g (kids.map NKid.toRec)) = toBytes (kids.flatMap (NKid.bytes post)) ∧
    ∀ i, kidsBitmap (kidsOf g (kids.map NKid.toRec)) i = bitmapOf (kids.map NKid.toRec) i
  | [], _, _ => ⟨rfl, fun _ => rfl⟩
  | kd :: kids, hw, hg => by
    obtain ⟨ih1, ih2⟩ := kidsOf_hash g post kids (fun k hk => hw k (by simp [hk]))
      (fun c l r pre po hm => hg c l r pre po (by simp [hm]))
    cases kd with
    | none =>
      refine ⟨?_, fun i => ?_⟩
      · simp only [List.map_cons, NKid.toRec, kidsOf, Kids.hashes, List.flatMap_cons, NKid.bytes,
          List.nil_append, ih1]
      · simp only [List.map_cons, NKid.toRec, kidsOf, kidsBitmap, bitmapOf, kidBit, ih2]; simp
    | hash hh =>
      refine ⟨?_, fun i => ?_⟩
      · simp only [List.map_cons, NKid.toRec, kidsOf, Kids.hashes, PTrie.hashOf, List.flatMap_cons,
          NKid.bytes, toBytes_append, ih1]
      · simp only [List.map_cons, NKid.toRec, kidsOf, kidsBitmap, bitmapOf, kidBit, ih2]; simp
    | node c l r pre po =>
      refine ⟨?_, fun i => ?_⟩
      · simp only [List.map_cons, NKid.toRec, kidsOf, Kids.hashes, List.flatMap_cons,
          NKid.bytes, toBytes_append, ih1, hg c l r pre po (by simp)]
        cases post <;> rfl
      · simp only [List.map_cons, NKid.toRec, kidsOf, kidsBitmap, bitmapOf, kidBit, ih2]; simp

theorem toBytes_bitmap {bm : Nat} (h : bm < 65536) : toBytes [bm % 256, bm / 256] = u16 bm := by
  simp only [toBytes, u16, leN, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨trivial, UInt8.toNat_inj.mp ?_⟩
  simp only [UInt8.toNat_ofNat']; omega

theorem toBytes_u32r_len {L : Nat} (h : L < 256) : toBytes (u32r L) = u32 L := toBytes_u32r h

theorem slot_hash {s : NSlot} (hw : s.wf) (post : Bool) (vals : Nat → Bytes) (n : Nat)
    (hval : ∀ pre po, s = .touched pre po →
      u32 (vals n).length ++ sha256 (vals n) = u32 72 ++ toBytes (sel post pre po)) :
    (slotOf vals n s.toRec).valueRef = toBytes (s.bytes post) := by
  cases s with
  | ref lenB hh =>
    simp only [NSlot.toRec, slotOf, Slot.valueRef, NSlot.bytes, toBytes_append]
    rw [u32, leN_leN' hw.1]
  | touched pre po =>
    simp only [NSlot.toRec, slotOf, Slot.valueRef, NSlot.bytes, toBytes_append,
      toBytes_u32r (show 72 < 256 by decide)]
    rw [hval pre po rfl]; cases post <;> rfl

theorem hpN_len_lt {k : List Nat} {b : Bool} {l : List Nat} (hb : Bytes8 l)
    (hm : (hpN k b).length ∈ l) : (hexPrefix k b).length < 256 := by
  have := hb _ hm; unfold hpN at this; rwa [List.length_map] at this

theorem nodeTree_hash (vals : Nat → Bytes) (n : Nat) (g : Nat → PTrie) (v : NodeV) (post : Bool)
    (hw : v.wf) (hb : Bytes8 (v.ser post))
    (hkid : ∀ c l r pre po, (c, l, r, pre, po) ∈ v.revealed → (g c).hashOf = toBytes (sel post pre po))
    (hval : ∀ pre po, v.vwin = some (pre, po) →
      u32 (vals n).length ++ sha256 (vals n) = u32 72 ++ toBytes (sel post pre po)) :
    (Sound.nodeTree vals n g v.toRec).hashOf = sha256 (toBytes (v.ser post)) := by
  cases v with
  | leaf k sl m =>
    obtain ⟨-, hsw, hm⟩ := hw
    have hL := hpN_len_lt (k := k) (b := true) hb (by simp [NodeV.ser, u32r])
    simp only [NodeV.toRec, Sound.nodeTree, PTrie.hashOf, NodeV.ser, toBytes_append]
    rw [toBytes_u32r (by unfold hpN; rw [List.length_map]; exact hL), toBytes_hpN,
      slot_hash hsw post vals n (fun pre po he => hval pre po (by subst he; rfl)),
      u64, leN_leN' hm]
    unfold hpN; rw [List.length_map]; rfl
  | ext k kid m =>
    obtain ⟨-, hne, hkw, hm⟩ := hw
    have hL := hpN_len_lt (k := k) (b := false) hb (by simp [NodeV.ser, u32r])
    simp only [NodeV.toRec, Sound.nodeTree, PTrie.hashOf, NodeV.ser, toBytes_append]
    rw [toBytes_u32r (by unfold hpN; rw [List.length_map]; exact hL), toBytes_hpN, u64, leN_leN' hm]
    have hk : (kidTree g kid.toRec).hashOf = toBytes (kid.bytes post) := by
      cases kid with
      | none => exact absurd rfl hne
      | hash hh => rfl
      | node c l r pre po =>
        simp only [NKid.toRec, kidTree, NKid.bytes]
        rw [hkid c l r pre po (by simp [NodeV.revealed])]; cases post <;> rfl
    rw [hk]; unfold hpN; rw [List.length_map]; rfl
  | branch sv kids m =>
    obtain ⟨hl, hsv, hkw, hm⟩ := hw
    obtain ⟨hk1, hk2⟩ := kidsOf_hash g post kids hkw (fun c l r pre po hmem => hkid c l r pre po
      (by simp only [NodeV.revealed, List.mem_filterMap]; exact ⟨_, hmem, rfl⟩))
    have hbm := kidBitmap_lt hl
    have hbm' : toBytes [kidBitmap kids % 256, kidBitmap kids / 256] =
        u16 (kidsBitmap (kidsOf g (kids.map NKid.toRec)) 0) := by
      rw [hk2, ← kidBitmap_eq]; exact toBytes_bitmap hbm
    cases sv with
    | none =>
      simp only [NodeV.toRec, Sound.nodeTree, Option.map_none, PTrie.hashOf, NodeV.ser,
        toBytes_append]
      rw [hbm', hk1, u64, leN_leN' hm]; rfl
    | some sl =>
      simp only [NodeV.toRec, Sound.nodeTree, Option.map_some, PTrie.hashOf, NodeV.ser,
        toBytes_append]
      rw [hbm', hk1, u64, leN_leN' hm,
        slot_hash (hsv sl rfl) post vals n (fun pre po he => hval pre po (by subst he; rfl))]
      rfl

end Link

end ZkFormal.Near
