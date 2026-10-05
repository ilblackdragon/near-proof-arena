import ZkFormal.Near.Link.ShaEnc
import ZkFormal.Near.Spec.SoundTrie

/-!
# ZkFormal.Near.Link.NodeSer — facts about the raw node serialization `NodeV.ser`

* `kidBitmap_eq` — the raw bitmap is `bitmapOf` of the records, `< 2^16`;
* `ser_vals` — every value of a serialization is raw, a byte, or below its length;
* `ser_length_post` — pre and post serializations have the same length.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

def kidTerm (x : NKid × Nat) : Nat := if x.1.present then 2 ^ x.2 else 0

theorem kidBitmap_aux : ∀ (l : List NKid) (i : Nat),
    ((l.zip (List.range' i l.length)).map kidTerm).sum = bitmapOf (l.map NKid.toRec) i
  | [], _ => rfl
  | a :: l, i => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      kidBitmap_aux l (i + 1), List.map_cons, bitmapOf]
    cases a <;> simp [kidTerm, NKid.present, NKid.toRec, kidBit]

theorem kidBitmap_eq (kids : List NKid) : kidBitmap kids = bitmapOf (kids.map NKid.toRec) 0 := by
  rw [← kidBitmap_aux, ← List.range_eq_range']; rfl

theorem bitmapOf_le : ∀ (l : List Kid) (i : Nat), bitmapOf l i + 2 ^ i ≤ 2 ^ (i + l.length)
  | [], i => by simp [bitmapOf]
  | k :: r, i => by
    have := bitmapOf_le r (i + 1)
    have hb : kidBit k ≤ 1 := by cases k <;> simp [kidBit]
    simp only [bitmapOf, List.length_cons]
    have e1 : i + 1 + r.length = i + (r.length + 1) := by omega
    rw [e1] at this
    have : kidBit k * 2 ^ i ≤ 2 ^ i := by
      calc kidBit k * 2 ^ i ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ hb
        _ = 2 ^ i := Nat.one_mul _
    rw [Nat.pow_succ] at *
    omega

theorem kidBitmap_lt {kids : List NKid} (h : kids.length = 16) : kidBitmap kids < 65536 := by
  rw [kidBitmap_eq]
  have := bitmapOf_le (kids.map NKid.toRec) 0
  simp [h] at this; omega

theorem hpN_length_le (k : List Nat) (b : Bool) : (hpN k b).length ≤ k.length + 1 := by
  unfold hpN; rw [List.length_map]; exact Sound.hexPrefix_length k b

theorem hpN_lt (k : List Nat) (b : Bool) : ∀ x ∈ hpN k b, x < 256 := by
  intro x hx; unfold hpN at hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact UInt8.toNat_lt _

theorem ser_length_post (v : NodeV) (hw : v.wf) : (v.ser true).length = (v.ser false).length := by
  cases v with
  | leaf k s m =>
    cases s <;> simp_all [NodeV.ser, NSlot.bytes, NodeV.wf, NSlot.wf]
  | ext k kid m =>
    cases kid <;> simp_all [NodeV.ser, NKid.bytes, NodeV.wf, NKid.wf]
  | branch v kids m =>
    obtain ⟨_, hv, hk, _⟩ := hw
    have hkids : (kids.flatMap (NKid.bytes true)).length = (kids.flatMap (NKid.bytes false)).length := by
      simp only [List.length_flatMap]
      congr 1; apply List.map_congr_left; intro kd hkd
      have := hk kd hkd
      cases kd <;> simp_all [NKid.bytes, NKid.wf]
    cases v with
    | none => simp [NodeV.ser, hkids]
    | some s =>
      have := hv s rfl
      cases s <;> simp_all [NodeV.ser, NSlot.bytes, NSlot.wf]

theorem mem_u32r {L x : Nat} (h : x ∈ u32r L) : x = L ∨ x = 0 := by
  simp only [u32r, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> simp [h]

theorem mem_slot_bytes {s : NSlot} {post : Bool} {x : Nat} (h : x ∈ s.bytes post) :
    x ∈ s.raw ∨ x < 256 := by
  cases s with
  | ref lenB hh => left; simpa [NSlot.bytes, NSlot.raw] using h
  | touched pre po =>
    simp only [NSlot.bytes, List.mem_append] at h
    rcases h with h | h
    · rcases mem_u32r h with rfl | rfl <;> (right; decide)
    · left; cases post <;> simp_all [NSlot.raw]

theorem mem_kid_bytes {kd : NKid} {post : Bool} {x : Nat} (h : x ∈ kd.bytes post) : x ∈ kd.raw := by
  cases kd with
  | none => simp [NKid.bytes] at h
  | hash hh => simpa [NKid.bytes, NKid.raw] using h
  | node c l r pre po => cases post <;> simp_all [NKid.bytes, NKid.raw]

/-- Every value of a serialization is a raw value, a byte, or below the length. -/
theorem ser_vals (v : NodeV) (hw : v.wf) (post : Bool) :
    ∀ x ∈ v.ser post, x ∈ v.raw ∨ x < 256 ∨ x < (v.ser false).length := by
  intro x hx
  cases v with
  | leaf k s m =>
    simp only [NodeV.ser, List.mem_append] at hx
    rcases hx with ((((h | h) | h) | h) | h)
    · simp at h; subst h; right; left; decide
    · rcases mem_u32r h with rfl | rfl
      · right; right; simp [NodeV.ser]; omega
      · right; left; decide
    · right; left; exact hpN_lt _ _ _ h
    · rcases mem_slot_bytes h with h | h
      · left; simp [NodeV.raw, h]
      · right; left; exact h
    · left; simp [NodeV.raw, h]
  | ext k kid m =>
    simp only [NodeV.ser, List.mem_append] at hx
    rcases hx with ((((h | h) | h) | h) | h)
    · simp at h; subst h; right; left; decide
    · rcases mem_u32r h with rfl | rfl
      · right; right; simp [NodeV.ser]; omega
      · right; left; decide
    · right; left; exact hpN_lt _ _ _ h
    · left; simp [NodeV.raw, mem_kid_bytes h]
    · left; simp [NodeV.raw, h]
  | branch sv kids m =>
    obtain ⟨hl, -, -, -⟩ := hw
    have hb := kidBitmap_lt hl
    simp only [NodeV.ser, List.mem_append] at hx
    rcases hx with (((h | h) | h) | h)
    · cases sv with
      | none => simp at h; subst h; right; left; decide
      | some s =>
        simp only [List.mem_append] at h
        rcases h with h | h
        · simp at h; subst h; right; left; decide
        · rcases mem_slot_bytes h with h | h
          · left; simp [NodeV.raw, h]
          · right; left; exact h
    · simp at h; rcases h with rfl | rfl
      · right; left; omega
      · right; left; omega
    · obtain ⟨kd, hkd, h⟩ := List.mem_flatMap.mp h
      left; simp only [NodeV.raw, List.mem_append, List.mem_flatMap]; left; right
      exact ⟨kd, hkd, mem_kid_bytes h⟩
    · left; simp [NodeV.raw, h]

end Link

end ZkFormal.Near
