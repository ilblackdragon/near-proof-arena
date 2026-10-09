import ZkFormal.NearV3.Link.Dag3
import ZkFormal.NearV3.Spec.Codec

/-!
# ZkFormal.NearV3.Link.NodeHash3 — record bytes are the node preimages

`enc_tree`: the raw serialisation of a node view is `nodeEnc` of its spec node, once its
revealed kids' windows are their hashes and its revealed value windows / length bytes are
the value's `sha256` / length.  `enc_fullTree`: along the ranked DAG of an instance, with
every revealed kid window the `sha256` of the kid record's bytes (the `DIGEST` lookups) and
every revealed value window the `sha256` of the value (the value `DIGEST` lookups),
`nodeEnc (fullTree n) = toB (ser n)`, hence `digest n = sha256 (toB (ser n))`.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

theorem toB_le256 : ∀ (l : List Nat), (∀ x ∈ l, x < 256) → toB l = leN l.length (le256 l)
  | [], _ => rfl
  | x :: r, h => by
    have hx := h x (by simp)
    have ih := toB_le256 r (fun y hy => h y (by simp [hy]))
    simp only [toB, List.map_cons, List.length_cons, leN, le256] at ih ⊢
    rw [ih, show (x + 256 * le256 r) % 256 = x by omega, show (x + 256 * le256 r) / 256 = le256 r by omega]

theorem toB_u32r {L : Nat} (h : L < 256) : toB (u32r L) = u32 L := by
  rw [toB_le256 _ (by simp [u32r]; omega)]; simp [u32r, le256, u32]

theorem toB_u32Bytes (n : Nat) : toB (u32Bytes n) = u32 n := u32Bytes_toBytes n

theorem toB_toNat (l : Bytes) : toB (l.map UInt8.toNat) = l := by
  unfold toB; rw [List.map_map]
  have : (UInt8.ofNat ∘ UInt8.toNat) = fun x => x := by funext x; exact UInt8.ofNat_toNat
  rw [this, List.map_id']

theorem toB_hpN (k : List Nat) (b : Bool) : toB (hpN k b) = hexPrefix k b := toB_toNat _

theorem toB_append (a b : List Nat) : toB (a ++ b) = toB a ++ toB b := List.map_append

theorem toB_u16 {x : Nat} (h : x < 65536) : toB [x % 256, x / 256] = u16 x := by
  simp only [toB, List.map_cons, List.map_nil, u16, leN]
  congr 2; congr 1; omega

theorem toB_len (l : List Nat) : (toB l).length = l.length := List.length_map _

/-- The bitmap of the spec children. -/
theorem kidBitmap_spec (g : Nat → PTrie) : ∀ (l : List NKid) (i : Nat),
    ((l.zip (List.range' i l.length)).map fun (kd, j) => if kd.present then 2 ^ j else 0).sum =
      kidsBitmap (kidsOf3 g (l.map NKid.toKid3)) i
  | [], _ => by simp [kidsOf3, kidsBitmap]
  | kd :: l, i => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      kidBitmap_spec g l (i + 1), List.map_cons]
    cases kd <;> simp [NKid.present, NKid.toKid3, kidsOf3, kidsBitmap]

theorem kidBitmap_eq3 (g : Nat → PTrie) (l : List NKid) :
    kidBitmap l = kidsBitmap (kidsOf3 g (l.map NKid.toKid3)) 0 := by
  rw [← kidBitmap_spec g l 0, ← List.range_eq_range']; rfl

theorem bitmap_lt : ∀ (l : List NKid) (i : Nat),
    ((l.zip (List.range' i l.length)).map fun (kd, j) => if kd.present then 2 ^ j else 0).sum + 2 ^ i ≤
      2 ^ (i + l.length)
  | [], i => by simp
  | kd :: l, i => by
    have ih := bitmap_lt l (i + 1)
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.sum_cons]
    generalize ((l.zip (List.range' (i + 1) l.length)).map fun (kd, j) => if kd.present then 2 ^ j else 0).sum = S at ih ⊢
    have e1 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ]; omega
    have e2 : i + 1 + l.length = i + (l.length + 1) := by omega
    rw [e1, e2] at ih
    have ht : (if kd.present then 2 ^ i else 0) ≤ 2 ^ i := by split <;> omega
    simp only at ht ⊢
    omega

theorem kidBitmap_aux (l : List NKid) : kidBitmap l =
    ((l.zip (List.range' 0 l.length)).map fun (kd, j) => if kd.present then 2 ^ j else 0).sum := by
  unfold kidBitmap; rw [List.range_eq_range']

theorem kidBitmap_lt3 {l : List NKid} (h : l.length = 16) : kidBitmap l < 65536 := by
  have := bitmap_lt l 0
  have e : 2 ^ (0 + l.length) = 65536 := by rw [h]
  rw [kidBitmap_aux]; omega

/-- Hashes of the spec children. -/
theorem hashes_spec (g : Nat → PTrie) : ∀ (l : List NKid),
    (∀ c l' r pre po, NKid.node c l' r pre po ∈ l → (g c).hashOf = toB pre) →
    Kids.hashes (kidsOf3 g (l.map NKid.toKid3)) = toB (l.flatMap (NKid.bytes false))
  | [], _ => rfl
  | kd :: l, h => by
    have ih := hashes_spec g l (fun c l' r pre po hm => h c l' r pre po (by simp [hm]))
    cases kd with
    | none => simpa [NKid.toKid3, kidsOf3, Kids.hashes, NKid.bytes] using ih
    | hash hh =>
      simp only [List.map_cons, NKid.toKid3, kidsOf3, Kids.hashes, PTrie.hashOf, List.flatMap_cons, NKid.bytes,
        toB_append, ih]
    | node c l' r pre po =>
      simp only [List.map_cons, NKid.toKid3, kidsOf3, Kids.hashes, List.flatMap_cons, NKid.bytes,
        toB_append, ih, h c l' r pre po (by simp)]
      rfl

/-- Value slot bytes are the `valueRef` of the spec slot. -/
theorem slot_spec (V : List ValRec3) (f : Nat → Nat) (sl : NSlot3) (hw : sl.wf)
    (hb : ∀ x ∈ sl.bytes false, x < 256)
    (hv : ∀ lb i l pre po w, sl = .val lb i l pre po w →
      (valOf V (f i)).length = l ∧ sha256 (valOf V (f i)) = toB pre) :
    (slot3 V (sl.toV3 f)).valueRef = toB (sl.bytes false) := by
  cases sl with
  | ref lenB h =>
    obtain ⟨h4, -⟩ := hw
    simp only [NSlot3.toV3, slot3, Slot.valueRef, NSlot3.bytes, toB_append]
    rw [toB_le256 lenB (fun x hx => hb x (by simp [NSlot3.bytes, hx])), h4]; rfl
  | val lenB i l pre po w =>
    obtain ⟨h4, -, -, -, h3, hle⟩ := hw
    obtain ⟨hl, hs⟩ := hv lenB i l pre po w rfl
    have hlb : ∀ x ∈ lenB, x < 256 := fun x hx => hb x (by simp [NSlot3.bytes, hx])
    simp only [NSlot3.toV3, slot3, Slot.valueRef, NSlot3.bytes, toB_append, hs]
    rw [toB_le256 lenB hlb, h4, hl, hle hlb]; rfl

/-- **One record.** -/
theorem enc_tree (V : List ValRec3) (f : Nat → Nat) (g : Nat → PTrie) (v : NodeV3) (hw : v.wf)
    (hb : ∀ x ∈ v.ser false, x < 256)
    (hk : ∀ c l r pre po, (c, l, r, pre, po) ∈ v.revealed → (g c).hashOf = toB pre)
    (hv : ∀ i l pre po w, v.value = some (i, l, pre, po, w) →
      (valOf V (f i)).length = l ∧ sha256 (valOf V (f i)) = toB pre) :
    nodeEnc (nodeTree3 V g (v.toRec3 f)) = toB (v.ser false) := by
  cases v with
  | leaf k sl m =>
    obtain ⟨-, hsw, hm8⟩ := hw
    simp only [NodeV3.ser, List.mem_append] at hb
    simp only [NodeV3.toRec3, nodeTree3, nodeEnc, NodeV3.ser, toB_append]
    rw [toB_u32Bytes, toB_hpN, slot_spec V f sl hsw (fun x hx => hb x (Or.inl (Or.inr hx)))
        (fun lb i l pre po w h => hv i l pre po w (by subst h; simp [NodeV3.value])),
      toB_le256 m (fun x hx => hb x (Or.inr hx)), hm8]
    simp only [hpN, List.length_map]; rfl
  | ext k kid m =>
    obtain ⟨-, hne, hkw, hm8⟩ := hw
    simp only [NodeV3.ser, List.mem_append] at hb
    have hkid : (kidTree3 g kid.toKid3).hashOf = toB (kid.bytes false) := by
      cases kid with
      | none => exact absurd rfl hne
      | hash h => rfl
      | node c l r pre po =>
        exact hk c l r pre po (by simp [NodeV3.revealed])
    simp only [NodeV3.toRec3, nodeTree3, nodeEnc, NodeV3.ser, toB_append]
    rw [toB_u32Bytes, toB_hpN, hkid, toB_le256 m (fun x hx => hb x (Or.inr hx)), hm8]
    simp only [hpN, List.length_map]; rfl
  | branch sv kids m =>
    obtain ⟨h16, hsv, hkw, hm8⟩ := hw
    simp only [NodeV3.ser, List.mem_append] at hb
    have hbm := kidBitmap_lt3 h16
    have hh := hashes_spec g kids (fun c l r pre po hm => hk c l r pre po (by
      simp only [NodeV3.revealed, List.mem_filterMap]; exact ⟨_, hm, rfl⟩))
    have hmem := toB_le256 m (fun x hx => hb x (Or.inr hx))
    rw [hm8] at hmem
    cases sv with
    | none =>
      simp only [NodeV3.toRec3, nodeTree3, Option.map_none, nodeEnc, NodeV3.ser, toB_append,
        ← kidBitmap_eq3 g kids, ← toB_u16 hbm, hh, hmem]
      rfl
    | some sl =>
      have hs := slot_spec V f sl (hsv sl rfl) (fun x hx => hb x (Or.inl (Or.inl (Or.inl (by simp [hx])))))
        (fun lb i l pre po w h => hv i l pre po w (by subst h; simp [NodeV3.value]))
      simp only [NodeV3.toRec3, nodeTree3, Option.map_some, nodeEnc, NodeV3.ser, toB_append,
        ← kidBitmap_eq3 g kids, ← toB_u16 hbm, hh, hmem, hs]
      rfl

theorem isNode_tree (V : List ValRec3) (g : Nat → PTrie) (r : Rec3) : isNode (nodeTree3 V g r) = true := by
  cases r with
  | leaf => rfl
  | ext => rfl
  | branch => rfl

/-- **Along the DAG of an instance**: record bytes are the preimages of the spec subtries. -/
theorem enc_fullTree {vs : List NodeS3} {V : List ValRec3} {f : Nat → Nat} {τ root : Nat} {rk : Nat → Nat}
    (hd : RootedDagR (recsOf f vs) V τ root rk) (hw : NodeWf3 vs)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hk : ∀ p (hp : p < vs.length), ∀ c l r pre po, (c, l, r, pre, po) ∈ vs[p].v.revealed →
      ∃ hc : c < vs.length, pre = (sha256 (toB (vs[c].v.ser false))).map UInt8.toNat)
    (hv : ∀ p (hp : p < vs.length), ∀ i l pre po w, vs[p].v.value = some (i, l, pre, po, w) →
      (valOf V (f i)).length = l ∧ pre = (sha256 (valOf V (f i))).map UInt8.toNat) :
    ∀ n, InInst (recsOf f vs) τ n → ∃ hn : n < vs.length,
      nodeEnc (fullTree (recsOf f vs) V n) = toB (vs[n].v.ser false) ∧ isNode (fullTree (recsOf f vs) V n) = true := by
  apply dag_inductionR hd
  intro n nr hnr ht ih
  have hn : n < vs.length := by have := lt_of_getElem? hnr; rwa [recsOf_length] at this
  have hnr' := hnr
  rw [recsOf_get _ _ hn] at hnr
  simp only [Option.some.injEq] at hnr; subst hnr
  refine ⟨hn, ?_⟩
  rw [fullTree_unfoldR hd hnr' ht]
  refine ⟨enc_tree V f _ _ (hw.wf _ (List.getElem_mem hn)) (hbytes _ (List.getElem_mem hn)) ?_ ?_, isNode_tree _ _ _⟩
  · intro c l r pre po hm
    obtain ⟨hc, hpre⟩ := hk n hn c l r pre po hm
    obtain ⟨_hc, he, hnode⟩ := ih c ((kids_toRec3 f _ c).mpr ⟨l, r, pre, po, hm⟩)
    rw [hashOf_eq_enc _ hnode, he, hpre, toB_toNat]
  · intro i l pre po w hval
    obtain ⟨h1, h2⟩ := hv n hn i l pre po w hval
    exact ⟨h1, by rw [h2, toB_toNat]⟩

end ZkFormal.NearV3.Link3
