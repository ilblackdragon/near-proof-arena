import ZkFormal.Near.Render.Proof.NodeInfo

/-!
# ZkFormal.Near.Render.Proof.ShaFit1 — node serializations of `mkInfo` are short bytes

`mkInfo` fills `pre`/`post` (and the digests `dpre`/`dpost`) in a loop over
the post-order; every entry ever written is `toNats (ser vh dig nr)` with a
32-byte value hash and windows of at most 32 bytes, so (`pre_ok`, `post_ok`)
every `pre n` / `post n` has bytes `< 256` and at most `sz0 (nodeAt n)` of
them, `sz0 nr` the serialized size with all windows 32 bytes (the `nodeSize`
of `Spec/Trie.lean` without the touched value).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- Serialized size of a record, all windows 32 bytes. -/
def sz0 (nr : NodeRec) : Nat := (ser (zeros 32) (fun _ => zeros 32) nr).length

theorem zeros_len : ∀ n, (zeros n).length = n
  | 0 => rfl
  | n + 1 => by simp [zeros, zeros_len n]

theorem concatAll_len (l : List Bytes) : (concatAll l).length = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [concatAll, ih]

theorem kids_len_le (dig : Nat → Bytes) (hd : ∀ c, (dig c).length ≤ 32) :
    ∀ kids : List Kid, ((kids.map (kidBytes dig)).map List.length).sum ≤
      ((kids.map (kidBytes fun _ => zeros 32)).map List.length).sum
  | [] => Nat.le_refl _
  | k :: ks => by
    have ih := kids_len_le dig hd ks
    simp only [List.map_cons, List.sum_cons]
    cases k with
    | none => simp only [kidBytes]; omega
    | hash h => simp only [kidBytes]; omega
    | node c => simp only [kidBytes, zeros_len]; have := hd c; omega

theorem vref_len_le (vh : Bytes) (hv : vh.length ≤ 32) (v : VSlot) :
    (vrefBytes vh v).length ≤ (vrefBytes (zeros 32) v).length := by
  cases v <;> simp [vrefBytes, zeros_len] <;> omega

theorem ser_len_le (vh : Bytes) (dig : Nat → Bytes) (hv : vh.length ≤ 32)
    (hd : ∀ c, (dig c).length ≤ 32) (nr : NodeRec) : (ser vh dig nr).length ≤ sz0 nr := by
  have hk := kids_len_le dig hd
  unfold sz0
  cases nr with
  | leaf k v mem =>
    have := vref_len_le vh hv v
    simp only [ser, List.length_append]; omega
  | ext k kid mem =>
    have := hk [kid]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    simp only [ser, List.length_append]; omega
  | branch v kids mem =>
    have := hk kids
    cases v with
    | none => simp only [ser, List.length_append, concatAll_len]; omega
    | some s =>
      have := vref_len_le vh hv s
      simp only [ser, List.length_append, concatAll_len]; omega

theorem toNats_lt (b : Bytes) : ∀ x ∈ toNats b, x < 256 := by
  intro x hx
  simp only [toNats, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.toNat_lt

/-! ## `mkInfo`'s serializations (closed form: `nodeSer` of the record tries) -/

theorem kids_hashes (g : Nat → PTrie) : ∀ kids : List Kid,
    Kids.hashes (kidsOf g kids) = concatAll (kids.map (kidBytes fun c => (g c).hashOf)) ∧
      ∀ i, kidsBitmap (kidsOf g kids) i = bitmapOf kids i
  | [] => ⟨rfl, fun _ => rfl⟩
  | k :: kids => by
    obtain ⟨h1, h2⟩ := kids_hashes g kids
    cases k with
    | none => exact ⟨by simp [kidsOf, Kids.hashes, h1, concatAll, kidBytes],
        fun i => by simp [kidsOf, kidsBitmap, bitmapOf, kidBit, h2]⟩
    | hash h => exact ⟨by simp [kidsOf, Kids.hashes, PTrie.hashOf, h1, concatAll, kidBytes],
        fun i => by simp [kidsOf, kidsBitmap, bitmapOf, kidBit, h2]⟩
    | node c => exact ⟨by simp [kidsOf, Kids.hashes, h1, concatAll, kidBytes],
        fun i => by simp [kidsOf, kidsBitmap, bitmapOf, kidBit, h2]⟩

/-- `nodeSer` of one record step is the record serialization `ser`. -/
theorem nodeSer_ser (vals : Nat → Bytes) (n : Nat) (g : Nat → PTrie) (nr : NodeRec)
    (hv : nr.touched = true → (vals n).length = 72) :
    nodeSer (Sound.nodeTree vals n g nr) = ser (sha256 (vals n)) (fun c => (g c).hashOf) nr := by
  have hslot : ∀ v : VSlot, (v = .touched → (vals n).length = 72) →
      (slotOf vals n v).valueRef = vrefBytes (sha256 (vals n)) v := by
    intro v h; cases v with
    | ref len hh => rfl
    | touched => simp [slotOf, Slot.valueRef, vrefBytes, h rfl]
  cases nr with
  | leaf k v mem =>
    simp only [Sound.nodeTree, nodeSer, ser]
    rw [hslot v (fun h => hv (by subst h; rfl))]
  | ext k kid mem =>
    simp only [Sound.nodeTree, nodeSer, ser]
    cases kid <;> rfl
  | branch v kids mem =>
    obtain ⟨h1, h2⟩ := kids_hashes g kids
    cases v with
    | none => simp only [Sound.nodeTree, Option.map_none, nodeSer, ser, h1, h2]
    | some s =>
      simp only [Sound.nodeTree, Option.map_some, nodeSer, ser, h1, h2]
      rw [hslot s (fun h => hv (by subst h; rfl))]

theorem mkInfo_ns (c : Claim) (e : Ext) : (mkInfo c e).ns = e.ns.toArray := rfl

section
variable {c : Claim} {e : Ext}

theorem pre_post_ok (hs : TreeShape e.ns) (vals : Nat → Bytes)
    (hv : ∀ k nr, e.ns[k]? = some nr → nr.touched = true → (vals k).length = 72) (n : Nat) :
    (toNats (nodeSer (treeOf e.ns vals e.ns.length n))).length ≤ sz0 ((mkInfo c e).nodeAt n) := by
  by_cases hn : n < e.ns.length
  · obtain ⟨d, hd0, hd⟩ := hs.depth
    have hget : e.ns[n]? = some e.ns[n] := by simp [hn]
    rw [NodeInfo.tree_node hs hd0 hd vals hget, nodeSer_ser _ _ _ _ (hv n _ hget), NodeInfo.info_nodeAt hn,
      toNats, List.length_map]
    refine ser_len_le _ _ (by simp [ArenaCore.sha256_length]) (fun c' => ?_) _
    by_cases hc : c' < e.ns.length
    · rw [NodeInfo.tree_hash hs vals hc, ArenaCore.sha256_length]; omega
    · cases h : e.ns.length with
      | zero => simp [treeOf, PTrie.hashOf]
      | succ N => simp [treeOf, List.getElem?_eq_none (show e.ns.length ≤ c' by omega), PTrie.hashOf]
  · have : e.ns.length ≤ n := by omega
    cases h : e.ns.length with
    | zero => simp [treeOf, nodeSer, toNats]
    | succ N => simp [treeOf, List.getElem?_eq_none (show e.ns.length ≤ n by omega), nodeSer, toNats]

/-- **`pre n`**: bytes, at most `sz0 (nodeAt n)` of them. -/
theorem pre_ok (c : Claim) (e : Ext) (hg : Good c e) (n : Nat) :
    ((mkInfo c e).pre.getD n []).length ≤ sz0 ((mkInfo c e).nodeAt n) ∧
      ∀ x ∈ (mkInfo c e).pre.getD n [], x < 256 := by
  by_cases hn : n < e.ns.length
  · rw [NodeInfo.info_pre hn]
    exact ⟨pre_post_ok hg.shape _ hg.vals_len n, toNats_lt _⟩
  · have : (mkInfo c e).pre.getD n [] = [] := by simp [mkInfo, Array.getD_eq_getD_getElem?, hn]
    simp [this]

theorem post_ok (c : Claim) (e : Ext) (hg : Good c e) (n : Nat) :
    ((mkInfo c e).post.getD n []).length ≤ sz0 ((mkInfo c e).nodeAt n) ∧
      ∀ x ∈ (mkInfo c e).post.getD n [], x < 256 := by
  by_cases hn : n < e.ns.length
  · rw [NodeInfo.info_post hn]
    refine ⟨pre_post_ok hg.shape _ (fun k nr hk ht => ?_) n, toNats_lt _⟩
    have hmem : k ∈ (mkInfo c e).touched := mem_touched.2 ⟨nr, hk, ht⟩
    have := acct_post hg k hmem
    rwa [vpost_eq hmem, NodeInfo.toNats_len] at this
  · have : (mkInfo c e).post.getD n [] = [] := by simp [mkInfo, Array.getD_eq_getD_getElem?, hn]
    simp [this]

end

end ZkFormal.Near.Render
