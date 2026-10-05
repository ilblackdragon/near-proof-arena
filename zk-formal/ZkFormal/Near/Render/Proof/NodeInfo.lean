import ZkFormal.Near.Render.Proof.AcctFacts
import ZkFormal.Near.Link.NodeHash

/-!
# ZkFormal.Near.Render.Proof.NodeInfo — depths and serializations of `mkInfo`

Under `TreeShape`: every node is reachable from the root (`reach_all`), the
generator's depths are the tree depths (`info_depth`), and the record trie of a
node is one `nodeTree` step over the record tries of its children
(`tree_node`, fuel stability).  The pre/post serializations are `nodeSer` of
the record tries (`info_pre`, `info_post`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

set_option linter.unusedSimpArgs false

namespace NodeInfo

/-! ## Reachability -/

section
variable {ns : List NodeRec} (hs : TreeShape ns)
include hs

theorem has_parent {k : Nat} (h0 : 0 < k) (hk : k < ns.length) : ∃ p, ChildOf ns p k := by
  have h1 := hs.unique_parent k h0 hk
  unfold refCount at h1
  obtain ⟨nr, hnr, hpos⟩ := Link.exists_pos_of_sum (fun nr => nr.kids.count (Kid.node k)) ns (by omega)
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hnr
  exact ⟨p, _, by simp [hp], List.count_pos_iff.1 hpos⟩

theorem reach_all {d : Nat → Nat} (hd : ∀ n c, ChildOf ns n c → d c = d n + 1) :
    ∀ m k, d k = m → k < ns.length → Sound.Reach ns 0 k := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k hdk hk
    by_cases h0 : k = 0
    · subst h0; exact .refl
    · obtain ⟨p, hp⟩ := has_parent hs (by omega) hk
      have := hd p k hp
      obtain ⟨nr, hnr, _⟩ := id hp
      have hpl : p < ns.length := by
        rcases Nat.lt_or_ge p ns.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hnr; cases hnr
      exact .tail (ih (d p) (by omega) p rfl hpl) hp

end

/-! ## Depths -/

theorem kidIds_mem {nr : NodeRec} {c : Nat} : c ∈ kidIds nr ↔ Kid.node c ∈ nr.kids := by
  simp only [kidIds, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, he⟩
    cases k <;> simp at he; subst he; exact hk
  · intro h; exact ⟨_, h, rfl⟩

theorem getD_arr {ns : List NodeRec} {n : Nat} {nr : NodeRec} (h : ns[n]? = some nr) :
    ns.toArray.getD n (.branch none [] 0) = nr := by
  have hn : n < ns.length := by
    rcases Nat.lt_or_ge n ns.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.getElem?_eq_getElem hn] at h
  simp [Array.getD_eq_getD_getElem?, hn, Option.some.inj h]

theorem kid_child {ns : List NodeRec} {n c : Nat} (h : c ∈ kidIds (ns.toArray.getD n (.branch none [] 0))) :
    ChildOf ns n c := by
  by_cases hn : n < ns.length
  · refine ⟨ns[n], by simp [hn], ?_⟩
    have : ns.toArray.getD n (.branch none [] 0) = ns[n] := getD_arr (by simp [hn])
    rw [this] at h; exact kidIds_mem.1 h
  · simp [Array.getD_eq_getD_getElem?, hn, kidIds, NodeRec.kids] at h

section
variable {ns : List NodeRec} {d : Nat → Nat} (hd : ∀ n c, ChildOf ns n c → d c = d n + 1)
include hd

theorem subD_val : ∀ f n x, ∀ p ∈ subD ns.toArray f n x, p.2 + d n = x + d p.1
  | 0, _, _, p, hp => by simp [subD] at hp
  | f + 1, n, x, p, hp => by
    simp only [subD, List.mem_cons, List.mem_flatMap] at hp
    rcases hp with rfl | ⟨c, hc, hp⟩
    · rfl
    · have := subD_val f c (x + 1) p hp
      have := hd n c (kid_child hc)
      omega

end

theorem mem_subD_child {ns : List NodeRec} (hs : TreeShape ns) {k : Nat} :
    ∀ f a x p, p ∈ (subD ns.toArray f a x).map Prod.fst → ChildOf ns p k →
      k ∈ (subD ns.toArray (f + 1) a x).map Prod.fst
  | 0, _, _, _, hp, _ => by simp [subD] at hp
  | f + 1, a, x, p, hp, hpk => by
    rw [subD] at hp ⊢
    simp only [List.map_cons, List.mem_cons, List.map_flatMap, List.mem_flatMap] at hp ⊢
    obtain ⟨nr, hnr, hk⟩ := hpk
    right
    rcases hp with rfl | ⟨c, hc, hp⟩
    · refine ⟨k, ?_, ?_⟩
      · rw [getD_arr hnr]; exact kidIds_mem.2 hk
      · simp [subD]
    · exact ⟨c, hc, mem_subD_child hs f c (x + 1) p hp ⟨nr, hnr, hk⟩⟩

theorem mem_subD {ns : List NodeRec} (hs : TreeShape ns) {d : Nat → Nat}
    (hd : ∀ n c, ChildOf ns n c → d c = d n + 1) {k : Nat} (hr : Sound.Reach ns 0 k) :
    ∀ f, d k - d 0 < f → k ∈ (subD ns.toArray f 0 0).map Prod.fst := by
  induction hr with
  | refl => intro f hf; obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩; simp [subD]
  | @tail p k hp hpk ih =>
    intro f hf
    have h1 := hd p k hpk
    have h2 := Sound.Reach.depth_le d hd hp
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact mem_subD_child hs f' 0 0 p (ih f' (by omega)) hpk

theorem fold_set_size : ∀ (L : List (Nat × Nat)) (a : Array Nat),
    (L.foldl (fun a p => a.set! p.1 p.2) a).size = a.size
  | [], _ => rfl
  | p :: L, a => by rw [List.foldl_cons, fold_set_size L]; simp

theorem fold_set (k v : Nat) : ∀ (L : List (Nat × Nat)) (a : Array Nat), k < a.size →
    (∀ p ∈ L, p.1 = k → p.2 = v) → (k ∈ L.map Prod.fst ∨ a.getD k 0 = v) →
    (L.foldl (fun a p => a.set! p.1 p.2) a).getD k 0 = v
  | [], a, _, _, h => by simpa using h
  | p :: L, a, hk, hv, h => by
    rw [List.foldl_cons]
    apply fold_set k v L _ (by simpa using hk) (fun q hq => hv q (by simp [hq]))
    by_cases hpk : p.1 = k
    · right
      have := hv p (by simp) hpk
      subst hpk
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hk, this]
    · rcases h with h | h
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hpk
        · left; exact h
      · right
        rw [← h]
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hpk]

/-- The generator's depths are the tree depths. -/
theorem info_depth {c : Claim} {e : Ext} (hs : TreeShape e.ns) {d : Nat → Nat} (hd0 : d 0 = 0)
    (hd : ∀ n c, ChildOf e.ns n c → d c = d n + 1) {k : Nat} (hk : k < e.ns.length) :
    (mkInfo c e).depth.getD k 0 = d k := by
  have hr := reach_all hs hd _ k rfl hk
  have hlt := Sound.Reach.depth_lt d hd hs hr hs.nonempty
  simp only [mkInfo, List.size_toArray]
  apply fold_set k (d k) _ _ (by simpa using hk)
  · intro p hp hpk
    have := subD_val hd _ _ _ p hp
    rw [hd0, hpk] at this; omega
  · left; exact mem_subD hs hd hr _ (by omega)

/-- Depths along child links. -/
theorem depth_child {c : Claim} {e : Ext} (hs : TreeShape e.ns) {n k : Nat} (h : ChildOf e.ns n k) :
    (mkInfo c e).depth.getD k 0 = (mkInfo c e).depth.getD n 0 + 1 := by
  obtain ⟨d, hd0, hd⟩ := hs.depth
  have hn : n < e.ns.length := by
    obtain ⟨nr, hnr, _⟩ := h
    rcases Nat.lt_or_ge n e.ns.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hnr; cases hnr
  rw [info_depth hs hd0 hd (hs.child_range n k h).2, info_depth hs hd0 hd hn]
  exact hd n k h

theorem depth_root {c : Claim} {e : Ext} (hs : TreeShape e.ns) : (mkInfo c e).depth.getD 0 0 = 0 := by
  obtain ⟨d, hd0, hd⟩ := hs.depth
  rw [info_depth hs hd0 hd hs.nonempty, hd0]


/-! ## Record tries: fuel stability -/

section
variable {ns : List NodeRec} (hs : TreeShape ns) {d : Nat → Nat} (hd0 : d 0 = 0)
  (hd : ∀ n c, ChildOf ns n c → d c = d n + 1)
include hs hd0 hd

theorem d_lt {n : Nat} (hn : n < ns.length) : d n < ns.length := by
  have := Sound.Reach.depth_lt d hd hs (reach_all hs hd _ n rfl hn) hs.nonempty
  omega

theorem tree_stable (vals : Nat → Bytes) : ∀ F G n, n < ns.length → ns.length ≤ d n + F →
    ns.length ≤ d n + G → treeOf ns vals F n = treeOf ns vals G n
  | 0, _, n, hn, hF, _ => absurd hF (by have := d_lt hs hd0 hd hn; omega)
  | _ + 1, 0, n, hn, _, hG => absurd hG (by have := d_lt hs hd0 hd hn; omega)
  | F + 1, G + 1, n, hn, hF, hG => by
    have hget : ns[n]? = some ns[n] := by simp [hn]
    rw [Sound.treeOf_succ hget, Sound.treeOf_succ hget]
    have hc : ∀ c, Kid.node c ∈ ns[n].kids → treeOf ns vals F c = treeOf ns vals G c := by
      intro c hc
      have hch : ChildOf ns n c := ⟨_, hget, hc⟩
      have := hd n c hch
      exact tree_stable vals F G c (hs.child_range n c hch).2 (by omega) (by omega)
    cases h : ns[n] with
    | leaf k v mem => rfl
    | ext k kid mem =>
      rw [h] at hc
      simp only [Sound.nodeTree]
      rw [Sound.kidTree_congr (fun c hk => hc c (by simp [NodeRec.kids, hk]))]
    | branch v kids mem =>
      rw [h] at hc
      simp only [Sound.nodeTree]
      rw [Sound.kidsOf_congr kids (fun c hk => hc c hk)]

/-- The record trie of a node is one `nodeTree` step over its children's. -/
theorem tree_node (vals : Nat → Bytes) {n : Nat} {nr : NodeRec} (hn : ns[n]? = some nr) :
    treeOf ns vals ns.length n = Sound.nodeTree vals n (treeOf ns vals ns.length) nr := by
  have hlt : n < ns.length := by
    rcases Nat.lt_or_ge n ns.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hn; cases hn
  rw [tree_stable hs hd0 hd vals ns.length (ns.length + 1) n hlt (by omega) (by omega), Sound.treeOf_succ hn]

end

theorem nodeTree_hashOf (vals : Nat → Bytes) (n : Nat) (g : Nat → PTrie) (nr : NodeRec) :
    (Sound.nodeTree vals n g nr).hashOf = sha256 (nodeSer (Sound.nodeTree vals n g nr)) := by
  cases nr with
  | leaf k v mem => rfl
  | ext k kid mem => rfl
  | branch v kids mem => cases v <;> rfl

/-! ## The pre/post serializations -/

theorem ofNats_toNats (b : Bytes) : ofNats (toNats b) = b := Link.toBytes_map_toNat b

theorem toNats_lt (b : Bytes) : ∀ x ∈ toNats b, x < 256 := by
  intro x hx; unfold toNats at hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact UInt8.toNat_lt _

section
variable {c : Claim} {e : Ext}

theorem info_N : (mkInfo c e).ns.size = e.ns.length := by simp [mkInfo]

theorem info_pre {n : Nat} (hn : n < e.ns.length) :
    (mkInfo c e).pre.getD n [] = toNats (nodeSer (treeOf e.ns e.vals0 e.ns.length n)) := by
  simp [mkInfo, Array.getD_eq_getD_getElem?, hn]

theorem info_post {n : Nat} (hn : n < e.ns.length) :
    (mkInfo c e).post.getD n [] = toNats (nodeSer (treeOf e.ns (e.valsAt e.rs.length) e.ns.length n)) := by
  simp [mkInfo, Array.getD_eq_getD_getElem?, hn]

theorem info_nodeAt {n : Nat} (hn : n < e.ns.length) : (mkInfo c e).nodeAt n = e.ns[n] := by
  simp [Info.nodeAt, mkInfo, Array.getD_eq_getD_getElem?, hn]

variable (hs : TreeShape e.ns)
include hs

theorem tree_hash (vals : Nat → Bytes) {n : Nat} (hn : n < e.ns.length) :
    (treeOf e.ns vals e.ns.length n).hashOf = sha256 (nodeSer (treeOf e.ns vals e.ns.length n)) := by
  obtain ⟨d, hd0, hd⟩ := hs.depth
  rw [tree_node hs hd0 hd vals (n := n) (nr := e.ns[n]) (by simp [hn])]
  exact nodeTree_hashOf _ _ _ _

theorem info_preDig {n : Nat} (hn : n < e.ns.length) :
    (mkInfo c e).preDig n = toNats (treeOf e.ns e.vals0 e.ns.length n).hashOf := by
  rw [Info.preDig, info_pre hn, shaN, ofNats_toNats, tree_hash hs _ hn]

theorem info_postDig {n : Nat} (hn : n < e.ns.length) :
    (mkInfo c e).postDig n = toNats (treeOf e.ns (e.valsAt e.rs.length) e.ns.length n).hashOf := by
  rw [Info.postDig, info_post hn, shaN, ofNats_toNats, tree_hash hs _ hn]

end

/-! ## The serialization of the view -/

open Link in
/-- `nodeSer` of a record with children `g` is the raw serialization of its view
(`Link.nodeTree_hash` without the hash). -/
theorem nodeSer_nodeTree (vals : Nat → Bytes) (n : Nat) (g : Nat → PTrie) (v : NodeV) (post : Bool)
    (hw : v.wf) (hb : Bytes8 (v.ser post))
    (hkid : ∀ c l r pre po, (c, l, r, pre, po) ∈ v.revealed → (g c).hashOf = toBytes (Link.sel post pre po))
    (hval : ∀ pre po, v.vwin = some (pre, po) →
      u32 (vals n).length ++ sha256 (vals n) = u32 72 ++ toBytes (Link.sel post pre po)) :
    nodeSer (Sound.nodeTree vals n g v.toRec) = toBytes (v.ser post) := by
  cases v with
  | leaf k sl m =>
    obtain ⟨-, hsw, hm⟩ := hw
    have hL := hpN_len_lt (k := k) (b := true) hb (by simp [NodeV.ser, u32r])
    simp only [NodeV.toRec, Sound.nodeTree, nodeSer, NodeV.ser, toBytes_append]
    rw [toBytes_u32r (by unfold hpN; rw [List.length_map]; exact hL), toBytes_hpN,
      slot_hash hsw post vals n (fun pre po he => hval pre po (by subst he; rfl)),
      u64, leN_leN' hm]
    unfold hpN; rw [List.length_map]; rfl
  | ext k kid m =>
    obtain ⟨-, hne, hkw, hm⟩ := hw
    have hL := hpN_len_lt (k := k) (b := false) hb (by simp [NodeV.ser, u32r])
    simp only [NodeV.toRec, Sound.nodeTree, nodeSer, NodeV.ser, toBytes_append]
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
      simp only [NodeV.toRec, Sound.nodeTree, Option.map_none, nodeSer, NodeV.ser, toBytes_append]
      rw [hbm', hk1, u64, leN_leN' hm]; rfl
    | some sl =>
      simp only [NodeV.toRec, Sound.nodeTree, Option.map_some, nodeSer, NodeV.ser, toBytes_append]
      rw [hbm', hk1, u64, leN_leN' hm,
        slot_hash (hsv sl rfl) post vals n (fun pre po he => hval pre po (by subst he; rfl))]
      rfl

/-- Every key of the revealed nodes has fewer than 510 nibbles (its hex-prefix
encoding is shorter than 256 bytes, as the `node` table's `HPL` row requires).
Not implied by `Good` (keys `< 512` nibbles); see R-L6e-2. -/
def KeyBound (e : Ext) : Prop := ∀ nr ∈ e.ns, nr.key.length < 510

theorem packNibbles_len : ∀ (l : List Nat), (packNibbles l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [packNibbles]
  | a :: b :: l => by
    simp only [packNibbles, List.length_cons, packNibbles_len l]; omega

theorem hexPrefix_len (k : List Nat) (b : Bool) : (hexPrefix k b).length = 1 + k.length / 2 := by
  cases k with
  | nil => simp [hexPrefix, packNibbles]
  | cons n rest =>
    by_cases h : (rest.length + 1) % 2 = 1
    · simp only [hexPrefix, List.length_cons, h, packNibbles_len]; omega
    · have h' : (rest.length + 1) % 2 = 0 := by omega
      simp only [hexPrefix, List.length_cons, h', packNibbles_len]; omega

theorem leBytes_lt (w x : Nat) : ∀ y ∈ leBytes w x, y < 256 := toNats_lt _
theorem shaN_lt (b : List Nat) : ∀ y ∈ shaN b, y < 256 := toNats_lt _
theorem shaN_len (b : List Nat) : (shaN b).length = 32 := by
  simp [shaN, toNats, ArenaCore.sha256_length]
theorem leBytes_len (w x : Nat) : (leBytes w x).length = w := by
  simp [leBytes, toNats, leN_length]
theorem toNats_len (b : Bytes) : (toNats b).length = b.length := by simp [toNats]

end NodeInfo

end ZkFormal.Near.Render
