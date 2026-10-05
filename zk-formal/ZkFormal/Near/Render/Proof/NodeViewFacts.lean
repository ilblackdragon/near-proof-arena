import ZkFormal.Near.Render.Proof.NodeInfo

/-!
# ZkFormal.Near.Render.Proof.NodeViewFacts — the honest node views

`nodeVOf I n nr` is a well-formed view of record `nr` (`view_wf`,
`view_toRec`); its revealed children are the record's (`view_revealed`); under
`Good` and `KeyBound` its pre/post serializations are the generator's
(`view_pre`, `view_post`), and in any case they have the same length
(`view_len`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

set_option linter.unusedSimpArgs false

namespace NodeInfo

theorem toBytes_toNats (b : Bytes) : toBytes (toNats b) = b := Link.toBytes_map_toNat b

theorem leN'_leBytes {w x : Nat} (h : x < 256 ^ w) : leN' (leBytes w x) = x := by
  rw [Link.leN'_eq, leBytes, toBytes_toNats, NearSpec.leNat_leN w x h]

section
variable (I : Info) (n : Nat)

theorem view_toRec {nr : NodeRec} (hw : nr.wf) : (nodeVOf I n nr).toRec = nr := by
  have hkid : ∀ k : Kid, k.wf → (nkidOf I k).toRec = k := by
    intro k _; cases k <;> simp [nkidOf, NKid.toRec, toBytes_toNats]
  have hslot : ∀ s : VSlot, s.wf → (nslotOf I n s).toRec = s := by
    intro s hs; cases s with
    | ref len h =>
      simp only [VSlot.wf] at hs
      have : leN' (leBytes 4 len) = len := leN'_leBytes (by have := hs.1; simp at this ⊢; omega)
      simp [nslotOf, NSlot.toRec, toBytes_toNats, this]
    | touched => rfl
  cases nr with
  | leaf k v mem =>
    obtain ⟨-, -, hv, hm⟩ := hw
    simp [nodeVOf, NodeV.toRec, hslot v hv, leN'_leBytes (w := 8) (show mem < 256 ^ 8 by omega)]
  | ext k kid mem =>
    obtain ⟨-, -, -, hk, hm⟩ := hw
    simp [nodeVOf, NodeV.toRec, hkid kid hk, leN'_leBytes (w := 8) (show mem < 256 ^ 8 by omega)]
  | branch v kids mem =>
    obtain ⟨-, hv, hk, hm⟩ := hw
    simp only [nodeVOf, NodeV.toRec, List.map_map, leN'_leBytes (w := 8) (show mem < 256 ^ 8 by omega)]
    congr 1
    · cases v with
      | none => rfl
      | some s => simp [hslot s (hv s rfl)]
    · conv => rhs; rw [← List.map_id kids]
      apply List.map_congr_left; intro k hk'; exact hkid k (hk k hk')

theorem view_wf {nr : NodeRec} (hw : nr.wf) : (nodeVOf I n nr).wf := by
  have hkid : ∀ k : Kid, k.wf → (nkidOf I k).wf := by
    intro k hk; cases k with
    | none => trivial
    | hash h => simpa [nkidOf, NKid.wf, toNats_len, Kid.wf] using hk
    | node c => simp [nkidOf, NKid.wf, Info.preDig, Info.postDig, shaN_len]
  have hslot : ∀ s : VSlot, s.wf → (nslotOf I n s).wf := by
    intro s hs; cases s with
    | ref len h => simp only [VSlot.wf] at hs; simp [nslotOf, NSlot.wf, leBytes_len, toNats_len, hs.2]
    | touched => simp [nslotOf, NSlot.wf, shaN_len]
  cases nr with
  | leaf k v mem =>
    obtain ⟨hk, -, hv, -⟩ := hw
    exact ⟨fun x hx => of_decide_eq_true (List.all_eq_true.1 hk x hx), hslot v hv, leBytes_len 8 mem⟩
  | ext k kid mem =>
    obtain ⟨hk, -, hne, hkw, -⟩ := hw
    refine ⟨fun x hx => of_decide_eq_true (List.all_eq_true.1 hk x hx), ?_, hkid kid hkw, leBytes_len 8 mem⟩
    cases kid <;> simp_all [nkidOf]
  | branch v kids mem =>
    obtain ⟨hl, hv, hk, -⟩ := hw
    refine ⟨by simp [hl], fun s hs => ?_, fun kd hkd => ?_, leBytes_len 8 mem⟩
    · cases v with
      | none => cases hs
      | some s' => simp at hs; subst hs; exact hslot s' (hv s' rfl)
    · obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hkd; exact hkid k (hk k hk')

/-- Revealed children of the view. -/
def revOf (c' : Nat) : Nat × Nat × Nat × List Nat × List Nat :=
  (c', (I.pre.getD c' []).length, I.res.getD c' c', I.preDig c', I.postDig c')

theorem view_revealed (nr : NodeRec) : (nodeVOf I n nr).revealed = (kidIds nr).map (revOf I) := by
  cases nr with
  | leaf k v mem => rfl
  | ext k kid mem => cases kid <;> rfl
  | branch v kids mem =>
    simp only [nodeVOf, NodeV.revealed, kidIds, NodeRec.kids, List.filterMap_map]
    rw [List.map_filterMap]
    congr 1; funext k; cases k <;> rfl

theorem view_touched (nr : NodeRec) : (nodeVOf I n nr).touched = nr.touched := by
  cases nr with
  | leaf k v mem => cases v <;> rfl
  | ext k kid mem => rfl
  | branch v kids mem =>
    rcases v with _ | v
    · rfl
    · cases v <;> rfl

theorem view_vwin {nr : NodeRec} {pre po : List Nat} (h : (nodeVOf I n nr).vwin = some (pre, po)) :
    nr.touched = true ∧ pre = shaN (I.vpre.getD n []) ∧ po = shaN (I.vpost.getD n []) := by
  cases nr with
  | leaf k v mem =>
    cases v with
    | ref _ _ => simp [nodeVOf, nslotOf, NodeV.vwin] at h
    | touched =>
      simp only [nodeVOf, nslotOf, NodeV.vwin, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨rfl, h.1.symm, h.2.symm⟩
  | ext k kid mem => simp [nodeVOf, NodeV.vwin] at h
  | branch v kids mem =>
    rcases v with _ | v
    · simp [nodeVOf, NodeV.vwin] at h
    · cases v with
      | ref _ _ => simp [nodeVOf, nslotOf, NodeV.vwin] at h
      | touched =>
        simp only [nodeVOf, Option.map_some, nslotOf] at h
        simp only [NodeV.vwin, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨rfl, h.1.symm, h.2.symm⟩

theorem slot_b8 (s : VSlot) (post : Bool) : ∀ y ∈ (nslotOf I n s).bytes post, y < 256 := by
  intro y hy
  cases s with
  | ref len h =>
    simp only [nslotOf, NSlot.bytes, List.mem_append] at hy
    rcases hy with hy | hy
    · exact leBytes_lt _ _ y hy
    · exact toNats_lt _ y hy
  | touched =>
    simp only [nslotOf, NSlot.bytes, List.mem_append] at hy
    rcases hy with hy | hy
    · simp [u32r] at hy; omega
    · cases post
      · exact shaN_lt _ y hy
      · exact shaN_lt _ y hy

theorem kid_b8 (k : Kid) (post : Bool) : ∀ y ∈ (nkidOf I k).bytes post, y < 256 := by
  intro y hy
  cases k with
  | none => simp [nkidOf, NKid.bytes] at hy
  | hash h => exact toNats_lt _ y hy
  | node c => cases post <;> exact shaN_lt _ y hy

theorem view_bytes8 {nr : NodeRec} (hw : nr.wf) (hk : nr.key.length < 510) (post : Bool) :
    Bytes8 ((nodeVOf I n nr).ser post) := by
  intro y hy
  have hp : ∀ (k : List Nat) (b : Bool), k.length < 510 → ∀ y ∈ u32r (hpN k b).length ++ hpN k b, y < 256 := by
    intro k b hk y hy
    rcases List.mem_append.1 hy with hy | hy
    · have : (hpN k b).length < 256 := by
        unfold hpN; rw [List.length_map, hexPrefix_len]; omega
      simp [u32r] at hy; omega
    · exact Link.hpN_lt k b y hy
  cases nr with
  | leaf k v mem =>
    simp only [nodeVOf, NodeV.ser, List.append_assoc, List.mem_append, List.mem_singleton] at hy
    rcases hy with rfl | hy | hy | hy | hy
    · omega
    · exact hp k true hk y (List.mem_append.2 (.inl hy))
    · exact hp k true hk y (List.mem_append.2 (.inr hy))
    · exact slot_b8 I n v post y hy
    · exact leBytes_lt _ _ y hy
  | ext k kid mem =>
    simp only [nodeVOf, NodeV.ser, List.append_assoc, List.mem_append, List.mem_singleton] at hy
    rcases hy with rfl | hy | hy | hy | hy
    · omega
    · exact hp k false hk y (List.mem_append.2 (.inl hy))
    · exact hp k false hk y (List.mem_append.2 (.inr hy))
    · exact kid_b8 I kid post y hy
    · exact leBytes_lt _ _ y hy
  | branch v kids mem =>
    obtain ⟨hl, -, -, -⟩ := hw
    have hbm := Link.kidBitmap_lt (kids := kids.map (nkidOf I)) (by simp [hl])
    simp only [nodeVOf, NodeV.ser, List.append_assoc, List.mem_append] at hy
    rcases hy with hy | hy | hy | hy
    · cases v with
      | none => simp at hy; omega
      | some s =>
        simp only [Option.map_some, List.mem_append, List.mem_singleton] at hy
        rcases hy with rfl | hy
        · omega
        · exact slot_b8 I n s post y hy
    · simp at hy; omega
    · simp only [List.mem_flatMap, List.mem_map] at hy
      obtain ⟨_, ⟨k, -, rfl⟩, hy⟩ := hy
      exact kid_b8 I k post y hy
    · exact leBytes_lt _ _ y hy

end

/-! ## The view serializes as the generator -/

section
variable {c : Claim} {e : Ext}

theorem ser_generic (hs : TreeShape e.ns) (hwf : ∀ nr ∈ e.ns, nr.wf) (vals : Nat → Bytes) (post : Bool)
    (hvals : ∀ k nr, e.ns[k]? = some nr → nr.touched = true → (vals k).length = 72 ∧
      toNats (sha256 (vals k)) = Link.sel post (shaN ((mkInfo c e).vpre.getD k []))
        (shaN ((mkInfo c e).vpost.getD k [])))
    (hdig : ∀ k, k < e.ns.length → toNats (treeOf e.ns vals e.ns.length k).hashOf =
      Link.sel post ((mkInfo c e).preDig k) ((mkInfo c e).postDig k))
    {n : Nat} (hn : n < e.ns.length) (hk : e.ns[n].key.length < 510) :
    (nodeVOf (mkInfo c e) n e.ns[n]).ser post = toNats (nodeSer (treeOf e.ns vals e.ns.length n)) := by
  obtain ⟨d, hd0, hd⟩ := hs.depth
  have hget : e.ns[n]? = some e.ns[n] := by simp [hn]
  have hw := hwf _ (List.getElem_mem hn)
  rw [tree_node hs hd0 hd vals hget]
  have h1 : Sound.nodeTree vals n (treeOf e.ns vals e.ns.length) e.ns[n] =
      Sound.nodeTree vals n (treeOf e.ns vals e.ns.length) (nodeVOf (mkInfo c e) n e.ns[n]).toRec := by
    rw [view_toRec _ n hw]
  have hb := view_bytes8 (mkInfo c e) n hw hk post
  rw [h1, nodeSer_nodeTree vals n _ _ post (view_wf _ n hw) hb]
  · exact (Link.map_toNat_toBytes hb).symm
  · intro c' l r pre po hm
    rw [view_revealed, List.mem_map] at hm
    obtain ⟨c'', hc, he⟩ := hm
    simp only [revOf, Prod.mk.injEq] at he
    obtain ⟨rfl, -, -, rfl, rfl⟩ := he
    have hch : ChildOf e.ns n c'' := ⟨_, hget, kidIds_mem.1 hc⟩
    rw [← hdig c'' (hs.child_range n c'' hch).2, toBytes_toNats]
  · intro pre po hvw
    obtain ⟨ht, rfl, rfl⟩ := view_vwin _ n hvw
    obtain ⟨hl, hsha⟩ := hvals n _ hget ht
    rw [hl, ← hsha, toBytes_toNats]

variable (hg : Good c e)
include hg

theorem view_pre {n : Nat} (hn : n < e.ns.length) (hk : e.ns[n].key.length < 510) :
    (nodeVOf (mkInfo c e) n e.ns[n]).ser false = (mkInfo c e).pre.getD n [] := by
  rw [info_pre hn]
  refine ser_generic hg.shape hg.nodes_wf e.vals0 false ?_ ?_ hn hk
  · intro k nr hk' ht
    have hmem : k ∈ (mkInfo c e).touched := mem_touched.2 ⟨nr, hk', ht⟩
    refine ⟨hg.vals_len k nr hk' ht, ?_⟩
    simp only [Link.sel, Bool.false_eq_true, if_false, vpre_eq hmem, shaN, ofNats_toNats]
  · intro k hk'
    simp only [Link.sel, Bool.false_eq_true, if_false, info_preDig hg.shape hk']

theorem view_post {n : Nat} (hn : n < e.ns.length) (hk : e.ns[n].key.length < 510) :
    (nodeVOf (mkInfo c e) n e.ns[n]).ser true = (mkInfo c e).post.getD n [] := by
  rw [info_post hn]
  refine ser_generic hg.shape hg.nodes_wf (e.valsAt e.rs.length) true ?_ ?_ hn hk
  · intro k nr hk' ht
    have hmem : k ∈ (mkInfo c e).touched := mem_touched.2 ⟨nr, hk', ht⟩
    have := acct_post hg k hmem
    rw [vpost_eq hmem, toNats_len] at this
    refine ⟨this, ?_⟩
    simp only [Link.sel, if_true, vpost_eq hmem, shaN, ofNats_toNats]
  · intro k hk'
    simp only [Link.sel, if_true, info_postDig hg.shape hk']

end

end NodeInfo

end ZkFormal.Near.Render
