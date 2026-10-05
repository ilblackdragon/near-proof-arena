import ZkFormal.Near.Link.NodeHash

/-!
# ZkFormal.Near.Link.TrieHash — node digests and the trie hash

* `child_digest`, `root_digest` — every node's pre/post serialization is
  consumed (by its parent slot or as the root) with its own length, so it is
  bytes and the window is its `sha256`;
* `trie_hash` — the hash of the extracted trie is `sha256` of the root's
  serialization, for any touched values matching the value windows.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem child_digest {p : Nat} (hp : p < vs.length) {c' l r : Nat} {pre po : List Nat}
    (hm : (c', l, r, pre, po) ∈ vs[p].v.revealed) :
    ∃ hc : c' < vs.length,
      Bytes8 (vs[c'].v.ser false) ∧ pre = (sha256 (toBytes (vs[c'].v.ser false))).map UInt8.toNat ∧
      Bytes8 (vs[c'].v.ser true) ∧ po = (sha256 (toBytes (vs[c'].v.ser true))).map UInt8.toNat := by
  obtain ⟨hc, -, hl, -, -⟩ := parent_link h hp hm
  have hlt := vs_length_lt h.node
  have hmem : ∀ m ∈ [digMsg (msgId K_NPRE c') l pre, digMsg (msgId K_NPOST c') l po],
      m ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
    intro m hm'
    rw [nearRecvs_digest]; apply List.mem_append_left; apply List.mem_append_left
    unfold nodeRecvs; dsimp only; rw [if_pos rfl]
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨(vs[p], p), mem_zip_range.mpr ⟨hp, rfl⟩, List.mem_append_left _ ?_⟩
    exact List.mem_flatMap.mpr ⟨_, hm, hm'⟩
  have hw := h.node.wf _ (List.getElem_mem hc)
  have e1 := encOf_npre (publicOf c) vs rs as mv c'
  have e2 := encOf_npost (publicOf c) vs rs as mv c'
  rw [List.getElem?_eq_getElem hc] at e1 e2
  simp only [Option.map_some, Option.getD_some] at e1 e2
  obtain ⟨b1, d1⟩ := sha_ok c vs ws rs as mv ids shaS shaR h (msgId K_NPRE c') l pre
    (by unfold msgId K_NPRE; omega) (by rw [e1, hl]) (hmem _ (by simp))
  obtain ⟨b2, d2⟩ := sha_ok c vs ws rs as mv ids shaS shaR h (msgId K_NPOST c') l po
    (by unfold msgId K_NPOST; omega) (by rw [e2, hl, ser_length_post _ hw]) (hmem _ (by simp))
  rw [e1] at b1 d1; rw [e2] at b2 d2
  exact ⟨hc, b1, d1, b2, d2⟩

theorem root_digest (h0 : 0 < vs.length) :
    Bytes8 (vs[0].v.ser false) ∧ c.1.preStateRoot = sha256 (toBytes (vs[0].v.ser false)) ∧
    Bytes8 (vs[0].v.ser true) ∧ c.1.slicePostRoot = sha256 (toBytes (vs[0].v.ser true)) := by
  have hh := hdr_of c h.rcpt
  have hw := h.node.wf _ (List.getElem_mem h0)
  have hhd : vs.headD default = vs[0] := by
    cases vs with
    | nil => simp at h0
    | cons a l => rfl
  have hmem : ∀ m ∈ [digMsg K_NPRE (vs[0].v.ser false).length
        ((List.range 32).map fun j => pubNat (publicOf c) (PV_PRE + j)),
      digMsg K_NPOST (vs[0].v.ser false).length
        ((List.range 32).map fun j => pubNat (publicOf c) (PV_POST + j))],
      m ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
    intro m hm'
    rw [nearRecvs_digest]; apply List.mem_append_left; apply List.mem_append_left
    unfold nodeRecvs; dsimp only; rw [if_pos rfl, hhd]
    exact List.mem_append_left _ hm'
  have e1 := encOf_npre (publicOf c) vs rs as mv 0
  have e2 := encOf_npost (publicOf c) vs rs as mv 0
  rw [List.getElem?_eq_getElem h0] at e1 e2
  simp only [Option.map_some, Option.getD_some] at e1 e2
  have k1 : msgId K_NPRE 0 = K_NPRE := rfl
  have k2 : msgId K_NPOST 0 = K_NPOST := rfl
  rw [k1] at e1; rw [k2] at e2
  obtain ⟨b1, d1⟩ := sha_ok c vs ws rs as mv ids shaS shaR h K_NPRE _
    ((List.range 32).map fun j => pubNat (publicOf c) (PV_PRE + j))
    (by unfold K_NPRE P; omega) (by rw [e1]) (hmem _ (by simp))
  obtain ⟨b2, d2⟩ := sha_ok c vs ws rs as mv ids shaS shaR h K_NPOST _
    ((List.range 32).map fun j => pubNat (publicOf c) (PV_POST + j))
    (by unfold K_NPOST P; omega) (by rw [e2, ser_length_post _ hw]) (hmem _ (by simp))
  rw [e1] at b1 d1; rw [e2] at b2 d2
  have p1 : (List.range 32).map (fun j => pubNat (publicOf c) (PV_PRE + j)) =
      c.1.preStateRoot.map UInt8.toNat := (pub_pre hh)
  have p2 : (List.range 32).map (fun j => pubNat (publicOf c) (PV_POST + j)) =
      c.1.slicePostRoot.map UInt8.toNat := (pub_post hh)
  rw [p1] at d1; rw [p2] at d2
  exact ⟨b1, map_toNat_inj d1, b2, map_toNat_inj d2⟩

theorem ns_get {n : Nat} (hn : n < vs.length) : (vs.map (·.v.toRec))[n]? = some vs[n].v.toRec := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hn]; rfl

/-- **The trie hash.** -/
theorem trie_hash (post : Bool) (vals : Nat → Bytes)
    (hval : ∀ n (hn : n < vs.length), ∀ pre po, vs[n].v.vwin = some (pre, po) →
      u32 (vals n).length ++ sha256 (vals n) = u32 72 ++ toBytes (sel post pre po)) :
    ∀ F n (hn : n < vs.length), vs.length ≤ vs[n].depth + F →
      (treeOf (vs.map (·.v.toRec)) vals F n).hashOf = sha256 (toBytes (vs[n].v.ser post))
  | 0, n, hn, hF => absurd (depth_lt h hn) (by omega)
  | F + 1, n, hn, hF => by
    have hd := (tree_shape h).depth
    rw [Sound.treeOf_succ (ns_get h hn)]
    have hw := h.node.wf _ (List.getElem_mem hn)
    -- bytes of this node
    have hb : Bytes8 (vs[n].v.ser post) := by
      by_cases h0 : n = 0
      · subst h0
        obtain ⟨b1, -, b2, -⟩ := root_digest h hn
        cases post; exact b1; exact b2
      · obtain ⟨p, hpc⟩ := has_parent h (Nat.pos_of_ne_zero h0) hn
        obtain ⟨hp, l, r, pre, po, hm⟩ := childOf_iff.mp hpc
        obtain ⟨_, b1, -, b2, -⟩ := child_digest h hp hm
        cases post; exact b1; exact b2
    apply nodeTree_hash vals n _ _ post hw hb _ (hval n hn)
    intro c' l r pre po hm
    obtain ⟨hc, b1, d1, b2, d2⟩ := child_digest h hn hm
    have hch : ChildOf (vs.map (·.v.toRec)) n c' := childOf_iff.mpr ⟨hn, l, r, pre, po, hm⟩
    obtain ⟨_, _, -, hdep⟩ := child_facts h hch
    have hdc : vs[c'].depth = vs[n].depth + 1 := by
      have := depth_lt h hn
      have hlt := vs_length_lt h.node
      exact (ofNat_inj (by omega) (h.node.small _ (List.getElem_mem hc)).1 hdep).symm
    rw [trie_hash post vals hval F c' hc (by omega)]
    cases post
    · simp only [sel, Bool.false_eq_true, if_false]; rw [d1, toBytes_map_toNat]
    · simp only [sel, if_true]; rw [d2, toBytes_map_toNat]

end Hyp

end Link

end ZkFormal.Near
