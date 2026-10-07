import ZkFormal.NearV3.Extract.Ups.UpsExt

/-!
# ZkFormal.NearV3.Extract.Ups.UpsRec — what a record's edges and bytes say about its post node (M7e, step 1)

Facts about one `nodeV3` record `s` (no table), used to derive the parts' `SrcShape`:

* **edges** (`edgesOf3`): a non-`END` edge of a branch is a `DOWN` edge to a revealed child at the symbol's
  slot (`edge_branch`); a `KEY` edge belongs to a leaf or an extension and sits before the key's end
  (`edge_key`); a `LEND` edge belongs to a leaf (`edge_lend`);
* **bytes** (`ser true`): byte 0 is the tag (`0` leaf, `3` extension, `1`/`2` branch without / with a value:
  `ser_tag`); byte 5 of a leaf / extension is the hex-prefix flag byte, whose high nibble is `2·isLeaf + odd`
  (`ser5_leaf`, `ser5_ext`); bytes 1–5 of an extension are `u32 |hp(k)| ‖ hp(k)[0]`, so `[1,0,0,0,0]` means
  `k = []` (`ext_nil_of`);
* **post nodes** (`post_eq`): record `n`'s post subtrie is `nodeTree3` of its `Rec3`, so the constructor, the
  key and the revealed / empty child slots carry over (`kidAt_node`, `kidAt_none`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Children -/

theorem kidAt_node (g : Nat → NearSpec.PTrie) : ∀ (l : List NKid) (j : Nat) {c lc r : Nat} {pre po : List Nat},
    l[j]? = some (NKid.node c lc r pre po) → UpsSpec.kidAt (kidsOf3 g (l.map NKid.toKid3)) j = some (g c)
  | [], _, _, _, _, _, _, h => by simp at h
  | k :: r, 0, _, _, _, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [NKid.toKid3, kidsOf3, UpsSpec.kidAt]
  | k :: r, j + 1, c, lc, rr, pre, po, h => by
    simp only [List.getElem?_cons_succ] at h
    have := kidAt_node g r j h
    cases k <;> simpa [NKid.toKid3, kidsOf3, UpsSpec.kidAt] using this

theorem kidAt_none (g : Nat → NearSpec.PTrie) : ∀ (l : List NKid) (j : Nat),
    l[j]? = some NKid.none → UpsSpec.kidAt (kidsOf3 g (l.map NKid.toKid3)) j = none
  | [], _, h => by simp at h
  | k :: r, 0, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [NKid.toKid3, kidsOf3, UpsSpec.kidAt]
  | k :: r, j + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    have := kidAt_none g r j h
    cases k <;> simpa [NKid.toKid3, kidsOf3, UpsSpec.kidAt] using this

/-! ## Edges -/

theorem ek_ne : EK_KEY ≠ EK_DOWN ∧ EK_KEY ≠ EK_VAL ∧ EK_KEY ≠ EK_LEND ∧ EK_LEND ≠ EK_DOWN ∧ EK_LEND ≠ EK_VAL ∧
    EK_LEND ≠ EK_KEY := by decide

/-- A non-`END` edge of a branch goes down to a revealed child in the symbol's slot. -/
theorem edge_branch {n : Nat} {s : NodeS3} {sv : Option NSlot3} {kids : List NKid} {m : List Nat}
    (hv : s.v = .branch sv kids m) {e : Msg} (he : e ∈ edgesOf3 n s) (hσ : e.getD 2 0 ≠ SYM_END) :
    ∃ c l r pre po, kids[e.getD 2 0]? = some (NKid.node c l r pre po) := by
  unfold edgesOf3 at he
  rw [hv] at he
  simp only [List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨⟨kd, j⟩, hmem, he⟩ | he
  · obtain ⟨hj, hkj⟩ := Link3.mem_zip_range hmem
    cases kd with
    | node c l r pre po =>
      simp only [Option.some.injEq] at he
      subst he
      refine ⟨c, l, r, pre, po, ?_⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [List.getElem?_eq_getElem hj, hkj]
    | none => simp at he
    | hash => simp at he
  · exfalso
    rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
    · simp at he
    · simp at he
    · simp only [List.mem_singleton] at he
      subst he; exact hσ rfl

/-- A `KEY` edge belongs to a leaf or an extension, before the end of its key. -/
theorem edge_key {n : Nat} {s : NodeS3} {e : Msg} (he : e ∈ edgesOf3 n s) (hk : e.getD 5 0 = EK_KEY) :
    (∃ k sl m, s.v = .leaf k sl m ∧ e.getD 1 0 < k.length) ∨
      (∃ k kid m, s.v = .ext k kid m ∧ e.getD 1 0 < k.length) := by
  have hne := ek_ne
  unfold edgesOf3 at he
  cases hv : s.v with
  | leaf k sl m =>
    rw [hv] at he
    simp only [List.mem_append, keyEdges3, List.mem_map, List.mem_range] at he
    rcases he with (⟨i, hi, rfl⟩ | he) | he
    · exact Or.inl ⟨k, sl, m, rfl, by simpa using hi⟩
    · exfalso; cases sl <;> simp at he; subst he; simp at hk; exact hne.2.1 hk.symm
    · exfalso; simp at he; subst he; simp at hk; exact hne.2.2.1 hk.symm
  | ext k kid m =>
    rw [hv] at he
    simp only [List.mem_append, keyEdges3, List.mem_map, List.mem_range] at he
    rcases he with ⟨i, hi, rfl⟩ | he
    · exact Or.inr ⟨k, kid, m, rfl, by simp; simp at hi; omega⟩
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x =>
        have hk0 : k ≠ [] := by intro h; subst h; simp at hl
        have hpos : 0 < k.length := List.length_pos_iff.mpr hk0
        refine Or.inr ⟨k, kid, m, rfl, ?_⟩
        cases kid <;> simp [hl] at he <;> subst he <;> simp <;> omega
  | branch sv kids m =>
    exfalso
    rw [hv] at he
    simp only [List.mem_append, List.mem_filterMap] at he
    rcases he with ⟨⟨kd, j⟩, -, he⟩ | he
    · cases kd <;> simp at he; subst he; simp at hk; exact hne.1 hk.symm
    · rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
      · simp at he
      · simp at he
      · simp only [List.mem_singleton] at he; subst he; simp at hk; exact hne.2.1 hk.symm

/-- A `LEND` edge belongs to a leaf. -/
theorem edge_lend {n : Nat} {s : NodeS3} {e : Msg} (he : e ∈ edgesOf3 n s) (hk : e.getD 5 0 = EK_LEND) :
    ∃ k sl m, s.v = .leaf k sl m := by
  have hne := ek_ne
  unfold edgesOf3 at he
  cases hv : s.v with
  | leaf k sl m => exact ⟨k, sl, m, rfl⟩
  | ext k kid m =>
    exfalso
    rw [hv] at he
    simp only [List.mem_append, keyEdges3, List.mem_map, List.mem_range] at he
    rcases he with ⟨i, hi, rfl⟩ | he
    · simp at hk; exact hne.2.2.2.2.2 hk.symm
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x => cases kid <;> simp [hl] at he <;> subst he <;> simp at hk <;> exact hne.2.2.2.2.2 hk.symm
  | branch sv kids m =>
    exfalso
    rw [hv] at he
    simp only [List.mem_append, List.mem_filterMap] at he
    rcases he with ⟨⟨kd, j⟩, -, he⟩ | he
    · cases kd <;> simp at he; subst he; simp at hk; exact hne.2.2.2.1 hk.symm
    · rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
      · simp at he
      · simp at he
      · simp only [List.mem_singleton] at he; subst he; simp at hk; exact hne.2.2.2.2.1 hk.symm

/-! ## Bytes -/

/-- The tag of a record's encoding. -/
def tagOf : NodeV3 → Nat
  | .leaf .. => 0
  | .ext .. => 3
  | .branch none .. => 1
  | .branch (some _) .. => 2

theorem ser_tag (v : NodeV3) (post : Bool) : (v.ser post).getD 0 0 = tagOf v := by
  cases v with
  | leaf => simp [NodeV3.ser, tagOf]
  | ext => simp [NodeV3.ser, tagOf]
  | branch sv kids m => cases sv <;> simp [NodeV3.ser, tagOf]

theorem hp_head (k : List Nat) (f : Bool) (hk : ∀ x ∈ k, x < 16) :
    (hpN k f).getD 0 0 / 16 = UpsSpec.lb f / 16 + k.length % 2 := by
  simp only [hpN, UpsSpec.hp_eq]
  have h16 : k.headD 0 < 16 := by
    cases k with
    | nil => simp
    | cons a r => simpa using hk a (by simp)
  rw [List.headD_eq_head?_getD] at h16
  split
  · next h =>
    simp only [List.map_cons, List.getD_cons_zero, UpsSpec.toNat_u8]
    cases f <;> simp [UpsSpec.lb] <;> omega
  · next h =>
    simp only [List.map_cons, List.getD_cons_zero, UpsSpec.toNat_u8]
    cases f <;> simp [UpsSpec.lb] <;> omega

theorem ser5_leaf (k : List Nat) (sl : NSlot3) (m : List Nat) (hk : ∀ x ∈ k, x < 16) :
    ((NodeV3.leaf k sl m).ser true).getD 5 0 / 16 = 2 + k.length % 2 := by
  have hl : 0 < (hpN k true).length := by simp [hpN, UpsSpec.hp_len]
  have e : ((NodeV3.leaf k sl m).ser true).getD 5 0 = (hpN k true).getD 0 0 := by
    simp only [NodeV3.ser, u32Bytes, toNats_u32, List.getD_eq_getElem?_getD, List.cons_append, List.nil_append, List.append_assoc,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
    rw [List.getElem?_append_left hl]
  rw [e, hp_head k true hk]; simp [UpsSpec.lb]

theorem ser5_ext (k : List Nat) (kid : NKid) (m : List Nat) (hk : ∀ x ∈ k, x < 16) :
    ((NodeV3.ext k kid m).ser true).getD 5 0 / 16 = k.length % 2 := by
  have hl : 0 < (hpN k false).length := by simp [hpN, UpsSpec.hp_len]
  have e : ((NodeV3.ext k kid m).ser true).getD 5 0 = (hpN k false).getD 0 0 := by
    simp only [NodeV3.ser, u32Bytes, toNats_u32, List.getD_eq_getElem?_getD, List.cons_append, List.nil_append, List.append_assoc,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
    rw [List.getElem?_append_left hl]
  rw [e, hp_head k false hk]; simp [UpsSpec.lb]

/-- An extension whose bytes 1–5 are `1 0 0 0 0` has the empty key. -/
theorem ext_nil_of (k : List Nat) (kid : NKid) (m : List Nat) (hk : ∀ x ∈ k, x < 16)
    (hlen : ((NodeV3.ext k kid m).ser true).length<2^22)
    (h1 : (List.range 4).map (fun i => ((NodeV3.ext k kid m).ser true).getD (1+i) 0)=[1,0,0,0])
    (h5 : ((NodeV3.ext k kid m).ser true).getD 5 0 = 0) : k = [] := by
  have hl : (hpN k false).length = k.length / 2 + 1 := by simp [hpN, UpsSpec.hp_len]
  have hb : (hpN k false).length<2^32 := by
    simp only [NodeV3.ser, List.length_append, List.length_cons, List.length_nil, u32Bytes_length] at hlen
    omega
  have hh : u32Bytes (hpN k false).length=[1,0,0,0] := by
    simpa [NodeV3.ser, List.range_succ, u32Bytes, toNats_u32, List.getD_eq_getElem?_getD] using h1
  have hval := congrArg le256 hh
  rw [u32Bytes_value hb] at hval
  have h5' := ser5_ext k kid m hk
  rw [h5] at h5'
  simp only [le256] at hval
  rw [hl] at hval
  exact List.length_eq_zero_iff.mp (by omega)

/-! ## Post nodes -/

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

/-- **A record's post subtrie** is its `Rec3` with post children. -/
theorem post_eq (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hb : Link3.ParentBal vs hds)
    (hvb : Link3.VParentBal vs es) (H : Link3.ShaHyp vs hds es others shaS shaR) (V' : List ValRec3)
    {n : Nat} (hn : n < vs.length) :
    fullTree (Rpost vs es) V' n = nodeTree3 V' (fullTree (Rpost vs es) V') (vs[n].v.toRec3 (Link3.vpos (Link3.vid0 es))) := by
  obtain ⟨h, hh, ht⟩ := Link3.head_of hN hhw hb n hn
  have hd := Link3.rootedDag3 hN hhw hvw hb hvb (Link3.vlen_le hvw) (Link3.rec_bytes hN hhw hvw hb H) hh
  exact Link3.fullTree_unfold_any hd V' (Link3.recsOf_get _ _ hn) (by simp only; rw [ht])

end

end ZkFormal.NearV3.UpsRows
