import ZkFormal.NearV3.Extract.Ups.UpsWalk

/-!
# ZkFormal.NearV3.Extract.Ups.UpsShape — `SrcOk` = generic node facts + the kind's shape (M7e, step 1)

`SrcOk` (what a part's kind needs from its source node) splits into
* **`NodeOk3 P`**: facts every post subtrie of a record has — encoding `< 2^22` bytes, usage `< 2^64`, key
  nibbles `< 16` and keys `< 510` nibbles, 36-byte value slots of length `< 2^32`, 16 children, 32-byte
  child hashes.  **`post_nodeOk`** proves it for `fullTree R V' n` of every record `n` (the hex-prefix
  length is a serialized byte, so `< 256`; slots and children from `NodeV3.wf` and the post SHA facts);
* **`SrcShape`**: the constructor of the source and the kind's slot / key conditions (a descend's target
  slot holds a child, an inserted slot is empty, a moved key is longer than `I`, a pass-through is
  `.ext []`).  These come from the walk and the case (open, UPSV3-DESIGN §8.2).

**`srcOk_of`**: `NodeOk3 P → SrcShape … P → SrcOk … P`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Generic facts of a source node. -/
structure NodeOk3 (P : NearSpec.PTrie) : Prop where
  len : (nodeEnc P).length < 2 ^ 22
  mem : P.memD < 2 ^ 64
  leaf : ∀ k sl m, P = .leaf k sl m →
    (∀ x ∈ k, x < 16) ∧ k.length < 510 ∧ sl.valueRef.length = 36 ∧ sl.len < 2 ^ 32
  ext : ∀ k c m, P = .ext k c m → (∀ x ∈ k, x < 16) ∧ k.length < 510 ∧ c.hashOf.length = 32
  branch : ∀ bv cs m, P = .branch bv cs m → UpsSpec.kidsLen cs = 16 ∧
    (∀ sl, bv = some sl → sl.valueRef.length = 36 ∧ sl.len < 2 ^ 32) ∧
    ∀ j c, UpsSpec.kidAt cs j = some c → c.hashOf.length = 32

/-- The kind-specific shape of a part's source. -/
def SrcShape (ci si ti sd ki : Nat) (P : NearSpec.PTrie) : Prop :=
  (ki = 0 → ∃ bv cs m c, P = .branch bv cs m ∧ UpsSpec.kidAt cs (slotOf sd) = some c) ∧
  (ki = 1 → ∃ k c m, P = .ext k c m) ∧
  (ki = 2 → ∃ k sl m, P = .leaf k sl m) ∧
  (ki = 3 → ∃ sl cs m, P = .branch (some sl) cs m) ∧
  (ki = 4 → ∃ cs m, P = .branch none cs m) ∧
  (ki = 5 → ∃ bv cs m, P = .branch bv cs m ∧ UpsSpec.kidAt cs (UpsSpec.yOf si) = none) ∧
  (ki = 6 → ∃ k sl m, P = .leaf k sl m ∧ ti + 1 ≤ k.length) ∧
  (ki = 7 → ∃ k c m, P = .ext k c m ∧ ti + 1 ≤ k.length) ∧
  (ki = 10 → (ci = 4 → ∃ k sl m, P = .leaf k sl m) ∧ (spXN ci = 1 → ∃ k c m, P = .ext k c m)) ∧
  (ki = 11 → ∃ c m, P = .ext [] c m)

/-- **`SrcOk` from the generic facts and the shape.** -/
theorem srcOk_of {ci si ti sd ki : Nat} {P : NearSpec.PTrie} (h : NodeOk3 P) (hs : SrcShape ci si ti sd ki P) :
    SrcOk ci si ti sd ki P := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s10, s11⟩ := hs
  have hm := h.mem
  refine ⟨h.len, fun hk => ?_, fun hk => ?_, s2, fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_,
    fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨bv, cs, m, c, rfl, hc⟩ := s0 hk
    obtain ⟨h16, hsl, hch⟩ := h.branch _ _ _ rfl
    exact ⟨bv, cs, m, c, rfl, fun sl hs => (hsl sl hs).1, hm, h16, hc, hch _ _ hc⟩
  · obtain ⟨k, c, m, rfl⟩ := s1 hk
    exact ⟨k, c, m, rfl, (h.ext _ _ _ rfl).2.2, hm⟩
  · obtain ⟨sl, cs, m, rfl⟩ := s3 hk
    obtain ⟨-, hsl, -⟩ := h.branch _ _ _ rfl
    exact ⟨sl, cs, m, rfl, (hsl sl rfl).1, (hsl sl rfl).2, hm⟩
  · obtain ⟨cs, m, rfl⟩ := s4 hk
    exact ⟨cs, m, rfl, hm⟩
  · obtain ⟨bv, cs, m, rfl, hy⟩ := s5 hk
    obtain ⟨h16, hsl, -⟩ := h.branch _ _ _ rfl
    exact ⟨bv, cs, m, rfl, fun sl hs => (hsl sl hs).1, hm, h16, hy⟩
  · obtain ⟨k, sl, m, rfl, hI⟩ := s6 hk
    obtain ⟨h1, h2, h3, h4⟩ := h.leaf _ _ _ rfl
    exact ⟨k, sl, m, rfl, h1, hI, h2, h3, h4⟩
  · obtain ⟨k, c, m, rfl, hI⟩ := s7 hk
    obtain ⟨h1, h2, h3⟩ := h.ext _ _ _ rfl
    exact ⟨k, c, m, rfl, h1, hI, h2, h3, hm⟩
  · obtain ⟨sL, sE⟩ := s10 hk
    refine ⟨fun h4 => ?_, fun hx => ?_⟩
    · obtain ⟨k, sl, m, rfl⟩ := sL h4
      obtain ⟨-, -, h3, h4⟩ := h.leaf _ _ _ rfl
      exact ⟨k, sl, m, rfl, h3, h4⟩
    · obtain ⟨k, c, m, rfl⟩ := sE hx
      obtain ⟨-, h2, h3⟩ := h.ext _ _ _ rfl
      exact ⟨k, c, m, rfl, h3, hm, h2⟩
  · obtain ⟨c, m, rfl⟩ := s11 hk
    exact ⟨c, m, rfl, (h.ext _ _ _ rfl).2.2, hm⟩

/-! ## Records -/

theorem kidsLen_of (g : Nat → NearSpec.PTrie) : ∀ l : List Kid3, UpsSpec.kidsLen (kidsOf3 g l) = l.length
  | [] => rfl
  | .none :: r => by simp [kidsOf3, UpsSpec.kidsLen, kidsLen_of g r]
  | .hash _ :: r => by simp [kidsOf3, UpsSpec.kidsLen, kidsLen_of g r]
  | .node _ :: r => by simp [kidsOf3, UpsSpec.kidsLen, kidsLen_of g r]

theorem kidAt_of (g : Nat → NearSpec.PTrie) : ∀ (l : List Kid3) (j : Nat) (c : NearSpec.PTrie),
    UpsSpec.kidAt (kidsOf3 g l) j = some c → (∃ h, Kid3.hash h ∈ l ∧ c = .hash h) ∨ ∃ c', Kid3.node c' ∈ l ∧ c = g c'
  | [], _, _, h => by simp [kidsOf3, UpsSpec.kidAt] at h
  | .none :: r, 0, _, h => by simp [kidsOf3, UpsSpec.kidAt] at h
  | .hash h' :: r, 0, c, h => by simp [kidsOf3, UpsSpec.kidAt] at h; exact Or.inl ⟨h', by simp, h.symm⟩
  | .node c' :: r, 0, c, h => by simp [kidsOf3, UpsSpec.kidAt] at h; exact Or.inr ⟨c', by simp, h.symm⟩
  | k :: r, j + 1, c, h => by
    have h' : UpsSpec.kidAt (kidsOf3 g r) j = some c := by cases k <;> simpa [kidsOf3, UpsSpec.kidAt] using h
    rcases kidAt_of g r j c h' with ⟨h1, h2, h3⟩ | ⟨c1, c2, c3⟩
    · exact Or.inl ⟨h1, List.mem_cons_of_mem _ h2, h3⟩
    · exact Or.inr ⟨c1, List.mem_cons_of_mem _ c2, c3⟩

theorem le256_4 {l : List Nat} (hl : l.length = 4) (hb : ∀ x ∈ l, x < 256) : le256 l < 2 ^ 32 := by
  have := Link3.le256_lt l hb; rw [hl] at this; exact this

theorem le256_3 {l : List Nat} (hl : l.length = 4) (hb : ∀ x ∈ l, x < 256) (h3 : l.getD 3 0 = 0) :
    le256 l < 2 ^ 24 := by
  match l, hl with
  | [a, b, c, d], _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h3
    subst h3
    have ha := hb a (by simp); have hb' := hb b (by simp); have hc := hb c (by simp)
    simp only [le256]; omega

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

/-- The value slot of a record, in the post tree. -/
theorem slotOk (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hvb : Link3.VParentBal vs es)
    (H : Link3.ShaHyp vs hds es others shaS shaR) {pv : Nat → NearSpec.Bytes} (HP : Link3.VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {n : Nat} (hn : n < vs.length) {s : NSlot3} (hwf : s.wf) (hb : ∀ x ∈ s.bytes true, x < 256)
    (hval : ∀ lb i l pre po w, s = .val lb i l pre po w → vs[n].v.value = some (i, l, pre, po, w)) :
    (slot3 (Link3.valsPost vs es pv) (s.toV3 (Link3.vpos (Link3.vid0 es)))).valueRef.length = 36 ∧
      (slot3 (Link3.valsPost vs es pv) (s.toV3 (Link3.vpos (Link3.vid0 es)))).len < 2 ^ 32 := by
  cases s with
  | ref lenB h =>
    obtain ⟨h4, h32⟩ := hwf
    simp only [NSlot3.toV3, slot3, NearSpec.Slot.valueRef, NearSpec.Slot.len, List.length_append, u32_length,
      Link3.toB, List.length_map, h32]
    refine ⟨by first | rfl | trivial, le256_4 h4 (fun x hx => hb x (by simp [NSlot3.bytes, hx]))⟩
  | val lenB i l pre po w =>
    obtain ⟨h4, -, -, -, h3, hle⟩ := hwf
    have hlb : ∀ x ∈ lenB, x < 256 := fun x hx => hb x (by simp [NSlot3.bytes, hx])
    have hv := hval lenB i l pre po w rfl
    obtain ⟨hL, -⟩ := Link3.val_post_sha hN hhw hvw hvb H HP hpl hn hv
    simp only [NSlot3.toV3, slot3, NearSpec.Slot.valueRef, NearSpec.Slot.len, List.length_append, u32_length,
      sha256_len]
    refine ⟨by first | rfl | trivial, ?_⟩
    rw [hL, ← hle hlb]
    have := le256_3 h4 hlb h3
    omega

theorem revealed_branch {sv : Option NSlot3} {kids : List NKid} {mb : List Nat} {c l r : Nat} {pre po : List Nat}
    (h : NKid.node c l r pre po ∈ kids) : (c, l, r, pre, po) ∈ (NodeV3.branch sv kids mb).revealed := by
  simp only [NodeV3.revealed, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

/-- **Every record's post subtrie has the generic facts.** -/
theorem post_nodeOk (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hb : Link3.ParentBal vs hds)
    (hvb : Link3.VParentBal vs es) (H : Link3.ShaHyp vs hds es others shaS shaR) {pv : Nat → NearSpec.Bytes}
    (HP : Link3.VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {n : Nat} (hn : n < vs.length) :
    NodeOk3 (fullTree (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) n) := by
  obtain ⟨he, hnode, hm⟩ := Link3.post_node hN hhw hvw hb hvb H HP hpl hn
  have hB := Link3.rec_bytes_post hN hhw hvw hb H _ (List.getElem_mem hn)
  have hwf := hN.wf _ (List.getElem_mem hn)
  have hlen : (nodeEnc (fullTree (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) n)).length
      < 2 ^ 22 := by
    rw [he, Link3.toB, List.length_map]; exact Link3.post_len_lt hN hn
  obtain ⟨h, hh, ht⟩ := Link3.head_of hN hhw hb n hn
  have hd := Link3.rootedDag3 hN hhw hvw hb hvb (Link3.vlen_le hvw) (Link3.rec_bytes hN hhw hvw hb H) hh
  have hu := Link3.fullTree_unfold_any hd (Link3.valsPost vs es pv) (Link3.recsOf_get _ _ hn) (by simp only; rw [ht])
  have hkid : ∀ c l r pre po, (c, l, r, pre, po) ∈ vs[n].v.revealed →
      (fullTree (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) c).hashOf.length = 32 := by
    intro c l r pre po hk
    obtain ⟨hc, -, -⟩ := Link3.kid_post_sha hN hvw hb H hn hk
    obtain ⟨-, hnode', -⟩ := Link3.post_node hN hhw hvw hb hvb H HP hpl hc
    rw [hashOf_eq_enc _ hnode', sha256_len]
  have hslot := fun (s : NSlot3) (hs : s.wf) (hsb : ∀ x ∈ s.bytes true, x < 256)
    (hval : ∀ lb i l pre po w, s = .val lb i l pre po w → vs[n].v.value = some (i, l, pre, po, w)) =>
    slotOk hN hhw hvw hvb H HP hpl hn hs hsb hval
  rw [hu] at hlen hm ⊢
  generalize hv : vs[n].v = vv at hu hwf hB hkid hslot hlen hm
  cases vv with
  | leaf k sl memB =>
    obtain ⟨hk16, hsw, -⟩ := hwf
    refine ⟨hlen, hm, fun k' sl' m he' => ?_, fun _ _ _ he' => by simp [NodeV3.toRec3, nodeTree3] at he',
      fun _ _ _ he' => by simp [NodeV3.toRec3, nodeTree3] at he'⟩
    simp only [NodeV3.toRec3, nodeTree3, NearSpec.PTrie.leaf.injEq] at he'
    obtain ⟨rfl, rfl, -⟩ := he'
    have hhp := hB (hpN k true).length (by simp [NodeV3.ser, u32r])
    simp only [hpN, List.length_map, UpsSpec.hp_len] at hhp
    have hS := hslot sl hsw (fun x hx => hB x (by simp [NodeV3.ser, hx]))
      (fun lb i l pre po w e => by rw [e]; rfl)
    exact ⟨hk16, by omega, hS.1, hS.2⟩
  | ext k kid memB =>
    obtain ⟨hk16, hkn, hkw, -⟩ := hwf
    refine ⟨hlen, hm, fun _ _ _ he' => by simp [NodeV3.toRec3, nodeTree3] at he', fun k' c m he' => ?_,
      fun _ _ _ he' => by simp [NodeV3.toRec3, nodeTree3] at he'⟩
    simp only [NodeV3.toRec3, nodeTree3, NearSpec.PTrie.ext.injEq] at he'
    obtain ⟨rfl, rfl, -⟩ := he'
    have hhp := hB (hpN k false).length (by simp [NodeV3.ser, u32r])
    simp only [hpN, List.length_map, UpsSpec.hp_len] at hhp
    refine ⟨hk16, by omega, ?_⟩
    cases kid with
    | none => exact absurd rfl hkn
    | hash h0 =>
      simp only [NKid.toKid3, kidTree3, NearSpec.PTrie.hashOf, Link3.toB, List.length_map]; exact hkw
    | node c l r pre po =>
      simp only [NKid.toKid3, kidTree3]
      exact hkid c l r pre po (by simp [NodeV3.revealed])
  | branch sv kids memB =>
    obtain ⟨h16, hsv, hkw, -⟩ := hwf
    refine ⟨hlen, hm, fun _ _ _ he' => by simp [NodeV3.toRec3, nodeTree3] at he',
      fun _ _ _ he' => by simp [NodeV3.toRec3, nodeTree3] at he', fun bv cs m he' => ?_⟩
    simp only [NodeV3.toRec3, nodeTree3, NearSpec.PTrie.branch.injEq] at he'
    obtain ⟨rfl, rfl, -⟩ := he'
    refine ⟨by rw [kidsLen_of, List.length_map, h16], fun sl hsl => ?_, fun j c hc => ?_⟩
    · cases sv with
      | none => simp at hsl
      | some s0 =>
        simp only [Option.map_some, Option.some.injEq] at hsl
        subst hsl
        exact hslot s0 (hsv s0 rfl) (fun x hx => hB x (by simp [NodeV3.ser, hx]))
          (fun lb i l pre po w e => by rw [e]; rfl)
    · rcases kidAt_of _ _ j c hc with ⟨h0, hm0, rfl⟩ | ⟨c', hm0, rfl⟩
      · obtain ⟨kd, hkd, he0⟩ := List.mem_map.1 hm0
        cases kd with
        | none => simp [NKid.toKid3] at he0
        | node => simp [NKid.toKid3] at he0
        | hash h1 =>
          simp only [NKid.toKid3, Kid3.hash.injEq] at he0
          subst he0
          simp only [NearSpec.PTrie.hashOf, Link3.toB, List.length_map]
          exact hkw _ hkd
      · obtain ⟨kd, hkd, he0⟩ := List.mem_map.1 hm0
        cases kd with
        | none => simp [NKid.toKid3] at he0
        | hash => simp [NKid.toKid3] at he0
        | node c0 l r pre po =>
          simp only [NKid.toKid3, Kid3.node.injEq] at he0
          subst he0
          exact hkid c0 l r pre po (revealed_branch hkd)

/-- **`UpsExt0.srcOk`** from the shapes: every part's source has `SrcOk`, given its kind's shape. -/
theorem ups_srcOk (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hb : Link3.ParentBal vs hds)
    (hvb : Link3.VParentBal vs es) (H : Link3.ShaHyp vs hds es others shaS shaR) {pv : Nat → NearSpec.Bytes}
    (HP : Link3.VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {v : List UpsSeg} (hw : UpsWf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    (hshape : ∀ k, k < ps.length → SrcShape ci si ti (sdx k) (kd k)
      (srcOf (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) s ps k)) :
    ∀ k, k < ps.length → SrcOk ci si ti (sdx k) (kd k)
      (srcOf (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) s ps k) := by
  intro k hk
  have hn := part_sN hN hw hbal hs hL hP k hk
  have hg : ps.getD k (0, 0) = ps[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  refine srcOk_of ?_ (hshape k hk)
  simp only [srcOf, hg]
  exact post_nodeOk hN hhw hvw hb hvb H HP hpl hn

end

end ZkFormal.NearV3.UpsRows
