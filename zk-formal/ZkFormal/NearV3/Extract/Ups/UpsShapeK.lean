import ZkFormal.NearV3.Extract.Ups.UpsTag

/-!
# ZkFormal.NearV3.Extract.Ups.UpsShapeK — every part's source has its kind's shape (M7e, step 1)

**`ups_shape`**: under `UpsEnv`, every part `k` of every segment has `SrcShape … (srcOf R V' s ps k)`, the last
open field of `UpsExt0`.  The source is record `N = sN` of the part, and `srcOf … k = nodeTree3 V' … (N's Rec3)`
(`post_eq`), so the shape is the record's:

* **constructor from the copied tag** (`tagCopy`): `RDB` (branch), `RDE` (extension), `RLP` (leaf), `RBR`
  (branch with a value), `PT` (extension; its copied `hplen = 1` and flag byte `0` give the empty key, `ptHead`);
* **from the walk** (`ups_walkHyp`): `RDB`'s slot `slotOf d` holds a revealed child (`ups_downSlot`: the step of
  level `d` is a `DOWN` edge of the branch); `RBV` (case `BV`, `t* = W3`: `bvSi`) is the `BMAP` record with
  `hasVal = 0`, a branch without value; `RBI` (case `BI`, `t* ∈ {W1, W2}`) is the `BMAP` record with bit `y`
  clear, so slot `y` is empty (`ups_termBmap`); `LSa`'s split branch reads the `LEND` edge's record, a leaf;
* **leaf vs extension** for `MVL`, `MVE` and `ESx1`'s split branch: the terminal `KEY` edge at `I` belongs to a
  leaf or an extension with `I < |k|` (`ups_termEdge`, `edge_key`), and the source's byte 5 read on the part's
  `TAG` row has high nibble `2·qtl + podd` (`tagNib5`): `≥ 2` for `MVL` (a leaf's flag byte), `≤ 1` for the
  others (an extension's).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Plan facts -/

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem kindCase : ∀ c, c < 11 → ∀ t, t < 3 → ∀ k, k < 4 → k < nTof c t →
    ((termPlan (UCase.all.getD c .LP) t).getD k .RDB = .RBV → c = 2) ∧
    ((termPlan (UCase.all.getD c .LP) t).getD k .RDB = .MVL → c = 5 ∨ c = 6) ∧
    ((termPlan (UCase.all.getD c .LP) t).getD k .RDB = .MVE → c = 7 ∨ c = 9) := by decide

theorem rdCount_add (kd : Nat → Nat) : ∀ j a m, rdCount kd j (a + m) = rdCount kd j a + rdCount kd (j + a) m
  | j, 0, m => by simp [rdCount]
  | j, a + 1, m => by
    rw [show a + 1 + m = (a + m) + 1 by omega]
    simp only [rdCount]
    rw [rdCount_add kd (j + 1) a m, show j + 1 + a = j + (a + 1) by omega]
    omega

theorem tag_cases (rv : NodeV3) :
    (tagOf rv = 0 → ∃ k sl m, rv = .leaf k sl m) ∧ (tagOf rv = 3 → ∃ k kid m, rv = .ext k kid m) ∧
    ((tagOf rv = 1 ∨ tagOf rv = 2) → ∃ sv kids m, rv = .branch sv kids m) ∧
    (tagOf rv = 2 → ∃ sl kids m, rv = .branch (some sl) kids m) := by
  cases rv with
  | leaf k sl m => simp [tagOf]
  | ext k kid m => simp [tagOf]
  | branch sv kids m => cases sv <;> simp [tagOf]

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- The terminal row of `LP BR BV LSb ESl0 ESl1` is `W3` (`sf·(ts1 + ts2)·(…) = 0`). -/
theorem w3Si (hc : ci = 0 ∨ ci = 1 ∨ ci = 2 ∨ ci = 5 ∨ ci = 7 ∨ ci = 8) : si = 2 := by
  obtain ⟨h4r, hsf, -⟩ := hL.walk
  obtain ⟨sc, -, -, sts⟩ := hP.seg 0 (by omega)
  have ok := okRow hw hs (i := 0) (by omega)
  have f := factN ok (rowLt hw hs _) (nextLt hw hs _)
    (e := mul3 (c sf) (.add (c ts1) (c ts2)) (sumc [cLP, cBR, cBV, cLSb, cESl0, cESl1])) (memSeg (by simp [cSeg]))
  have c0 : s.row 0 cLP = if 0 = ci then 1 else 0 := sc 0 (by omega)
  have c1 : s.row 0 cBR = if 1 = ci then 1 else 0 := sc 1 (by omega)
  have c2 : s.row 0 cBV = if 2 = ci then 1 else 0 := sc 2 (by omega)
  have c5 : s.row 0 cLSb = if 5 = ci then 1 else 0 := sc 5 (by omega)
  have c7 : s.row 0 cESl0 = if 7 = ci then 1 else 0 := sc 7 (by omega)
  have c8 : s.row 0 cESl1 = if 8 = ci then 1 else 0 := sc 8 (by omega)
  have s1 : s.row 0 ts1 = if 0 = si then 1 else 0 := sts 0 (by omega)
  have s2 : s.row 0 ts2 = if 1 = si then 1 else 0 := sts 1 (by omega)
  simp only [sumc, List.map_cons, List.map_nil] at f
  nev_simp at f
  simp only [hsf, c0, c1, c2, c5, c7, c8, s1, s2] at f
  have := hP.ix.2.2.2
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;> simp at f <;> rfl

/-- A descend reads a level above the terminal: `sdx k < D`. -/
theorem descLt (k : Nat) (hk : k < ps.length) (hkd : kd k ≤ 1) : sdx k < di := by
  have h1 := hP.desc k hk hkd
  have h2 := hP.rcnt k hk
  have h3 := hP.ndesc
  have := rdCount_add kd 0 k (ps.length - k)
  rw [show k + (ps.length - k) = ps.length by omega, Nat.zero_add] at this
  omega

/-- The kind's case, for the terminal kinds `RBV MVL MVE`. -/
theorem kindCaseK (k : Nat) (hk : k < ps.length) :
    (kd k = 4 → ci = 2) ∧ (kd k = 6 → ci = 5 ∨ ci = 6) ∧ (kd k = 7 → ci = 7 ∨ ci = 9) := by
  obtain ⟨i1, i2, -, -⟩ := hP.ix
  have hkT : 1 < kd k → kd k < 11 → k < nTof ci ti := by
    intro a b
    rcases Nat.lt_or_ge k (nTof ci ti) with h | h
    · exact h
    · have := (hP.upper k hk h).1; omega
  have h4 : ∀ (_ : k < nTof ci ti), k < 4 := fun h => by have := nTof_le ci i1 ti i2; omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have hT := hkT (by omega) (by omega) <;>
    have hp := (hP.term k hk hT).1 <;> rw [h] at hp <;>
    have C := kindCase ci i1 ti i2 k (h4 hT) hT
  · exact C.1 hp.symm
  · exact C.2.1 hp.symm
  · exact C.2.2 hp.symm

end

/-! ## The shapes -/

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws)
  {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

set_option maxHeartbeats 4000000 in
/-- **Every part's source has its kind's shape** (`UpsExt0.srcOk` via `ups_srcOk`). -/
theorem ups_shape :
    ∀ k, k < ps.length → SrcShape ci si ti (sdx k) (kd k) (srcOf (Rpost vs es) (Vpost vs es pv) s ps k) := by
  intro k hk
  have hN := E.node
  have G := E.walk
  have hw := E.ups
  have hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (postB vs (s.row i sN)).getD (s.row i spos) 0 :=
    fun i hi hrd => (upb_reads hN hw E.upb hs i hi hrd).1
  have hn := part_sN hN hw E.upb hs hL hP k hk
  have hg : ps.getD k (0, 0) = ps[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  have hsrc : srcOf (Rpost vs es) (Vpost vs es pv) s ps k = nodeTree3 (Vpost vs es pv)
      (fullTree (Rpost vs es) (Vpost vs es pv)) (vs[s.row ps[k].1 sN].v.toRec3 (Link3.vpos (Link3.vid0 es))) := by
    simp only [srcOf, hg]; exact post_eq hN E.head E.val E.par E.vpar E.sha _ hn
  have hPb : postB vs (s.row ps[k].1 sN) = vs[s.row ps[k].1 sN].v.ser true := by
    simp only [postB]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
  have hget : vs[s.row ps[k].1 sN]? = some vs[s.row ps[k].1 sN] := List.getElem?_eq_getElem hn
  have hwf := hN.wf _ (List.getElem_mem hn)
  -- the part's first row
  have K := partK hw hs hL hP k hk
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  obtain ⟨hlt0, hq0, hpf⟩ := pFirst hw hs hL k hk
  have ok0 := okRow hw hs hlt0
  obtain ⟨b1, b2, b3, b4, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) hpf hq0
  have hkl : kd k < 12 := (hP.part k hk).1
  have hT := fun (h : kd k = 0 ∨ kd k = 1 ∨ kd k = 2 ∨ kd k = 3 ∨ kd k = 11) => by
    have := tagCopy hw hs hL hP (postB vs) hR k hk h
    rw [hPb, ser_tag] at this
    exact this
  -- the terminal record
  have hterm : 1 < kd k → kd k < 11 → s.row ps[k].1 sN = s.row 0 (11 + di) := by
    intro a b
    have hkT : k < nTof ci ti := by
      rcases Nat.lt_or_ge k (nTof ci ti) with h | h
      · exact h
      · have := (hP.upper k hk h).1; omega
    obtain ⟨-, -, -, -, -, hsd, -⟩ := hP.term k hk hkT
    rw [(hP.src k hk (by omega)).1, hsd]
  have recOf : ∀ r, vs[s.row 0 (11 + di)]? = some r → 1 < kd k → kd k < 11 → r = vs[s.row ps[k].1 sN] := by
    intro r hr a b
    rw [← hterm a b, hget] at hr
    exact (Option.some.inj hr).symm
  -- leaf vs extension from the terminal `KEY` edge and byte 5
  have keyRec : 4 ≤ ci → ci ≠ 4 → 1 < kd k → kd k < 11 →
      ((∃ key sl m, vs[s.row ps[k].1 sN].v = .leaf key sl m ∧ ti < key.length) ∨
        (∃ key kid m, vs[s.row ps[k].1 sN].v = .ext key kid m ∧ ti < key.length)) := by
    intro h4 hne a b
    obtain ⟨r, hr, -, hK⟩ := ups_termEdge G hw hs hL hP h4
    obtain ⟨e, he, hek, hI⟩ := hK hne
    rw [recOf r hr a b] at he
    rw [← hI]; exact edge_key he hek
  have nib5 := fun (h : kd k = 6 ∨ kd k = 7 ∨ (kd k = 10 ∧ spXN ci = 1)) => by
    have := tagNib5 hw hs hL hP (postB vs) hR k hk h
    rw [hPb] at this
    exact this
  have leafOrExt : 4 ≤ ci → ci ≠ 4 → 1 < kd k → kd k < 11 → (kd k = 6 ∨ kd k = 7 ∨ (kd k = 10 ∧ spXN ci = 1)) →
      (kd k = 6 → ∃ key sl m, vs[s.row ps[k].1 sN].v = .leaf key sl m ∧ ti < key.length) ∧
      (kd k ≠ 6 → ∃ key kid m, vs[s.row ps[k].1 sN].v = .ext key kid m ∧ ti < key.length) := by
    intro h4 hne a b hk67
    obtain ⟨n5, hpo, hq6, hq7⟩ := nib5 hk67
    rcases keyRec h4 hne a b with ⟨key, sl, m, hv, hI⟩ | ⟨key, kid, m, hv, hI⟩
    · rw [hv] at hwf n5
      rw [ser5_leaf key sl m hwf.1] at n5
      refine ⟨fun _ => ⟨key, sl, m, hv, hI⟩, fun h6 => ?_⟩
      have := hq7 h6; omega
    · rw [hv] at hwf n5
      rw [ser5_ext key kid m hwf.1] at n5
      refine ⟨fun h6 => ?_, fun _ => ⟨key, kid, m, hv, hI⟩⟩
      have := hq6 h6; have := Nat.mod_lt key.length (show 0 < 2 by omega); omega
  generalize hrv : vs[s.row ps[k].1 sN].v = rv at hsrc hwf hT keyRec leafOrExt
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ⟨fun h4 => ?_, fun hx => ?_⟩, fun h => ?_⟩
  · -- `RDB`: a branch (tag), its descend slot holds a child (walk)
    obtain ⟨-, -, htl, hte, -⟩ := head_RDB ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (fun m hm => by rw [I0.kd m hm, h])
    have ht := hT (Or.inl h)
    obtain ⟨sv', kids, m, rfl⟩ := (tag_cases rv).2.2.1 (by omega)
    obtain ⟨r, hr, hslot⟩ := ups_downSlot G hw hs hL hP (sdx k) (descLt hw hs hL hP k hk (by omega))
    rw [← (hP.src k hk (by omega)).1, hget] at hr
    have hr' := Option.some.inj hr
    obtain ⟨c, l, rr, pre, po, hkid⟩ := hslot sv' kids m (by rw [← hr', hrv])
    rw [hsrc]
    simp only [NodeV3.toRec3, nodeTree3]
    exact ⟨_, _, _, _, rfl, kidAt_node _ kids _ hkid⟩
  · -- `RDE`: an extension (tag)
    have hte := (head_RDE ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (fun m hm => by rw [I0.kd m hm, h])).2.2.1
    obtain ⟨key, kid, m, rfl⟩ := (tag_cases rv).2.1 (by have := hT (Or.inr (Or.inl h)); omega)
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]; exact ⟨_, _, _, rfl⟩
  · -- `RLP`: a leaf (tag)
    have htl := (head_RLP ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (fun m hm => by rw [I0.kd m hm, h])).2.2.1
    obtain ⟨key, sl, m, rfl⟩ := (tag_cases rv).1 (by have := hT (Or.inr (Or.inr (Or.inl h))); omega)
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]; exact ⟨_, _, _, rfl⟩
  · -- `RBR`: a branch with a value (tag)
    obtain ⟨-, -, htl, hte, htb2, -⟩ := head_RBR ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (fun m hm => by rw [I0.kd m hm, h])
    obtain ⟨sl, kids, m, rfl⟩ := (tag_cases rv).2.2.2 (by have := hT (Or.inr (Or.inr (Or.inr (Or.inl h)))); omega)
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3, Option.map_some]; exact ⟨_, _, _, rfl⟩
  · -- `RBV`: the `BMAP` record of `W3`, without a value
    have hci := (kindCaseK hw hs hL hP k hk).1 h
    have hsi := w3Si hw hs hL hP (by omega)
    obtain ⟨r, hr, bm, hv, hbm, hv0, -⟩ := ups_termBmap G hw hs hL hP (Or.inl hci)
    rw [recOf r hr (by omega) (by omega), hrv] at hbm
    have hv0 := hv0 hsi
    subst hv0
    cases rv with
    | branch sv' kids m =>
      simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hbm
      cases sv' with
      | none => rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3, Option.map_none]; exact ⟨_, _, rfl⟩
      | some _ => simp at hbm
    | leaf => simp [NodeV3.bmap] at hbm
    | ext => simp [NodeV3.bmap] at hbm
  · -- `RBI`: the `BMAP` record of `W1`/`W2`, slot `y` empty
    have hci := (termCase hw hs hL hP k hk (Or.inl h)).1 h
    have hsi := rbiSi hw hs hL hP k hk h
    obtain ⟨r, hr, bm, hv, hbm, -, hbit⟩ := ups_termBmap G hw hs hL hP (Or.inr hci)
    rw [recOf r hr (by omega) (by omega), hrv] at hbm
    have hbit := hbit (by omega)
    cases rv with
    | branch sv' kids m =>
      simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hbm
      obtain ⟨rfl, -⟩ := hbm
      have h16 : kids.length = 16 := hwf.1
      have hy : UpsSpec.yOf si < 16 := by
        rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> decide
      have hb := Render.NodeGen3.bitOf_kidBitmap kids (UpsSpec.yOf si)
      unfold Near.Render.NodeGen.bitOf at hb
      rw [hbit] at hb
      have hkn := Walk3.kbit_zero hb.symm
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hkn
      simp only [Option.getD_some] at hkn
      rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]
      exact ⟨_, _, _, rfl, kidAt_none _ kids _ (by rw [List.getElem?_eq_getElem (by omega), hkn])⟩
    | leaf => simp [NodeV3.bmap] at hbm
    | ext => simp [NodeV3.bmap] at hbm
  · -- `MVL`: the terminal `KEY` edge's record, a leaf (byte 5)
    have hci := (kindCaseK hw hs hL hP k hk).2.1 h
    obtain ⟨key, sl, m, hv, hI⟩ := (leafOrExt (by omega) (by omega) (by omega) (by omega) (Or.inl h)).1 h
    subst hv
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]; exact ⟨_, _, _, rfl, by omega⟩
  · -- `MVE`: the terminal `KEY` edge's record, an extension (byte 5)
    have hci := (kindCaseK hw hs hL hP k hk).2.2 h
    obtain ⟨key, kid, m, hv, hI⟩ := (leafOrExt (by omega) (by omega) (by omega) (by omega) (Or.inr (Or.inl h))).2
      (by omega)
    subst hv
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]; exact ⟨_, _, _, rfl, by omega⟩
  · -- `SPB`, `LSa`: the `LEND` edge's record, a leaf
    obtain ⟨r, hr, hLe, -⟩ := ups_termEdge G hw hs hL hP (by omega)
    obtain ⟨e, he, hek⟩ := hLe h4
    rw [recOf r hr (by omega) (by omega)] at he
    obtain ⟨key, sl, m, hv⟩ := edge_lend he hek
    rw [hrv] at hv
    subst hv
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]; exact ⟨_, _, _, rfl⟩
  · -- `SPB`, `ESl1`/`ESn1`: the `KEY` edge's record, an extension (byte 5)
    have hc : ci = 8 ∨ ci = 10 := by unfold spXN at hx; split at hx <;> omega
    obtain ⟨key, kid, m, hv, -⟩ := (leafOrExt (by omega) (by omega) (by omega) (by omega)
      (Or.inr (Or.inr ⟨h, hx⟩))).2 (by omega)
    subst hv
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]; exact ⟨_, _, _, rfl⟩
  · -- `PT`: an extension (tag) with the empty key (copied `hplen` and flag byte)
    have hte := (head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (fun m hm => by rw [I0.kd m hm, h])).2.2.1
    obtain ⟨key, kid, m, rfl⟩ := (tag_cases rv).2.1 (by have := hT (Or.inr (Or.inr (Or.inr (Or.inr h)))); omega)
    obtain ⟨p1, p5⟩ := ptHead hw hs hL hP (postB vs) hR k hk h
    rw [hPb, hrv] at p1 p5
    have hlen := Link3.post_len_lt hN hn
    rw [hrv] at hlen
    have hk0 := ext_nil_of key kid m hwf.1 hlen p1 p5
    subst hk0
    rw [hsrc]; simp only [NodeV3.toRec3, nodeTree3]; exact ⟨_, _, rfl⟩

/-- **`UpsExt0` of a segment** without the shape hypothesis: only `vbytes` remains. -/
theorem ups_ext0S (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256) :
    UpsExt0 s ps ci ti si kd sdx (postB vs) (srcOf (Rpost vs es) (Vpost vs es pv) s ps) (sv (s.row 0 tau)) :=
  ups_ext0 E hs hL hP hvb (ups_shape E hs hL hP)

/-- **The parts of a segment** without the shape hypothesis: only `vbytes` remains. -/
theorem ups_partsAllS (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256) :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx
        (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k).memD) :=
  ups_partsAll E hs hL hP hvb (ups_shape E hs hL hP)

end

end ZkFormal.NearV3.UpsRows
