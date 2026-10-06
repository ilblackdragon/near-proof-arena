import ZkFormal.NearV3.Extract.Ups.UpsReads

/-!
# ZkFormal.NearV3.Extract.Ups.UpsSrc — the source nodes of the parts (M7e, step 1)

The source of part `k` is the post subtrie of the record it reads,
`srcOf R V' s ps k = fullTree R V' (sN of part k)` with `R = recsOf (vpos (vid0 es)) vs` and the post
value records `V' = valsPost vs es pv`.

* **`post_node`** (any record `n`): `nodeEnc (fullTree R V' n) = toB (ser true)`, the subtrie is a node, its
  `memory_usage` is `< 2^64` and its encoding has the record's length (`head_of` gives the record's
  instance head, then `enc_fullTree_post` and `fullTree_unfold_any`);
* **`part_sN`**: every part reads a record `sN < |vs|` (the new leaf shares its parent part's `sN`);
* **`ups_srcEnc`**: `UpsExt0.srcEnc` with `Pb = postB vs`, `src = srcOf R V' s ps`, and "sources are nodes
  with usage `< 2^64`" (`ups_partsG`'s `hsrcM`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

/-- The `MEM` bytes of a record are bytes of its post serialization. -/
theorem memD_tree {f : Nat → Nat} (V' : List ValRec3) (g : Nat → PTrie) {v : NodeV3} (hwf : v.wf)
    (hb : ∀ x ∈ v.ser true, x < 256) : (nodeTree3 V' g (v.toRec3 f)).memD < 2 ^ 64 := by
  have key : ∀ memB : List Nat, memB.length = 8 → (∀ x ∈ memB, x < 256) → le256 memB < 2 ^ 64 := by
    intro memB hl hx
    have := le256_lt memB hx
    rw [hl] at this; exact this
  cases v with
  | leaf k sl memB =>
    simp only [NodeV3.toRec3, nodeTree3, PTrie.memD, PTrie.mem?, Option.getD_some]
    exact key memB hwf.2.2 (fun x hx => hb x (by simp [NodeV3.ser, hx]))
  | ext k kid memB =>
    simp only [NodeV3.toRec3, nodeTree3, PTrie.memD, PTrie.mem?, Option.getD_some]
    exact key memB hwf.2.2.2 (fun x hx => hb x (by simp [NodeV3.ser, hx]))
  | branch sv kids memB =>
    simp only [NodeV3.toRec3, nodeTree3, PTrie.memD, PTrie.mem?, Option.getD_some]
    exact key memB hwf.2.2.2 (fun x hx => hb x (by cases sv <;> simp [NodeV3.ser, hx]))

/-- **Every record's post subtrie**: its encoding is the record's post bytes, it is a node, its usage is
`< 2^64`. -/
theorem post_node (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR) {pv : Nat → Bytes}
    (HP : VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {n : Nat} (hn : n < vs.length) :
    nodeEnc (fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) n) = toB (vs[n].v.ser true) ∧
      isNode (fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) n) = true ∧
      (fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) n).memD < 2 ^ 64 := by
  obtain ⟨h, hh, ht⟩ := head_of hw hhw hb n hn
  have hbytes := rec_bytes hw hhw hvw hb H
  have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
  have hI : InInst (recsOf (vpos (vid0 es)) vs) h.tau n := ⟨_, recsOf_get _ _ hn, by simp only; rw [ht]⟩
  obtain ⟨_, henc, hnode⟩ := enc_fullTree_post hd hw (rec_bytes_post hw hhw hvw hb H)
    (fun p hp c l r pre po hk => by
      obtain ⟨hc, -, he⟩ := kid_post_sha hw hvw hb H hp hk; exact ⟨hc, he⟩)
    (fun p hp i l pre po w hv => val_post_sha hw hhw hvw hvb H HP hpl hp hv) n hI
  refine ⟨henc, hnode, ?_⟩
  rw [fullTree_unfold_any hd _ (recsOf_get _ _ hn) (by simp only; rw [ht])]
  exact memD_tree _ _ (hw.wf _ (List.getElem_mem hn)) (rec_bytes_post hw hhw hvw hb H _ (List.getElem_mem hn))

end ZkFormal.NearV3.Link3

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The source node of part `k`: the post subtrie of the record it reads. -/
def srcOf (R : List NodeRec3) (V' : List ValRec3) (s : UpsSeg) (ps : List (Nat × Nat))
    (k : Nat) : NearSpec.PTrie :=
  fullTree R V' (s.row (ps.getD k (0, 0)).1 sN)

/-- The new leaf is never the topmost terminal part, and the part above it is not a new leaf. -/
theorem nlfNotTop : ∀ ci, ci < 11 → ∀ ti, ti < 3 → ∀ k, k < 4 →
    (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB = .NLF →
    k + 1 < nTof ci ti ∧ ¬ ((termPlan (UCase.all.getD ci .LP) ti).getD (k + 1) .RDB = .NLF) := by decide

theorem kd8 : UKind.all.getD 8 .RDB = .NLF := rfl

attribute [local irreducible] UpsSeg.row UpsSeg.next

/-- **Every part reads a record**: its `sN` is a record of `nodeV3`. -/
theorem part_sN {vs : List NodeS3} {v : List UpsSeg} (hN : NodeWf3 vs) (hw : UpsWf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    (k : Nat) (hk : k < ps.length) : s.row ps[k].1 sN < vs.length := by
  have viaRead : ∀ c (hc : c < ps.length), kd c ≠ 8 → s.row ps[c].1 sN < vs.length := by
    intro c hc h8
    obtain ⟨hlt, hrd, hsN, -⟩ := memRead hw hs hL hP c hc h8
    obtain ⟨hn, -⟩ := upb_read hN hw hbal hs hlt hrd
    rwa [hsN] at hn
  by_cases h8 : kd k = 8
  · have i1 := hP.ix.1; have i2 := hP.ix.2.1
    have hT : k < nTof ci ti := by
      apply Classical.byContradiction; intro hc
      have := (hP.upper k hk (by omega)).1; omega
    have hk4 : k < 4 := by have := nTof_le ci i1 ti i2; omega
    obtain ⟨hTk, -, -, -, -, hsd, -⟩ := hP.term k hk hT
    rw [h8, kd8] at hTk
    obtain ⟨hk1, hne⟩ := nlfNotTop ci i1 ti i2 k hk4 hTk.symm
    have hk1' : k + 1 < ps.length := by have := hP.len; omega
    obtain ⟨hTk1, hlo, hhi, -, -, hsd1, -⟩ := hP.term (k + 1) hk1' hk1
    have h81 : kd (k + 1) ≠ 8 := fun h => hne (by rw [← hTk1, h, kd8])
    have e1 := (hP.src k hk (by omega)).1
    have e2 := (hP.src (k + 1) hk1' (by omega)).1
    rw [e1, hsd, ← hsd1, ← e2]
    exact viaRead (k + 1) hk1' h81
  · exact viaRead k hk h8

/-- **`UpsExt0.srcEnc`** and "sources are nodes with usage `< 2^64`", with `Pb = postB vs` and
`src = srcOf R V' s ps`. -/
theorem ups_srcEnc {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat} {v : List UpsSeg}
    (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hb : Link3.ParentBal vs hds)
    (hvb : Link3.VParentBal vs es) (H : Link3.ShaHyp vs hds es others shaS shaR) {pv : Nat → NearSpec.Bytes}
    (HP : Link3.VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    (hw : UpsWf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    (k : Nat) (hk : k < ps.length) :
    postB vs (s.row ps[k].1 sN) =
        (nodeEnc (srcOf (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) s ps k)).map
          UInt8.toNat ∧
      isNode (srcOf (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) s ps k) = true ∧
      (srcOf (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) s ps k).memD < 2 ^ 64 := by
  have hn := part_sN hN hw hbal hs hL hP k hk
  have hg : ps.getD k (0, 0) = ps[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  obtain ⟨he, hnode, hm⟩ := Link3.post_node hN hhw hvw hb hvb H HP hpl hn
  simp only [srcOf, hg]
  refine ⟨?_, hnode, hm⟩
  have hvg : vs.getD (s.row ps[k].1 sN) default = vs[s.row ps[k].1 sN] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
  rw [he, postB, hvg]
  have hB := Link3.rec_bytes_post hN hhw hvw hb H _ (List.getElem_mem hn)
  unfold Link3.toB
  rw [List.map_map]
  conv => lhs; rw [← List.map_id (vs[s.row ps[k].1 sN].v.ser true)]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp, id, UInt8.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (hB x hx)).symm

end ZkFormal.NearV3.UpsRows
