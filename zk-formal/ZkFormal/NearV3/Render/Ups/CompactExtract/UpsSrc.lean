import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsReads
import ZkFormal.NearV3.Extract.Ups.UpsSrc
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
attribute [local irreducible] UpsSeg.row UpsSeg.next
theorem part_sN {vs : List NodeS3} {v : List UpsSeg} (hN : NodeWf3 vs) (hw : Wf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
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
    (hw : Wf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
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

end ZkFormal.NearV3.Render.UpsRelay.Extract
