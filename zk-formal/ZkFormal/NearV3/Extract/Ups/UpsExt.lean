import ZkFormal.NearV3.Extract.Ups.UpsShape

/-!
# ZkFormal.NearV3.Extract.Ups.UpsExt — `UpsExt0` from the other tables (M7e, step 1 assembled)

**`ups_ext0`**: for every segment, `UpsExt0` holds with `Pb = postB vs` (the records' post bytes),
`src = srcOf R V' s ps` (the post subtries of the records read) and the scheduler's value `sv τ`, from
* the `nodeV3` / heads / values views and their link hypotheses (`post_tau`'s);
* the `UPB` balance (`reads`, `srcEnc`), the scheduler interface `SchedVal` (`vlen`, `digV`), the `upsV3`
  `BYTES` / `DIGEST` facts (`digV`), the walk hypotheses of all walks (`tiLe`);
* two residual hypotheses: the parts' **shapes** (`SrcShape`, from the walk and the case: open) and
  **`vbytes`** (the `W0` length limbs are bytes: not constrained by the table, STATUS §6).

**`ups_partsAll`**: then every part of every segment emits `nodeEnc (upsQ … k)` with exact `MEMD` limbs.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The facts about the other tables that the parts of every segment need. -/
structure UpsEnv (vs : List NodeS3) (hds : List HeadE) (es : List ValE) (others : List Msg)
    (shaS shaR : Nat → List Fp → Nat) (pv : Nat → NearSpec.Bytes) (v : List UpsSeg) (sv : Nat → NearSpec.Bytes)
    (othersU : List Msg) (ws : List WalkR) : Prop where
  node : NodeWf3 vs
  head : HeadWf hds
  val : ValWf es
  par : Link3.ParentBal vs hds
  vpar : Link3.VParentBal vs es
  sha : Link3.ShaHyp vs hds es others shaS shaR
  vpost : Link3.VPostOk others pv
  vpostLen : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l
  ups : UpsWf v
  upb : UpbBal vs v
  sched : SchedVal v sv
  bytesU : ∀ m, shaR B_BYTES m = cnt ((upsTraffic v).sends B_BYTES ++ othersU) m
  othU : ∀ m ∈ othersU, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS
  digU : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp
  memd : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp)
  tauD : UpsTauDistinct v
  tauB : ∀ s ∈ v, s.row 0 tau < 2 ^ 17
  walk : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hds (allWalks ws v)

/-- The post records and values of the link. -/
abbrev Rpost (vs : List NodeS3) (es : List ValE) : List NodeRec3 := Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs
abbrev Vpost (vs : List NodeS3) (es : List ValE) (pv : Nat → NearSpec.Bytes) : List ValRec3 := Link3.valsPost vs es pv

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws)
  {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

/-- **`UpsExt0` of a segment**, given its parts' shapes and that its length limbs are bytes. -/
theorem ups_ext0 (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256)
    (hshape : ∀ k, k < ps.length → SrcShape ci si ti (sdx k) (kd k) (srcOf (Rpost vs es) (Vpost vs es pv) s ps k)) :
    UpsExt0 s ps ci ti si kd sdx (postB vs) (srcOf (Rpost vs es) (Vpost vs es pv) s ps) (sv (s.row 0 tau)) where
  reads := upb_reads E.node E.ups E.upb hs
  srcEnc := fun k hk =>
    (ups_srcEnc E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP k hk).1
  srcOk := ups_srcOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP hshape
  vlen := (ups_vlen E.ups E.sched hs hL hvb).1
  vbytes := hvb
  digV := ups_digV E.ups E.sched (Link3.ShaHyp.sha E.sha) othersU E.bytesU E.othU E.digU E.tauD
    (ups_idBound E.node E.head E.par E.ups E.upb E.tauB) hs hL
  tiLe := ups_tiLe E.walk E.ups hs hL hP
  xy := ups_xy E.ups hs hL hP

/-- **The parts of a segment** from the other tables, its parts' shapes and its length limbs. -/
theorem ups_partsAll (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256)
    (hshape : ∀ k, k < ps.length → SrcShape ci si ti (sdx k) (kd k) (srcOf (Rpost vs es) (Vpost vs es pv) s ps k)) :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx
        (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k).memD) :=
  ups_partsG E.ups (Link3.ShaHyp.sha E.sha) othersU E.bytesU E.othU E.digU E.memd E.tauD
    (ups_idBound E.node E.head E.par E.ups E.upb E.tauB) hs hL hP (ups_ext0 E hs hL hP hvb hshape)
    (fun k hk => (ups_srcEnc E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP k hk).2)

end

end ZkFormal.NearV3.UpsRows
