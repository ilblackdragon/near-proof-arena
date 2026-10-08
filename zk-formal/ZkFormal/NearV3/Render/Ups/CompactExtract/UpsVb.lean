import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsShapeK
import ZkFormal.NearV3.Render.Ups.CompactExtract.ValueBounds
import ZkFormal.NearV3.Extract.Ups.UpsVb
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR} {taus : List Nat}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws taus)
  {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

/-- **`vbytes` from the other tables.** -/
theorem ups_vbytesE : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256 := by
  have hw := E.ups
  have HS := sha_seg hw (Link3.ShaHyp.sha E.sha) taus sv othersU E.relays E.bytesU E.othU E.digU E.tauD
    (ups_idBound E.node E.head E.par E.ups E.upb E.tauB) s hs ps fls wsl hL
  have HM := memd_seg hw E.memd E.tauD s hs
  have HL := ups_look0 hw hs hL hP (upb_reads E.node E.ups E.upb hs)
    (fun k hk => (ups_srcEnc E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP k hk).1)
    (ups_srcOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP (ups_shape E hs hL hP))
    (ups_tiLe E.walk E.ups hs hL hP) (ups_xy E.ups hs hL hP) HS HM
  exact ups_vbytes hw hs hL hP HS HL

/-- **`UpsExt0` of every segment** from the other tables alone. -/
theorem ups_ext0V :
    UpsExt0 s ps ci ti si kd sdx (postB vs) (srcOf (Rpost vs es) (Vpost vs es pv) s ps) (sv (s.row 0 tau)) :=
  ups_ext0S E hs hL hP (ups_vbytesE E hs hL hP)

/-- **The parts of every segment** from the other tables alone: every part `k` emits `nodeEnc (upsQ … k)` and
(not the new leaf) sends its node's exact `memory_usage` on `MEMD`. -/
theorem ups_partsAllV :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx
        (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k).memD) :=
  ups_partsAllS E hs hL hP (ups_vbytesE E hs hL hP)

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
