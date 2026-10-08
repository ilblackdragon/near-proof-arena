import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsShape
import ZkFormal.NearV3.Render.Ups.CompactExtract.ValueClosed
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
/-- The facts about the other tables that the parts of every segment need. -/
structure UpsEnv (vs : List NodeS3) (hds : List HeadE) (es : List ValE) (others : List Msg)
    (shaS shaR : Nat → List Fp → Nat) (pv : Nat → NearSpec.Bytes) (v : List UpsSeg) (sv : Nat → NearSpec.Bytes)
    (othersU : List Msg) (ws : List WalkR) (taus : List Nat) : Prop where
  node : NodeWf3 vs
  head : HeadWf hds
  val : ValWf es
  par : Link3.ParentBal vs hds
  vpar : Link3.VParentBal vs es
  sha : Link3.ShaHyp vs hds es others shaS shaR
  vpost : Link3.VPostOk others pv
  vpostLen : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l
  ups : Wf v
  upb : UpbBal vs v
  sched : SchedLength v sv
  bytesU : ∀ m, shaR B_BYTES m = cnt (taus.flatMap (fun t=>relayValueMsgs t (sv t)) ++ (upsTraffic v).sends B_BYTES ++ othersU) m
  relays : ∀t∈taus,t<32
  othU : ∀ m ∈ othersU, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS
  digU : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp
  memd : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp)
  tauD : UpsTauDistinct v
  tauB : ∀ s ∈ v, s.row 0 tau < 32
  walk : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hds (allWalks ws v)

/-- The post records and values of the link. -/
abbrev Rpost (vs : List NodeS3) (es : List ValE) : List NodeRec3 := Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs
abbrev Vpost (vs : List NodeS3) (es : List ValE) (pv : Nat → NearSpec.Bytes) : List ValRec3 := Link3.valsPost vs es pv

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR} {taus : List Nat}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws taus)
  {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

/-- **`UpsExt0` of a segment**, given its parts' shapes and that its length limbs are bytes. -/
theorem ups_ext0 (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256)
    (hshape : ∀ k, k < ps.length → SrcShape ci si ti (sdx k) (kd k) (srcOf (Rpost vs es) (Vpost vs es pv) s ps k)) :
    UpsExt0 s ps ci ti si kd sdx (postB vs) (srcOf (Rpost vs es) (Vpost vs es pv) s ps) (sv (s.row 0 tau)) where
  reads := upb_reads E.node E.ups E.upb hs
  srcEnc := fun k hk =>
    (ups_srcEnc E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP k hk).1
  srcOk := ups_srcOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP hshape
  vlen := ups_vlen E.ups E.sched hs hL hvb
  vbytes := hvb
  digV := by
    intro i hi hg hid hlen
    apply fresh_traffic E.ups (ups_idBound E.node E.head E.par E.ups E.upb E.tauB)
      (Link3.ShaHyp.sha E.sha) taus sv othersU E.relays E.othU E.bytesU E.digU hs hi (E.sched.len _) hg
    · rw [hid,upsIdN_val (by have := E.tauB s hs; omega) (by omega)]
      rfl
    · exact hlen
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
  ups_partsG E.ups (Link3.ShaHyp.sha E.sha) taus sv othersU E.relays E.bytesU E.othU E.digU E.memd E.tauD
    (ups_idBound E.node E.head E.par E.ups E.upb E.tauB) hs hL hP (ups_ext0 E hs hL hP hvb hshape)
    (fun k hk => (ups_srcEnc E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP k hk).2)

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
