import ZkFormal.NearV3.Render.Ups.CompactExtract.GlobalParts
import ZkFormal.NearV3.Render.Ups.CompactExtract.WalkLink
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows Assembly
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **`UpsExt0.xy`**: a split with a new leaf (other than `LSa`) has its moved nibble `x = tX` different
from the new leaf's nibble `y`: the terminal `KEY` edge's nibble differs from the walk symbol. -/
theorem ups_xy : spYN ci = 1 → ci ≠ 4 → s.row 0 tX ≠ UpsSpec.yOf si := by
  intro hy h4
  obtain ⟨i1, i2, i3, i4⟩ := hP.ix
  have hci : 4 ≤ ci ∧ ci ≤ 10 := by unfold spYN at hy; split at hy <;> omega
  have h0 : 0 < s.rows.length := by have := hL.walk.1; omega
  obtain ⟨c1, c2, c3, c4⟩ := hP.seg 0 h0
  have hsi := (spbSeg (okRow hw hs h0) (rowLt hw hs _) (nextLt hw hs _) hL.walk.2.1 c1 c4 hci.1 hci.2 i4).2.2.2 hy
  obtain ⟨-, -, -, hmK, -, -, -, -, -, hK, -⟩ := ups_walkTerm hw hs hL hP
  rw [if_pos hci.1] at hmK
  obtain ⟨-, hnib⟩ := (hK hci.1).2 h4
  have hlt : si + 1 < s.rows.length := by have := hL.walk.1; omega
  have F := wRowF hw hs hL (si + 1) (by omega)
  have hne := (F.absK hmK).2
  rw [hnib, hL.segc _ hlt tX (by decide), wsym_yOf si hsi] at hne
  exact hne

end


/-- Construct the old semantic input contract from source/walk authentication
and the Codec relay. No desired fresh-value digest is an input premise. -/
theorem ext0_of_relay {v : List UpsSeg} (hw : Wf v) (hb : CompactIdBound v)
    {shaS shaR : Nat→List Fp→Nat} (hsha : ShaFacts shaS shaR)
    (taus : List Nat) (values : Nat→NearSpec.Bytes) (others : List Msg)
    (SV : SchedLength v values) (htaus : ∀tau∈taus,tau<32)
    (hothers : ∀m∈others,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS)
    (hbytes : ∀m,shaR B_BYTES m=cnt
      (taus.flatMap (fun t=>relayValueMsgs t (values t))++(upsTraffic v).sends B_BYTES++others) m)
    (hdig : ∀m∈(upsTraffic v).recvs B_DIGEST,0<shaS B_DIGEST m.toFp)
    {f : Nat→Nat} {vs : List NodeS3} {V : List ValRec3} {heads : List HeadE} {walks : List WalkR}
    (G : Walk3.WalkHyp f vs V heads (allWalks walks v))
    {s : UpsSeg} (hs : s∈v) {ps : List (Nat×Nat)} {fls : List (List (Nat×Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat→Nat}
    (hP : UpsPlan s ps ci ti di si kd sdx)
    {Pb : Nat→List Nat} {src : Nat→NearSpec.PTrie}
    (hr : UpbReads s Pb)
    (he : ∀k (hk:k<ps.length),Pb (s.row ps[k].1 sN)=(nodeEnc (src k)).map UInt8.toNat)
    (hsrc : ∀k,k<ps.length → SrcOk ci si ti (sdx k) (kd k) (src k))
    (hvb : s.row 0 L0<256 ∧ s.row 0 L1<256 ∧ s.row 0 L2<256) :
    UpsExt0 s ps ci ti si kd sdx Pb src (values (s.row 0 tau)) := by
  refine ⟨hr,he,hsrc,ups_vlen hw SV hs hL hvb,hvb,?_,
    ups_tiLe G hw hs hL hP,ups_xy hw hs hL hP⟩
  intro i hi hg hid hlen
  apply fresh_traffic hw hb hsha taus values others htaus hothers hbytes hdig hs hi (SV.len _) hg
  · rw [hid,upsIdN_val (by have := (hb s hs).1; omega) (by omega)]
    rfl
  · exact hlen

end ZkFormal.NearV3.Render.UpsRelay.Extract
