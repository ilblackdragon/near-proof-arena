import ZkFormal.NearV3.Render.Ups.CompactExtract.SourceValueBridge
import ZkFormal.NearV3.Render.Ups.CompactExtract.ValueBounds
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows Assembly
/-- Codec-to-upsert value extraction without a digest or limb-bound premise.
Downward node authentication supplies the emitted VLEN range before value
semantics is constructed, avoiding circular dependence on fresh-value bounds. -/
theorem ext0_closed {v : List UpsSeg} (hw : Wf v) (hb : CompactIdBound v)
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
    (hM : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (htau : UpsTauDistinct v) :
    UpsExt0 s ps ci ti si kd sdx Pb src (values (s.row 0 tau)) := by
  have HS:=sha_seg hw hsha taus values others htaus hbytes hothers hdig htau hb s hs ps fls ws hL
  have HM:=memd_seg hw hM htau s hs
  have HL:=ups_look0 hw hs hL hP hr he hsrc (ups_tiLe G hw hs hL hP) (ups_xy hw hs hL hP) HS HM
  exact ext0_of_relay hw hb hsha taus values others SV htaus hothers hbytes hdig G hs hL hP
    hr he hsrc (ups_vbytes hw hs hL hP HS HL)

/-- All compact output node serializations, with fresh values authenticated by
Codec and SHA. Neither a fresh hash nor a value-limb range is assumed. -/
theorem parts_closed {v : List UpsSeg} (hw : Wf v) (hb : CompactIdBound v)
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
    (hsrcM : ∀k,k<ps.length → isNode (src k)=true ∧ (src k).memD<2^64)
    (hM : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (htau : UpsTauDistinct v) :
    ∀k (hk:k<ps.length),
      rowsB s ps[k].1 ps[k].2=(nodeEnc (upsQ ci si ti (s.row 0 tX) (values (s.row 0 tau)) kd sdx src k)).map UInt8.toNat ∧
      (kd k≠8 → limbs (fun i=>s.row (ps[k].1+ps[k].2-8+i) rx) 8=
        (upsQ ci si ti (s.row 0 tX) (values (s.row 0 tau)) kd sdx src k).memD) := by
  have X:=ext0_closed hw hb hsha taus values others SV htaus hothers hbytes hdig G hs hL hP hr he hsrc hM htau
  exact ups_partsG hw hsha taus values others htaus hbytes hothers hdig hM htau hb hs hL hP X hsrcM

end ZkFormal.NearV3.Render.UpsRelay.Extract
