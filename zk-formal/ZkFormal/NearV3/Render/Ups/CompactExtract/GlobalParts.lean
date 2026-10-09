import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsLook
import ZkFormal.NearV3.Render.Ups.CompactExtract.ValueLength
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows
/-- All twelve node constructors reconstructed from the compact physical view,
Codec relay/SHA balance, MEMD balance and authenticated source semantics. -/
theorem ups_partsG {v : List UpsSeg} (hw : Wf v) {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (taus : List Nat) (values : Nat→NearSpec.Bytes) (others : List Msg)
    (htaus : ∀t∈taus,t<32) (hbytes : ∀ m, shaR B_BYTES m = cnt (taus.flatMap (fun t=>relayValueMsgs t (values t)) ++ (upsTraffic v).sends B_BYTES ++ others) m)
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdig : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (hM : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (htau : UpsTauDistinct v) (hB : CompactIdBound v)
    {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    {Pb : Nat → List Nat} {src : Nat → NearSpec.PTrie} {val : NearSpec.Bytes}
    (X0 : UpsExt0 s ps ci ti si kd sdx Pb src val)
    (hsrcM : ∀ k, k < ps.length → isNode (src k) = true ∧ (src k).memD < 2 ^ 64) :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) val kd sdx src k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) val kd sdx src k).memD) :=
  ups_partsS hw hs hL hP X0 hsrcM (sha_seg hw hsha taus values others htaus hbytes hoth hdig htau hB s hs ps fls ws hL)
    (memd_seg hw hM htau s hs)

end ZkFormal.NearV3.Render.UpsRelay.Extract
