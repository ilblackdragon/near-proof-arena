import ZkFormal.NearV3.Render.Ups.CompactExtract.PartFresh
import ZkFormal.NearV3.Render.Ups.CompactExtract.ValueLength
import ZkFormal.NearV3.Render.Ups.CompactExtract.FreshTraffic
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open NearSpec Assembly ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows UpsGen

/-- Fresh value fields of an extracted node part refer to the Codec value.
The digest row's gate, identifier and length are derived from the actual field
constraints. Byte range for VLEN comes from node SHA authentication upstream. -/
theorem authenticated_fresh {v : List UpsSeg} (hw : Wf v) (hb : CompactIdBound v)
    {shaS shaR : Nat→List Fp→Nat} (hsha : ShaFacts shaS shaR)
    (taus : List Nat) (values : Nat→Bytes) (others : List Msg)
    (SV : SchedLength v values) (htaus : ∀tau∈taus,tau<32)
    (hothers : ∀m∈others,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS)
    (hbytes : ∀m,shaR B_BYTES m=cnt
      (taus.flatMap (fun t=>relayValueMsgs t (values t))++(upsTraffic v).sends B_BYTES++others) m)
    (hdig : ∀m∈(upsTraffic v).recvs B_DIGEST,0<shaS B_DIGEST m.toFp)
    {s : UpsSeg} (hs : s∈v) {ps : List (Nat×Nat)} {fls : List (List (Nat×Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat→Nat}
    (hP : UpsPlan s ps ci ti di si kd sdx) (k : Nat) (hk : k<ps.length)
    {rL rH : Nat} (UL : UField s rL 4) (UH : UField s rH 32)
    (hSL : stOf (s.row rL)=4) (hSH : stOf (s.row rH)=5)
    (hLo : ps[k].1≤rL) (hLe : rL+4≤ps[k].1+ps[k].2)
    (hHo : ps[k].1≤rH) (hHe : rH+32≤ps[k].1+ps[k].2)
    (hv : vcpV ci (kd k)=0) (hLb : ∀x∈rowsB s rL 4,x<256) :
    (values (s.row 0 tau)).length=s.row 0 L0+256*s.row 0 L1+65536*s.row 0 L2 ∧
      rowsB s rH 32=(sha256 (values (s.row 0 tau))).map UInt8.toNat := by
  have K:=partK hw hs hL hP k hk
  have heL:=vlenFresh hw hs hL.segc K UL hSL hLo hLe hv
  have hlb : s.row 0 L0<256 ∧ s.row 0 L1<256 ∧ s.row 0 L2<256 := by
    rw [heL] at hLb
    exact ⟨hLb _ (by simp),hLb _ (by simp),hLb _ (by simp)⟩
  have hlen:=ups_vlen hw SV hs hL hlb
  obtain ⟨heH,hg,hi,hl⟩:=vhFresh hw hs hL.segc K UH hSH hHo hHe hv hlb
  refine ⟨hlen,?_⟩
  rw [heH]
  apply fresh_traffic hw hb hsha taus values others htaus hothers hbytes hdig hs
    (by have := K.le; omega) (SV.len _) hg
  · rw [hi,upsIdN_val (by have := (hb s hs).1; omega) (by omega)]
    rfl
  · exact hl.trans hlen.symm
end ZkFormal.NearV3.Render.UpsRelay.Extract
