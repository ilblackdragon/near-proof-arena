import ZkFormal.NearV3.Render.Ups.CompactExtract.ByteOwnership
import ZkFormal.NearV3.Render.Ups.CompactExtract.FreshDigest
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open NearSpec Assembly ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows UpsGen

/-- Fresh SHA authenticity from the actual compact BYTES traffic, without a
native-run or node-job preimage hypothesis. The only byte inventory premise is
whole-table SHA bus balance with Codec relays and disjoint other message kinds. -/
theorem fresh_traffic {v : List UpsSeg} (hw : Wf v) (hb : CompactIdBound v)
    {shaS shaR : Nat→List Fp→Nat} (hsha : ShaFacts shaS shaR)
    (taus : List Nat) (values : Nat→Bytes) (others : List Msg)
    (htaus : ∀tau∈taus,tau<32)
    (hothers : ∀m∈others,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS)
    (hbytes : ∀m,shaR B_BYTES m=cnt
      (taus.flatMap (fun t=>relayValueMsgs t (values t))++(upsTraffic v).sends B_BYTES++others) m)
    (hdig : ∀m∈(upsTraffic v).recvs B_DIGEST,0<shaS B_DIGEST m.toFp)
    {s : UpsSeg} (hs : s∈v) {i : Nat} (hi : i<s.rows.length)
    (hlen : (values (s.row 0 tau)).length<2^24)
    (hg : s.row i gD=1) (hid : s.row i dI=upsertJobId (s.row 0 tau) 0)
    (hl : s.row i dL=(values (s.row 0 tau)).length) :
    regN (s.row i)=(sha256 (values (s.row 0 tau))).map UInt8.toNat := by
  apply relay_fresh_traffic hsha taus values ((upsTraffic v).sends B_BYTES) others htaus
    (byte_ownership hw hb) hothers hbytes (hb s hs).1 hlen
  · intro b hb'
    obtain ⟨x,_,rfl⟩:=List.mem_map.mp hb'
    exact rowLt hw hs _ _
  · have hm:=digest_member (D:=s.next i) (rowLt hw hs i) hg
    have hh:=hdig _ (mem_upsRecvs.mpr ⟨s,hs,i,hi,hm⟩)
    simpa only [hid,hl,digMsg] using hh
end ZkFormal.NearV3.Render.UpsRelay.Extract
