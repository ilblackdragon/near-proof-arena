import ZkFormal.NearV3.Public.RootIndex
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRootChain

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.V2 Assembly

theorem prepared_public_root_counts (AP : AirP) {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (overhead : Nat)
    (hseg : AP.pubSegs=Public.preparedSegments)
    (hlen : (Public.preparedBytes p overhead).length<256^4) (msg : List Fp) :
    pubCount AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) B_ROOT true msg=
      ([Msg.toFp ([0]++p.hdr.prevStateRoot.map UInt8.toNat)]).count msg ∧
    pubCount AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) B_ROOT false msg=
      ([Msg.toFp ([p.hdr.K+1]++p.hdr.postStateRoot.map UInt8.toNat)]).count msg := by
  let I:=Public.prepared_pubIdx AP p overhead hseg (prepD0_roots hp) (prepD0_source_roots hp) hlen
  obtain ⟨hpre,hpost⟩:=Public.prepared_root_index AP overhead hseg hp (prepD0_source_roots hp) hlen
  have ha:=I.count B_ROOT true msg
  have hb:=I.count B_ROOT false msg
  change I.recs B_ROOT true=_ at hpre
  change I.recs B_ROOT false=_ at hpost
  rw [hpre] at ha
  rw [hpost] at hb
  exact ⟨ha,hb⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
