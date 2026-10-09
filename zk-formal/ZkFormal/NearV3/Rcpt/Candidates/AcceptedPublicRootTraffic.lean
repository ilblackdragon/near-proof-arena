import ZkFormal.NearV3.Rcpt.Candidates.AcceptedPreparedLength
import ZkFormal.NearV3.Rcpt.Candidates.PublicRootTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.V2 Assembly Assembly.RoutingBoundedLayout

/-- Actual normalized candidate public descriptor traffic, with byte-offset
no-wrap derived from native acceptance rather than a public-size premise. -/
theorem accepted_public_root_counts (AP : AirP) {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {p : Prep}
    (hp : prepD0 cb (nativeHint k w m)=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w) (overhead : Nat)
    (hseg : AP.pubSegs=Public.preparedSegments) (msg : List Fp) :
    let q:=boundedPrep p k.L k.H.shardId
    pubCount AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes q overhead)) B_ROOT true msg=
      ([Msg.toFp ([0]++p.hdr.prevStateRoot.map UInt8.toNat)]).count msg ∧
    pubCount AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes q overhead)) B_ROOT false msg=
      ([Msg.toFp ([p.hdr.K+1]++p.hdr.postStateRoot.map UInt8.toNat)]).count msg := by
  let q:=boundedPrep p k.L k.H.shardId
  have hr : Public.RootsSized q:=prepD0_roots (p:=p) hp
  have hs : ∀s∈q.lists,s.root.length=32:=prepD0_source_roots (p:=p) hp
  have hl:=accepted_prepared_u32 hp hk hw h hm overhead
  let I:=Public.prepared_pubIdx AP q overhead hseg hr hs hl
  have hpre:=Public.prepared_pubIdx_recs AP q overhead hseg hr hs hl B_ROOT true
  have hpost:=Public.prepared_pubIdx_recs AP q overhead hseg hr hs hl B_ROOT false
  rw [Public.preparedOn_rootPre] at hpre
  rw [Public.preparedOn_rootPost q (Public.prep_root_index_lt (p:=p) hp)] at hpost
  have ha:=I.count B_ROOT true msg
  have hb:=I.count B_ROOT false msg
  change I.recs B_ROOT true=_ at hpre
  change I.recs B_ROOT false=_ at hpost
  rw [hpre] at ha
  rw [hpost] at hb
  exact ⟨ha,hb⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
