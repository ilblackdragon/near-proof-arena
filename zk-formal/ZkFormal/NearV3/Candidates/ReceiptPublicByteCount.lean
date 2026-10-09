import ZkFormal.NearV3.Public.ReceiptIndex
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedPublicRootTraffic

namespace ZkFormal.NearV3.Candidates.ReceiptPublicByteCount
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.V2 Assembly Assembly.RoutingBoundedLayout
open Rcpt.Candidates.NodePostUpdate

theorem records (p : Prep) : Public.bodyRecords p=emitAt K_RF 8 ((p.body.drop 8).map UInt8.toNat) := by
  simp only [Public.bodyRecords,emitAt,List.length_map,List.length_drop]
  apply List.map_congr_left
  intro j hj
  have hd : j<(p.body.drop 8).length := by simpa using List.mem_range.mp hj
  have hm : j<((p.body.drop 8).map UInt8.toNat).length := by simpa using hd
  have hb : 8+j<p.body.length := by simp only [List.length_drop] at hd;omega
  rw [←List.getElem_eq_getD (h:=hm) 0,List.getElem_map,List.getElem_drop,
    ←List.getElem_eq_getD (h:=hb) 0]
  rfl

theorem accepted (AP : AirP) {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {p : Prep}
    (hp : prepD0 cb (nativeHint k w m)=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w) (overhead : Nat)
    (hseg : AP.pubSegs=Public.preparedSegments) (msg : List Fp) :
    pubCount AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes (boundedPrep p k.L k.H.shardId) overhead))
      B_BYTES false msg=cnt (emitAt K_RF 8 ((p.body.drop 8).map UInt8.toNat)) msg := by
  let q:=boundedPrep p k.L k.H.shardId
  have hr : Public.RootsSized q:=prepD0_roots (p:=p) hp
  have hs : ∀s∈q.lists,s.root.length=32:=prepD0_source_roots (p:=p) hp
  have hl:=accepted_prepared_u32 hp hk hw hc hm overhead
  let I:=Public.prepared_pubIdx AP q overhead hseg hr hs hl
  have hi:=Public.prepared_pubIdx_recs AP q overhead hseg hr hs hl B_BYTES false
  rw [show B_BYTES=0 from rfl,Public.prepared_body_records,records] at hi
  have hcount:=I.count B_BYTES false msg
  change I.recs B_BYTES false=_ at hi
  rw [hi] at hcount
  exact hcount

end ZkFormal.NearV3.Candidates.ReceiptPublicByteCount
