import ZkFormal.NearV3.Public.RootIndex
import ZkFormal.NearV3.Public.ReceiptIndex
import ZkFormal.NearV3.Public.HeaderBinding

/-! Public bindings available to the final AIR assembly from actual successful
native preparation. This is a public-input theorem, not the final admission certificate. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpec NearSpecV3 Sched

structure PreparedBindings (AP : AirP) (p : Prep) (witnessOverhead : Nat) where
  index : PubIdx AP (ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)) Fp.ofNat
  fits : pubFit AP (ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)) = true
  source : index.recs B_SRC true = sourceRecords p
  boundary : index.recs B_BNDP true = boundaryRecords p
  body : index.recs 0 false = bodyRecords p
  pubb : index.recs B_SPUBB true = (schedulerRecords p).pubb
  par : index.recs B_SPAR true = (schedulerRecords p).par
  dlSend : index.recs B_SDL true = (schedulerRecords p).dlSend
  dlRecv : index.recs B_SDL false = (schedulerRecords p).dlRecv
  rootPre : index.recs B_ROOT true = [[0] ++ p.hdr.prevStateRoot.map UInt8.toNat]
  rootPost : index.recs B_ROOT false = [[p.hdr.K+1] ++ p.hdr.postStateRoot.map UInt8.toNat]
  bodyLength :
    V2.leNat ((List.range 4).map (fun k => PubVal.val
      ((ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)).getD (PH_BLEN+k) 0))) = p.body.length
  overhead :
    V2.leNat ((List.range 4).map (fun k => PubVal.val
      ((ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)).getD (SizeV3.PH_WOVH+k) 0))) = witnessOverhead

/-- The only remaining numeric premises are bounds on the encoded statement and
overhead. The actual overhead's witness-size meaning is a separate assembly obligation. -/
def bindPrepared (AP : AirP) {cb : Bytes} {hint : Hint} {p : Prep} (witnessOverhead : Nat)
    (hseg : AP.pubSegs = preparedSegments) (hp : prepD0 cb hint = .ok p)
    (hlen : (preparedBytes p witnessOverhead).length ≤ AP.maxPub) (hmax : AP.maxPub < 256^4)
    (ho : witnessOverhead < 256^4) : PreparedBindings AP p witnessOverhead := by
  have hr := Assembly.prepD0_roots hp
  have hs := Assembly.prepD0_source_roots hp
  have hlen' : (preparedBytes p witnessOverhead).length < 256^4 := by omega
  let I := prepared_pubIdx AP p witnessOverhead hseg hr hs hlen'
  obtain ⟨hsource,hboundary,hbody⟩ := prepared_receipt_index AP p witnessOverhead hseg hr hs hlen'
  obtain ⟨hpubb,hpar,hsend,hrecv⟩ := prepared_scheduler_index AP witnessOverhead hseg hp hr hs hlen'
  obtain ⟨hpre,hpost⟩ := prepared_root_index AP witnessOverhead hseg hp hs hlen'
  exact ⟨I,prepared_pubFit AP p witnessOverhead hseg hr hs hlen hmax,
    hsource,hboundary,hbody,hpubb,hpar,hsend,hrecv,hpre,hpost,
    prepared_body_count p witnessOverhead hr hlen',prepared_overhead_count p witnessOverhead hr ho⟩

end ZkFormal.NearV3.Public
