import ZkFormal.NearV3.Candidates.ReceiptGatedShaJobs
import ZkFormal.NearV3.Assembly.RcptSourceRcPreimages

namespace ZkFormal.NearV3.Candidates.ReceiptSourceDigestBridge
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton Rcpt.Candidates

/-- Equality includes actual indexed IDs and duplicate flags, not only bytes. -/
theorem jobs_source (pub : List Fp) (ls : RcptV3Vs) (own : Nat)
    (sources : List SrcList) (entries : List ProofEntry)
    (h : rcShaPayloads pub ls=(sourceRcShaJobs own sources entries).map (·.bytes)) :
    ReceiptGatedShaJobs.rcJobs pub ls (Public.sourceDup sources)=sourceRcShaJobs own sources entries := by
  unfold ReceiptGatedShaJobs.rcJobs
  rw [h]
  apply List.ext_getElem
  · simp [sourceRcShaJobs]
  · intro i hi hj
    simp only [sourceRcShaJobs,List.map_map,List.length_map,List.length_range] at hj
    simp [sourceRcShaJobs,List.getElem_zipIdx,List.getElem_map,List.getElem_range,hj]

theorem source_outputs {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness} (pub : List Fp) (ls : RcptV3Vs)
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : rcShaPayloads pub ls=(sourceRcShaJobs k.H.shardId p.lists w.entries).map (·.bytes)) :
    Sha.Gen.expectedDigests (ReceiptGatedShaJobs.rcJobs pub ls (Public.sourceDup p.lists))=
      ((DedupCompile.blocks p.lists w.entries).filter (fun B=>!B.dup)).map
        (fun B=>digMsg (msgId K_RC B.j) B.L B.leaf) := by
  rw [jobs_source pub ls k.H.shardId p.lists w.entries h]
  exact source_rc_digest_outputs ha hp hk hw

end ZkFormal.NearV3.Candidates.ReceiptSourceDigestBridge
