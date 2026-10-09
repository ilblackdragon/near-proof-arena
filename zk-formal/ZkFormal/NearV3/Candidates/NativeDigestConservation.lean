import ZkFormal.NearV3.Candidates.ReceiptDigestPartition
import ZkFormal.NearV3.Rcpt.Candidates.NativeNodeDigestBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestBalance

namespace ZkFormal.NearV3.Candidates.NativeDigestConservation
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates Rcpt.Candidates.NodePostUpdate Render

/-- Native SHA outputs and the physical empty-value provider cover HEAD/node
consumers, leaving precisely the written VPOST obligations. All counts retain
occurrence multiplicity; this equation does not discharge the account jobs. -/
theorem physical (ns : List NodeS3) (vals : List ValE) (trh : Trace Fp)
    (th tn tv : Nat) (pub msg : List Fp) (hn : NodeOk ns)
    (hnode : tableBusCount HeadV3.interactions trh th pub B_DIGEST false msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ns))).map Msg.toFp).count msg+
      ((ns.flatMap slotDigests).map Msg.toFp).count msg)
    (hvalue : tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg=
      ((ns.flatMap childDigests).map Msg.toFp).count msg+
      (((nativeValueShaJobs vals).map ZkFormal.Near.Render.digestMsg).map Msg.toFp).count msg+
      tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_DIGEST true msg+
      ((ns.flatMap postSlotDigests).map Msg.toFp).count msg) :
    ((Sha.Gen.expectedDigests (jobsToSha (nativeShaJobs ns vals))).map Msg.toFp).count msg+
      tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_DIGEST true msg+
      ((ns.flatMap postSlotDigests).map Msg.toFp).count msg=
      tableBusCount HeadV3.interactions trh th pub B_DIGEST false msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg := by
  have hs:=physical_node_digest_split ns hn tn pub msg
  rw [ReceiptDigestPartition.jobs_digests] at hnode ⊢
  simp only [nativeShaJobs,List.map_append,List.count_append]
  omega

end ZkFormal.NearV3.Candidates.NativeDigestConservation
