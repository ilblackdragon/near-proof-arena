import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestPipeline
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.UpsGen Assembly

private theorem slot_counts (ss : List NodeS3) (msg : List Fp) :
    ((ss.flatMap slotDigests).map Msg.toFp).count msg=
      ((ss.flatMap preSlotDigests).map Msg.toFp).count msg+
      ((ss.flatMap postSlotDigests).map Msg.toFp).count msg := by
  induction ss with
  | nil=>simp
  | cons s ss ih=>
    simp only [List.flatMap_cons,slot_digest_split,List.map_append,List.count_append] at *
    omega

/-- Actual node/value traffic partition. The remaining value obligations are
precisely written VPOST slots; VPRE includes every empty revealed value. -/
theorem physical_value_balance (u : Inputs) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) (ts : List PTrie)
    (t : Nat) (pub msg : List Fp)
    (hn : Render.NodeOk (assignList q 0 (records u (Candidates.ChainMetadata.assign cs 0
      (initializeList 0 (forestNodes 0 0 0 ts))))))
    (hv : Render.ValOk (Candidates.ChainMetadata.assignValues cs (seedValuesFrom 0 (forestBytes ts)))) :
    let ns:=assignList q 0 (records u (Candidates.ChainMetadata.assign cs 0
      (initializeList 0 (forestNodes 0 0 0 ts))))
    let es:=Candidates.ChainMetadata.assignValues cs (seedValuesFrom 0 (forestBytes ts))
    tableBusCount SizeCount.nodeTable.interactions (Candidates.TrieCountHeight.node ns pub) t pub B_DIGEST false msg=
      ((ns.flatMap childDigests).map Msg.toFp).count msg+
      (((nativeValueShaJobs es).map ZkFormal.Near.Render.digestMsg).map Msg.toFp).count msg+
      tableBusCount EmptyValue.table.interactions (Candidates.TrieCountHeight.value es pub) t pub B_DIGEST true msg+
      ((ns.flatMap postSlotDigests).map Msg.toFp).count msg := by
  dsimp only
  rw [physical_node_digest_split _ hn,slot_counts,native_preSlot_inventory]
  have he:=EmptyValue.physical_inventory _ hv pub msg t
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
