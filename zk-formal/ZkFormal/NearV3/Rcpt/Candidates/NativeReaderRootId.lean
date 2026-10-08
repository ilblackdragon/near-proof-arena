import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderRankOrigin

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

theorem extended_root_id (n v d : Nat) (t : PTrie) (key : List Nat) :
    pathRecordId (extendedAddresses n v d t key) t=n := by
  cases t <;> cases key <;> simp [pathRecordId,extendedAddresses]

/-- The chosen reader's MIDROOT occurrence ID is the original forest root ID,
not a freely chosen base-instance field. -/
theorem NativeReaderOrigin.rid {root : OccurrenceAddress} {run : TreeRun} {value : Bytes} {I : UpsInst}
    (h : NativeReaderOrigin root run value I) : I.rid=root.nid := by
  obtain ⟨B,base,Qs,he,rfl⟩:=h
  change pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]) root.tree=root.nid
  exact extended_root_id _ _ _ _ _

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
