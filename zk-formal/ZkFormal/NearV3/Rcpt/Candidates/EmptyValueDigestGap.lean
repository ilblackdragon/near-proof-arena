import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestPhysical
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestJobs

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Assembly

/-- Native value revelation explicitly permits an empty stored value. -/
theorem empty_mkSlot : mkSlot (mkStore [[]]) 0 (sha256 []) true=.val [] := by
  simp [mkSlot,mkStore,storeGet]

/-- The raw group-data read accepts that empty value. This is a local runtime
fixture, not a complete accepted checkD0a witness. -/
theorem empty_group_read (shard : Nat) :
    readKey (.leaf (keyGroupsData shard) (.val []) 0) (keyGroupsData shard)
      "BufferedReceiptGroupsQueueData"=.ok (some []) := by
  simp [readKey,PTrie.find,Slot.get]

/-- Existing value jobs omit the empty record altogether. -/
theorem empty_value_jobs (vid : Nat) : nativeValueShaJobs [seedValue vid []]=[] := by
  simp [nativeValueShaJobs,seedValue]

/-- The same revealed node slot nevertheless requests its empty SHA digest. -/
theorem empty_slot_digest (vid nid tau depth : Nat) (key : List Nat) :
    slotDigests (seedNodeView tau depth nid vid (.leaf key (.val []) 0))=
      [digMsg (msgId K_VPRE vid) 0 ((sha256 []).map UInt8.toNat)] := by
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
