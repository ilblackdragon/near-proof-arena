import ZkFormal.NearV3.Candidates.NativeAccessBytePartition
import ZkFormal.NearV3.Candidates.NativeQueueBytes

namespace ZkFormal.NearV3.Candidates.NativeQueueOwnership
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate Qv

/-- Native queue keys have distinct trie-key tags from account and access-key
records; this is independent of the value bytes and of trie shape. -/
theorem keys_disjoint {pre : PTrie} {v : MainValues} {r : ReadRequest}
    (hr : r ∈ mainRequests pre v) (account receiver : Bytes) (pk : PublicKey) :
    r.key≠accountKeyPath account ∧ r.key≠keyAccessKey receiver pk := by
  simp only [mainRequests,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hr
  rcases hr with (rfl|rfl|rfl)|⟨shard,_,rfl⟩ <;>
    simp [keyDelayedIdx,keyBufferedIdx,keyYieldIdx,keyGroupsData,accountKeyPath,keyAccessKey,nibbles]

theorem outside_writes {pre : PTrie} {v : MainValues} {r : ReadRequest}
    (hr : r ∈ mainRequests pre v) {i : Nat} (hi : valueIndex pre r.key=some i)
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId)) :
    i∉writtenValueIds pre writes := by
  intro hm
  obtain ⟨key,hkey,hslot⟩ := List.mem_filterMap.mp hm
  have hmapped : key.1∈writes.map Prod.fst := List.mem_map.mpr ⟨key,hkey,rfl⟩
  rw [hw] at hmapped
  obtain ⟨receipt,_,he⟩ := List.mem_map.mp hmapped
  rw [←he] at hslot
  exact (keys_disjoint hr receipt.receiverId receipt.receiverId receipt.signerPk).1
    (valueIndex_key_unique pre _ _ i hi hslot)

theorem outside_access {pre : PTrie} {v : MainValues} {r : ReadRequest}
    (hr : r ∈ mainRequests pre v) {i : Nat} (hi : valueIndex pre r.key=some i)
    (rs : List Receipt) : i∉NativeAccessKeyProviders.selected pre rs := by
  intro hm
  obtain ⟨receipt,_,_,_,hslot⟩ := NativeAccessKeyProviders.selected_receipt hm
  exact (keys_disjoint hr [] receipt.receiverId receipt.signerPk).2
    (valueIndex_key_unique pre _ _ i hi hslot)

/-- Every original-state queue provider owns a slot in the exact residual
inventory left after both native account and access-key providers. -/
theorem provider_remaining {pre : PTrie} {v : MainValues} {p : QueueProvider}
    (hp : p∈queueProviders pre (mainRequests pre v) 0 0)
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId)) :
    p.vid∈(NativeAccessBytePartition.remaining pre writes).filter
      (fun i=>!(decide (i∈NativeAccessKeyProviders.selected pre rs))) := by
  obtain ⟨⟨bytes,i⟩,hsel,rfl⟩ := List.mem_map.mp hp
  obtain ⟨hb,r,hr,hi⟩ := queueSelected_mem.mp hsel
  have hlt := (List.getElem?_eq_some_iff.mp hb).1
  have hwritten := outside_writes hr hi hw
  have haccess := outside_access hr hi rs
  simp [NativeAccessBytePartition.remaining,hlt,hwritten,haccess]

end ZkFormal.NearV3.Candidates.NativeQueueOwnership
