import ZkFormal.NearV3.Candidates.NativeQueuePartition
import ZkFormal.NearV3.Candidates.NativePriorRawBytes

namespace ZkFormal.NearV3.Candidates.NativePriorOwnership
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate Qv
open ZkFormal.Air ZkFormal.Algebra

theorem outside_writes {pre : PTrie} {i : Nat} (hi:valueIndex pre keyBwState=some i)
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId)) :
    i∉writtenValueIds pre writes := by
  intro hm
  obtain ⟨key,hkey,hslot⟩:=List.mem_filterMap.mp hm
  have hkey':key.1∈writes.map Prod.fst:=List.mem_map.mpr ⟨key,hkey,rfl⟩
  rw [hw] at hkey'
  obtain ⟨receipt,_,he⟩:=List.mem_map.mp hkey'
  rw [←he] at hslot
  have heq:=valueIndex_key_unique pre _ _ i hi hslot
  simp [keyBwState,accountKeyPath,nibbles] at heq

theorem outside_access {pre : PTrie} {i : Nat} (hi:valueIndex pre keyBwState=some i)
    (rs : List Receipt) : i∉NativeAccessKeyProviders.selected pre rs := by
  intro hm
  obtain ⟨receipt,_,_,_,hslot⟩:=NativeAccessKeyProviders.selected_receipt hm
  have heq:=valueIndex_key_unique pre _ _ i hi hslot
  simp [keyBwState,keyAccessKey,nibbles] at heq

theorem outside_queue {pre : PTrie} {i : Nat} (hi:valueIndex pre keyBwState=some i)
    (v : MainValues) : i∉NativeQueuePartition.ids pre v := by
  intro hm
  obtain ⟨p,hp,he⟩:=List.mem_map.mp hm
  obtain ⟨⟨bytes,j⟩,hsel,rfl⟩:=List.mem_map.mp hp
  obtain ⟨_,r,hr,hslot⟩:=queueSelected_mem.mp hsel
  have hij:j=i:=by simpa using he
  subst j
  have heq:=valueIndex_key_unique pre _ _ i hi hslot
  simp only [mainRequests,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hr
  rcases hr with (rfl|rfl|rfl)|⟨shard,_,rfl⟩ <;>
    simp [keyBwState,keyDelayedIdx,keyBufferedIdx,keyYieldIdx,keyGroupsData,nibbles] at heq

/-- The native prior parser owns a slot still present in the exact residual
after accounts, access keys and queue providers; no duplicate supply is added. -/
theorem main_remaining {pre : PTrie} {i : Nat} (hi:valueIndex pre keyBwState=some i)
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId)) (v : MainValues) :
    i∈(NativeQueuePartition.residual pre rs writes).filter
      (fun j=>!(decide (j∈NativeQueuePartition.ids pre v))) := by
  obtain ⟨bs,hf⟩:=valueIndex_defined pre keyBwState i hi
  obtain ⟨j,hj,hb⟩:=valueIndex_complete pre keyBwState bs hf
  have he:i=j:=Option.some.inj (hi.symm.trans hj)
  subst j
  have hlt: i<(NearSpecV3.valsOf pre).length:=(List.getElem?_eq_some_iff.mp hb).1
  simp [NativeQueuePartition.residual,NativeAccessBytePartition.remaining,hlt,
    outside_writes hi hw,outside_access hi rs,outside_queue hi v]

def remainingIds (pre : PTrie) (rs : List Receipt) (writes : List (List Nat×Bytes))
    (v : MainValues) : List Nat :=
  (NativeQueuePartition.residual pre rs writes).filter
    (fun j=>!(decide (j∈NativeQueuePartition.ids pre v)))

/-- Physical prior-byte supply removes exactly its own occurrence from the
remaining original-state demand. Other equal-valued occurrences remain. -/
theorem present_partition {pre : PTrie} {i : Nat} (hi:valueIndex pre keyBwState=some i)
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (v : MainValues) {bs : Bytes} {old : Bandwidth.State}
    (hb:(NearSpecV3.valsOf pre)[i]?=some bs)
    (hd:Bandwidth.State.decode bs=some old) (hfit:bs.length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (ProcPriorRawGen.trace old i true) t pub B_VBYTES true msg+
    cnt (((remainingIds pre rs writes v).erase i).flatMap
      (fun j=>emitAt j 0 (((NearSpecV3.valsOf pre).getD j []).map UInt8.toNat))) msg=
    cnt ((remainingIds pre rs writes v).flatMap
      (fun j=>emitAt j 0 (((NearSpecV3.valsOf pre).getD j []).map UInt8.toNat))) msg := by
  rw [ProcPriorRawByteTraffic.decoded_count bs old i t pub msg hd hfit]
  have hp:=List.Perm.flatMap_right
    (fun j=>emitAt j 0 (((NearSpecV3.valsOf pre).getD j []).map UInt8.toNat))
    (List.perm_cons_erase (main_remaining hi hw v))
  have hc:=(hp.map Msg.toFp).count_eq msg
  simp only [List.flatMap_cons,List.map_append,List.count_append] at hc
  simp only [List.getD_eq_getElem?_getD,hb,Option.getD_some] at hc
  exact hc.symm

end ZkFormal.NearV3.Candidates.NativePriorOwnership
