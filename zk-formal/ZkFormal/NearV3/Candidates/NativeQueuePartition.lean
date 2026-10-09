import ZkFormal.NearV3.Candidates.NativeQueueOwnership

namespace ZkFormal.NearV3.Candidates.NativeQueuePartition
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate Qv
open ZkFormal.Algebra

def residual (pre : PTrie) (rs : List Receipt) (writes : List (List Nat×Bytes)) : List Nat :=
  (NativeAccessBytePartition.remaining pre writes).filter
    (fun i=>!(decide (i∈NativeAccessKeyProviders.selected pre rs)))

def ids (pre : PTrie) (v : MainValues) : List Nat :=
  (queueProviders pre (mainRequests pre v) 0 0).map QueueProvider.vid

/-- Select each original queue occurrence once from the exact unowned inventory. -/
theorem selected_permutation {pre : PTrie} {v : MainValues}
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId)) :
    (ids pre v).Perm ((residual pre rs writes).filter (fun i=>decide (i∈ids pre v))) := by
  apply (List.perm_ext_iff_of_nodup (queueProviders_ids_nodup _ _ _ _)
    ((((List.nodup_range).filter _).filter _).filter _)).2
  intro i
  simp only [List.mem_filter,decide_eq_true_eq]
  constructor
  · intro hi
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
    refine ⟨?_,List.mem_map.mpr ⟨p,hp,rfl⟩⟩
    simpa only [NativeAccessBytePartition.remaining,List.mem_filter] using NativeQueueOwnership.provider_remaining hp hw
  · exact fun h=>h.2

/-- Provider payloads are the original bytes at the provider VID, even if
other occurrences have equal bytes or the same queue is queried repeatedly. -/
theorem byte_inventory (pre : PTrie) (v : MainValues) :
    (queueProviders pre (mainRequests pre v) 0 0).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat)) =
    (ids pre v).flatMap (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat)) := by
  simp only [ids,List.flatMap_map]
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨⟨bytes,i⟩,hsel,rfl⟩ := List.mem_map.mp hp
  have hb := (queueSelected_mem.mp hsel).1
  simp [List.getD_eq_getElem?_getD,hb]

/-- Exact original-state byte partition after account/key ownership: queue
providers plus the explicit remaining IDs equal the previous residual. -/
theorem byte_partition {pre : PTrie} {v : MainValues}
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId)) (msg : List Fp) :
    cnt ((queueProviders pre (mainRequests pre v) 0 0).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg+
    cnt (((residual pre rs writes).filter (fun i=>!(decide (i∈ids pre v)))).flatMap
      (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg=
    cnt ((residual pre rs writes).flatMap
      (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg := by
  rw [byte_inventory]
  have hp := List.Perm.flatMap_right
    (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))
    (selected_permutation (pre:=pre) (v:=v) hw)
  have hf := List.Perm.flatMap_right
    (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))
    (List.filter_append_perm (fun i=>decide (i∈ids pre v)) (residual pre rs writes))
  have hc := (hp.map Msg.toFp).count_eq msg
  have hd := (hf.map Msg.toFp).count_eq msg
  simp only [List.flatMap_append,List.map_append,List.count_append,cnt] at hc hd ⊢
  omega

/-- The physical access-key sends and exact queue providers jointly remove
only their owned bytes from the non-account inventory. -/
theorem access_queue_partition {pre : PTrie} {v : MainValues}
    {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (hvalid : ∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      ∀bytes,pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
        bytes.length=9 ∧ bytes.getD 8 0=1)
    (tr : ZkFormal.Air.Trace Fp) (tk : Nat) (pub msg : List Fp)
    (ht : TableTraffic AkeyV3.interactions tr tk pub
      (akeyTraffic (NativeAccessKeyProviders.providers pre rs))) :
    ZkFormal.Air.tableBusCount AkeyV3.interactions tr tk pub B_VBYTES true msg+
    cnt ((queueProviders pre (mainRequests pre v) 0 0).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg+
    cnt (((residual pre rs writes).filter (fun i=>!(decide (i∈ids pre v)))).flatMap
      (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg=
    cnt ((NativeAccessBytePartition.remaining pre writes).flatMap
      (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg := by
  have hkey := NativeAccessBytePartition.physical_split hw hvalid tr tk pub msg ht
  have hqueue := byte_partition (pre:=pre) (v:=v) hw msg
  change _ + cnt ((residual pre rs writes).flatMap _) msg = _ at hkey
  omega

end ZkFormal.NearV3.Candidates.NativeQueuePartition
