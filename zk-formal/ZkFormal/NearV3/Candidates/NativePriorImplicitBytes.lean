import ZkFormal.NearV3.Candidates.NativePriorOwnership
import ZkFormal.NearV3.Candidates.NativeQueueForestPartition

namespace ZkFormal.NearV3.Candidates.NativePriorImplicitBytes
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Assembly Qv

def remaining (tree : PTrie) : List (Bytes×Nat) :=
  (NearSpecV3.valsOf tree).zipIdx.filter
    (fun x=>!(([missingRequest tree]).any (fun r=>valueIndex tree r.key == some x.2)))

theorem outside_queue {tree : PTrie} {i : Nat} (hi:valueIndex tree keyBwState=some i) :
    valueIndex tree (missingRequest tree).key≠some i := by
  intro hq
  have he:=valueIndex_key_unique tree _ _ i hi hq
  simp [missingRequest,keyBwState,keyDelayedIdx,nibbles] at he

theorem entry_remaining {tree : PTrie} {i : Nat} {bs : Bytes}
    (hi:valueIndex tree keyBwState=some i) (hb:(NearSpecV3.valsOf tree)[i]?=some bs) :
    (bs,i)∈remaining tree := by
  apply List.mem_filter.mpr
  exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hb,by simp [outside_queue hi]⟩

/-- Each implicit prestate uses its own global value offset. The raw prior
parser removes exactly one remaining occurrence after the missing-chunk queue
provider, preserving all other occurrences and their byte multiplicities. -/
theorem physical_partition {tree : PTrie} {i : Nat} {bs : Bytes} {old : Bandwidth.State}
    (hi:valueIndex tree keyBwState=some i) (hb:(NearSpecV3.valsOf tree)[i]?=some bs)
    (hd:Bandwidth.State.decode bs=some old) (hfit:bs.length≤2^22)
    (base t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (ProcPriorRawGen.trace old (base+i) true) t pub B_VBYTES true msg+
    cnt (((remaining tree).erase (bs,i)).flatMap
      (fun x=>emitAt (base+x.2) 0 (x.1.map UInt8.toNat))) msg=
    cnt (NativeQueueForestPartition.remainingBytes tree [missingRequest tree] base) msg := by
  rw [ProcPriorRawByteTraffic.decoded_count bs old (base+i) t pub msg hd hfit]
  have hp:=List.Perm.flatMap_right
    (fun x : Bytes×Nat=>emitAt (base+x.2) 0 (x.1.map UInt8.toNat))
    (List.perm_cons_erase (entry_remaining hi hb))
  have hc:=(hp.map Msg.toFp).count_eq msg
  simp only [List.flatMap_cons,List.map_append,List.count_append] at hc
  exact hc.symm

end ZkFormal.NearV3.Candidates.NativePriorImplicitBytes
