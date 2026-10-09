import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryWriteInventory
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest

theorem write_count (bs : List NativeBlock) (hc:(allRows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryTable.interactions 67 68 69) (trace (allRows bs)) t pub 67 false msg=
      (bs.flatMap (fun b=>(ProcPriorEvents.writeEvents b.pub.ids b.old.links).map
        (ProcRecordWriteTraffic.message b.run.tau))).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [physical_writes _ hc]
  exact List.Perm.count_eq (all_writes_perm bs) msg

theorem gated_write_count (bs : List NativeBlock) (hc:(allRows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
      (ProcPriorMemoryGated.liftTrace (trace (allRows bs)) t pub) t pub 67 false msg=
      (bs.flatMap (fun b=>(ProcPriorEvents.writeEvents b.pub.ids b.old.links).map
        (ProcRecordWriteTraffic.message b.run.tau))).count msg := by
  rw [ProcPriorMemoryGated.lift_table_traffic]
  exact write_count bs hc t pub msg

/-- Same native blocks, current IDs, original records and ordinals on both
sides: selected RecordLinear sends equal sorted memory receives exactly. -/
theorem record_balance (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (tm tr : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
      (ProcPriorMemoryGated.liftTrace (trace (allRows bs)) tm pub) tm pub 67 false msg=
    tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76)
      (ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs) tr pub 67 true msg := by
  have hc:(allRows bs).length≤2^22:=Nat.le_of_lt (capacity bs hn hlen hraw)
  rw [gated_write_count bs hc,tableBusCount_eq]
  have hh:=ProcRecordWriteTraffic.physical (fun b=>b.pub.ids) bs (by omega) tr pub
  exact (congrArg (fun xs=>xs.count msg) hh).symm
end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
