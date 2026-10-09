import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryQueries
import ZkFormal.NearV3.Candidates.ProcRawNativeBudget
import ZkFormal.NearV3.Candidates.ProcPriorMemoryLiftTraffic
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest

theorem all_queries_perm (bs : List NativeBlock) :
    (queryMessages (allRows bs)).Perm
      (bs.flatMap (fun b=>((ProcPriorEvents.queryEvents b.pub.ids b.old.links).map
        (ProcPriorCodecQueries.message b.run.tau)).map (List.map Fp.ofNat))) := by
  induction bs with
  | nil=>exact .nil
  | cons b bs ih=>
    have hp:=tagged_queries_perm b
    simp only [allRows,List.flatMap_cons,queryMessages,List.flatMap_append] at *
    simpa only [List.map_map,Function.comp_def] using hp.append ih

theorem rows_bound (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64) :
    (allRows bs).length≤(ProcRawConcatGeometry.rows bs).length+4096*bs.length := by
  induction bs with
  | nil=>simp [allRows,ProcRawConcatGeometry.rows]
  | cons b bs ih=>
    have hh:=ProcPriorRows.rows_length b.pub.ids b.old.links
    have h64:=hn b (by simp)
    have hsq:=Nat.mul_le_mul h64 h64
    have ht:=ih (fun a ha=>hn a (by simp [ha]))
    simp only [allRows,List.flatMap_cons,List.length_append,tagged,List.length_map,List.length_cons]
    rw [show ProcRawConcatGeometry.rows (b::bs)=ProcRawConcatGeometry.blockRows b++ProcRawConcatGeometry.rows bs from rfl,
      List.length_append,ProcRawConcatGeometry.block_length]
    unfold ProcRawConcatGeometry.blockLength ProcPriorRawSlots.length
    change (ProcPriorRows.rows b.pub.ids b.old.links).length+(allRows bs).length≤_
    omega

theorem capacity (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184) :
    (allRows bs).length<2^22 := by
  have hh:=rows_bound bs hn
  omega

/-- Exact physical query count of the executable native memory provider.
The sorting permutation preserves every duplicate query occurrence. -/
theorem query_count (bs : List NativeBlock) (hc:(allRows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryTable.interactions 67 68 69) (trace (allRows bs)) t pub 68 true msg=
      (bs.flatMap (fun b=>((ProcPriorEvents.queryEvents b.pub.ids b.old.links).map
        (ProcPriorCodecQueries.message b.run.tau)).map (List.map Fp.ofNat))).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [physical_queries _ hc]
  exact List.Perm.count_eq (all_queries_perm bs) msg

/-- The degree-reduced provider retains the exact physical bus68 inventory. -/
theorem gated_query_count (bs : List NativeBlock) (hc:(allRows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
      (ProcPriorMemoryGated.liftTrace (trace (allRows bs)) t pub) t pub 68 true msg=
      (bs.flatMap (fun b=>((ProcPriorEvents.queryEvents b.pub.ids b.old.links).map
        (ProcPriorCodecQueries.message b.run.tau)).map (List.map Fp.ofNat))).count msg := by
  rw [ProcPriorMemoryGated.lift_table_traffic]
  exact query_count bs hc t pub msg

/-- The constructed provider and the actual corrected Codec have equal
natural bus68 multiplicities for the SAME native blocks. This equation does
not assert Local legality of the new concatenated memory trace. -/
theorem codec_balance {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (bs : List NativeBlock) (hlen:bs.length≤32)
    (hb:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ZkFormal.NearV3.Sched.Gen.ActualRun.run
        (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (tmem tcodec : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
      (ProcPriorMemoryGated.liftTrace (trace (allRows bs)) tmem pub) tmem pub 68 true msg=
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs)
        ZkFormal.NearV3.Sched.Gen.codecPad) tcodec pub 68 false msg := by
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hm=>(ZkFormal.NearV3.Sched.prepD0_sched hp b.pub (hb b hm).2.1).n64
  have hc: (allRows bs).length≤2^22:=Nat.le_of_lt (capacity bs hn hlen hraw)
  rw [gated_query_count bs hc,tableBusCount_eq]
  have he:=ProcCodecPriorReadNative.prepared_blocks hp bs (by omega) hb tcodec pub
  exact (congrArg (fun xs=>xs.count msg) he).symm
end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
