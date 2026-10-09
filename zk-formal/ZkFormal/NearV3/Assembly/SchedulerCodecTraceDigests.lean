import ZkFormal.NearV3.Assembly.SchedulerCodecGeneratedDigests
import ZkFormal.NearV3.Candidates.SchedHeight

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Sched Sched.Gen Sched.Complete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

private theorem row_lookup_list (rows : Array (Array Nat)) :
    (List.range rows.size).map (fun r=>rows[r]!)=rows.toList := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range,Array.getElem_toList]
  simp [show i<rows.size by simpa using hj]

/-- Exact physical log22 Codec inventory, including all inactive padding rows. -/
theorem trace_digests (rows : Array (Array Nat)) (hcap:rows.size≤2^22)
    (t : Nat) (pub : List Fp) :
    (List.range ((SchedHeight.trace rows codecPad).height t)).flatMap
      (fun r=>Near.rowTraffic Codec.interactions (SchedHeight.trace rows codecPad) t r pub B_DIGEST false)=
      rows.toList.flatMap rowDigests := by
  change (List.range (2^22)).flatMap _=_
  rw [show 2^22=rows.size+(2^22-rows.size) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz : (List.range (2^22-rows.size)).flatMap (fun r=>
      Near.rowTraffic Codec.interactions (SchedHeight.trace rows codecPad) t (rows.size+r) pub B_DIGEST false)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    apply zero_digest_row
    change Fp.ofNat (natCell rows codecPad (rows.size+r) Codec.dgg)=0
    rw [natCell,natRow_ge _ _ (by omega)]
    simp [codecPad,gd_zrow]
    rfl
  rw [hz,List.append_nil,←row_lookup_list,List.flatMap_map]
  apply UpsRows.flatMap_congr'
  intro r hr
  apply rowDigests_installed
  intro c
  have hlt:r<rows.size:=List.mem_range.mp hr
  change Fp.ofNat (natCell rows codecPad r c)=_
  rw [natCell,natRow_lt _ _ hlt]
  rw [show rows[r]! =rows[r]'hlt by simp [hlt]]
  rfl

/-- Exact bus count for any generated Codec array at the active common height. -/
theorem trace_digest_count (rows : Array (Array Nat)) (hcap:rows.size≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount Codec.interactions (SchedHeight.trace rows codecPad) t pub B_DIGEST false msg=
      (rows.toList.flatMap rowDigests).count msg := by
  rw [tableBusCount_eq,trace_digests rows hcap]

end ZkFormal.NearV3.Assembly.CodecDigest
