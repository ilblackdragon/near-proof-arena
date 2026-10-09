import ZkFormal.NearV3.Candidates.ProcScanCmpSilent
import ZkFormal.NearV3.Candidates.ProcDistRowCost
namespace ZkFormal.NearV3.Candidates.ProcDistCmpPhysical
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ProcDistCmpTraffic

theorem cells_active (rows:Array (Array Nat))(r:Nat)(hr:r<rows.size)(t:Nat) :
    (SchedHeight.trace rows distPad).cell t r=fun c=>Fp.ofNat rows[r]![c]! := by
  funext c
  change Fp.ofNat (natCell rows distPad r c)=_
  unfold natCell
  rw [natRow_lt _ _ hr]
  rw [show rows[r]! = rows[r]'hr by simp [hr]]
  rfl

theorem cells_padding (rows:Array (Array Nat))(r:Nat)(hr:rows.size≤r)(t:Nat) :
    (SchedHeight.trace rows distPad).cell t r=fun _=>0 := by
  funext c
  change Fp.ofNat (natCell rows distPad r c)=_
  unfold natCell
  rw [natRow_ge _ _ hr]
  simp [distPad,gd_zrow]
  rfl

theorem physical (rows:Array (Array Nat))(hcap:rows.size≤2^22)(t:Nat)(pub:List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ScanDist.table.interactions
      (SchedHeight.trace rows distPad) t r pub B_SCMP true)=
    rows.toList.flatMap (fun row=>messages (fun c=>Fp.ofNat row[c]!)) := by
  simp only [row_messages]
  rw [show 2^22=rows.size+(2^22-rows.size) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-rows.size)).flatMap (fun j=>messages
      ((SchedHeight.trace rows distPad).cell t (rows.size+j)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j hj
    rw [cells_padding rows _ (by omega)]
    simp [messages,show (0:Fp)≠1 from by decide +kernel]
  rw [hz,List.append_nil,←ProcCodecConcatTraffic.row_lookup rows,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r hr
  rw [cells_active rows r (List.mem_range.mp hr)]

theorem merged (I:Input)(R:Run)(d:DistOut)(h:distRows I R=.ok d) :
    (sdRows R d).toList.flatMap (fun row=>messages (fun c=>Fp.ofNat row[c]!))=d.cmps.map cmpMsg := by
  simp only [sdRows,Array.toList_append,List.flatMap_append]
  rw [ProcScanCmpSilent.traffic,List.nil_append,ProcDistCmpTraffic.generated I R d h]

open ZkFormal.NearV3.Assembly.CodecDigest ProcNativeOldComparisonCapacity

def rows (bs:List NativeBlock) : Array (Array Nat) :=
  (bs.flatMap (fun b=>(sdRows b.run (distribution b)).toList)).toArray

theorem blocks (bs:List NativeBlock)(hn:∀b∈bs,b.run.n≤64)
    (hcap:(rows bs).size≤2^22)(t:Nat)(pub:List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ScanDist.table.interactions
      (SchedHeight.trace (rows bs) distPad) t r pub B_SCMP true)=
    (bs.flatMap (fun b=>(distribution b).cmps)).map cmpMsg := by
  rw [physical _ hcap]
  simp only [rows,List.toList_toArray,List.flatMap_assoc,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  exact merged _ b.run _ (distribution_eq b (hn b hb))
end ZkFormal.NearV3.Candidates.ProcDistCmpPhysical
