import ZkFormal.NearV3.Candidates.ProcNativeDistComparisonTraffic
namespace ZkFormal.NearV3.Candidates.ProcScanDistPhases
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ZkFormal.NearV3.Assembly.CodecDigest
open ProcNativeOldComparisonCapacity

def scanRows (bs:List NativeBlock) := bs.flatMap (fun b=>(Scan.rows b.run).toList)
def distRows (bs:List NativeBlock) := bs.flatMap (fun b=>(distribution b).rows.toList)
def rows (bs:List NativeBlock) : Array (Array Nat) := (scanRows bs++distRows bs).toArray
def trace (bs:List NativeBlock) := SchedHeight.trace (rows bs) distPad

theorem size_eq (bs:List NativeBlock) : (rows bs).size=(ProcDistCmpPhysical.rows bs).size := by
  unfold rows scanRows distRows ProcDistCmpPhysical.rows
  simp only [List.size_toArray,List.length_append]
  induction bs with
  | nil=>rfl
  | cons b bs ih=>
    simp only [List.flatMap_cons,List.length_append,sdRows,Array.toList_append,List.length_append] at *
    omega

theorem capacity {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs) :
    (rows bs).size≤2758688 ∧ (rows bs).size<2^22 := by
  rw [size_eq]
  have hb:=ProcNativeDistComparisonTraffic.bounds hp bs hc
  constructor <;> omega

theorem scan_silent (bs:List NativeBlock) :
    (scanRows bs).flatMap (fun row=>ProcDistCmpTraffic.messages (fun c=>Fp.ofNat row[c]!))=[] := by
  unfold scanRows
  rw [List.flatMap_assoc,List.flatMap_eq_nil_iff]
  intro b hb
  exact ProcScanCmpSilent.traffic b.run

theorem physical {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs)
    (t:Nat)(pub:List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ScanDist.table.interactions
      (trace bs) t r pub B_SCMP true)=
    (bs.flatMap (fun b=>(distribution b).cmps)).map cmpMsg := by
  rw [show trace bs=SchedHeight.trace (rows bs) distPad from rfl,
    ProcDistCmpPhysical.physical (rows bs) (by have h:=capacity hp bs hc;omega)]
  simp only [rows,List.toList_toArray,List.flatMap_append,scan_silent,List.nil_append,
    distRows,List.flatMap_assoc,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  exact ProcDistCmpTraffic.generated _ b.run _ (distribution_eq b (hc.valid b hb).2)

theorem count {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs)
    (t:Nat)(pub msg:List Fp) :
    tableBusCount ScanDist.table.interactions (trace bs) t pub B_SCMP true msg=
    ((bs.flatMap (fun b=>(distribution b).cmps)).map cmpMsg).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical hp bs hc t pub)
end ZkFormal.NearV3.Candidates.ProcScanDistPhases
