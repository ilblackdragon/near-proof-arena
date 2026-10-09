import ZkFormal.NearV3.Candidates.ProcRecordConcatTraffic
import ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
namespace ZkFormal.NearV3.Candidates.ProcRecordSelectedTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest

theorem selected_component : ProcPriorCodecActualFamily.components[3]?=
    some (ProcPriorRecordLinear.table 75 71 72 67 76) := rfl

/-- The selected linear-result repair splits only bus72; original record-byte
requests on75 are identical to the checked three-limb receiver. -/
theorem row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorRecordLinear.interactions 75 71 72 67 76) tr t r pub 75 false=
    rowTraffic (ProcPriorRecordTable.interactions 75 71 72 67 76) tr t r pub 75 false := by
  simp [ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions,rowTraffic]

theorem count (tr : Trace Fp) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76) tr t pub 75 false msg=
    tableBusCount (ProcPriorRecordTable.interactions 75 71 72 67 76) tr t pub 75 false msg := by
  rw [tableBusCount_eq,tableBusCount_eq]
  simp only [row]

theorem balance (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hb:∀b∈bs,b.Valid) (hcap:(ProcRawConcatGeometry.rows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawConcatGeometry.trace bs) t pub 75 true msg=
    tableBusCount (ProcPriorRecordLinear.table 75 71 72 67 76).interactions
      (ProcRecordConcatTraffic.trace ids bs) t pub 75 false msg := by
  change _=tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76) _ _ _ _ _ _
  rw [count]
  exact ProcRecordConcatTraffic.balance ids bs hb hcap t pub msg
end ZkFormal.NearV3.Candidates.ProcRecordSelectedTraffic
