import ZkFormal.NearV3.Candidates.ProcPriorRecordTraffic
import ZkFormal.NearV3.Candidates.ProcRawRecordTraffic
namespace ZkFormal.NearV3.Candidates.ProcNativeRecordBalance
open NearSpec NearSpec.Bandwidth ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest ProcRawConcatGeometry

theorem record (b : NativeBlock) (hb:b.Valid) (ids : List Nat) (j : Nat)
    (r : LinkAllowance) (hj:b.old.links[j]?=some r) :
    (List.range 24).flatMap (fun g=>ProcRawConcatTraffic.messages
      (blockCell b (5+24*j+g)) 75 true)=
    (ProcPriorRecordRows.rowsFor r j).flatMap
      (fun x=>ProcPriorRecordTraffic.messages (ProcPriorRecordCells.cell ids b.run.tau x)) := by
  rw [ProcPriorRecordTraffic.record]
  unfold ProcPriorRecordTraffic.bytes
  rw [List.map_eq_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro g hg
  exact ProcRawRecordTraffic.native_record b hb j g r hj (List.mem_range.mp hg)

/-- Every original occurrence is retained, independently of duplicate or
unknown sender/receiver IDs. No distinctness or native grid order is assumed. -/
theorem indexed (b : NativeBlock) (hb:b.Valid) (ids : List Nat) :
    (List.range b.old.links.length).flatMap (fun j=>(List.range 24).flatMap
      (fun g=>ProcRawConcatTraffic.messages (blockCell b (5+24*j+g)) 75 true))=
    (List.range b.old.links.length).flatMap (fun j=>
      (ProcPriorRecordRows.rowsFor (b.old.links.getD j ⟨0,0,0⟩) j).flatMap
        (fun x=>ProcPriorRecordTraffic.messages (ProcPriorRecordCells.cell ids b.run.tau x))) := by
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  have h:j<b.old.links.length:=List.mem_range.mp hj
  exact record b hb ids j (b.old.links.getD j ⟨0,0,0⟩) (by simp [List.getElem?_eq_getElem h,List.getD])
end ZkFormal.NearV3.Candidates.ProcNativeRecordBalance
