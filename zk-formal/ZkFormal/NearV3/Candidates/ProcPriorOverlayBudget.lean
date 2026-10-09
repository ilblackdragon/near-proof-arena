import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryComplete
import ZkFormal.NearV3.Candidates.ProcRecordConcatTraffic
import ZkFormal.NearV3.Candidates.ProcPriorIdRows
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayBudget
open ZkFormal.NearV3.Assembly.CodecDigest

def idRows (bs : List NativeBlock) :=
  bs.flatMap (fun b=>ProcPriorIdRows.rows b.pub.ids b.old.links)
def occupied (bs : List NativeBlock) : Nat :=
  (ProcPriorNativeMemory.allRows bs).length+(idRows bs).length+
  (ProcRawConcatGeometry.rows bs).length+
  (ProcRecordConcatTraffic.rows (fun b=>b.pub.ids) bs).length

/-- Charge all four selected overlay components to the SAME old-record
occurrences. Bounding each component by the full raw budget independently
would lose the shared-height bound. -/
theorem charge (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64) :
    2*occupied bs≤3*(ProcRawConcatGeometry.rows bs).length+8320*bs.length := by
  induction bs with
  | nil=>simp [occupied,ProcPriorNativeMemory.allRows,idRows,ProcRawConcatGeometry.rows,ProcRecordConcatTraffic.rows]
  | cons b bs ih=>
    have h64:=hn b (by simp)
    have hsquare:=Nat.mul_le_mul h64 h64
    have hm:=ProcPriorRows.rows_length b.pub.ids b.old.links
    have hid:=ProcPriorIdRows.rows_length b.pub.ids b.old.links
    have hr:=ProcRecordConcatTraffic.block_length b.pub.ids b
    have hraw:=ProcRawConcatGeometry.block_length b
    have htail:=ih (fun b hb=>hn b (by simp [hb]))
    simp only [occupied,ProcPriorNativeMemory.allRows,idRows,ProcRawConcatGeometry.rows,
      ProcRecordConcatTraffic.rows,List.flatMap_cons,List.length_append,List.length_cons,
      ProcPriorNativeMemory.tagged,List.length_map] at htail ⊢
    unfold ProcRawConcatGeometry.blockLength ProcPriorRawSlots.length at hraw
    omega

/-- One extra row per stage still fits log22. This is a capacity theorem;
local boundary/clock installation is a separate obligation. -/
theorem capacity (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184) :
    occupied bs+4≤3134900 ∧ occupied bs+4<2^22 := by
  have hc:=charge bs hn
  omega
end ZkFormal.NearV3.Candidates.ProcPriorOverlayBudget
