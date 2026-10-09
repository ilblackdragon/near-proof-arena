import ZkFormal.NearV3.Candidates.ProcIdConcatTraffic
namespace ZkFormal.NearV3.Candidates.ProcNativeIdBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest

theorem block_length (ids : List Nat) (b : NativeBlock) :
    (ProcIdConcatTraffic.blockRows ids b).length=ids.length+2*b.old.links.length := by
  simp [ProcIdConcatTraffic.blockRows,ProcPriorIdRows.rows_length]

theorem rows_bound (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hi:∀b∈bs,(ids b).length≤64) :
    (ProcIdConcatTraffic.rows ids bs).length≤(ProcRawConcatGeometry.rows bs).length+64*bs.length := by
  induction bs with
  | nil=>simp [ProcIdConcatTraffic.rows,ProcRawConcatGeometry.rows]
  | cons b bs ih=>
    have h:=hi b (by simp)
    have ht:=ih (fun b hb=>hi b (by simp [hb]))
    simp only [ProcIdConcatTraffic.rows,ProcRawConcatGeometry.rows] at ht
    simp only [ProcIdConcatTraffic.rows,ProcRawConcatGeometry.rows,List.flatMap_cons,
      List.length_append,block_length,ProcRawConcatGeometry.block_length,List.length_cons]
    unfold ProcRawConcatGeometry.blockLength ProcPriorRawSlots.length
    omega

theorem native_capacity (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hi:∀b∈bs,(ids b).length≤64) (hk:bs.length≤32)
    (hb:(ProcRawConcatGeometry.rows bs).length≤2001184) :
    (ProcIdConcatTraffic.rows ids bs).length<2^22 := by
  have h:=rows_bound ids bs hi
  omega

/-- Exact physical request/result conservation on the same original records and
prepared ID lists. Boundary-comparison metadata and full ID TableLocal remain
separate from this data-traffic theorem. -/
theorem balance (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hr:(ProcRawConcatGeometry.rows bs).length≤2^22)
    (hi:(ProcIdConcatTraffic.rows ids bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76)
      (ProcRecordConcatTraffic.trace ids bs) t pub (if req then 71 else 72) req msg=
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdConcatTraffic.trace ids bs) t pub (if req then 71 else 72) (!req) msg := by
  rw [ProcIdConcatTraffic.count req ids bs hi,tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [ProcRecordIdTraffic.physical req ids bs hr]
end ZkFormal.NearV3.Candidates.ProcNativeIdBalance
