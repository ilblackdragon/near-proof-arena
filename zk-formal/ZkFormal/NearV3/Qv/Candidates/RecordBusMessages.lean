import ZkFormal.NearV3.Qv.Candidates.RecordFieldTraffic
import ZkFormal.NearV3.Qv.Candidates.RecordTraffic

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open ZkFormal.Near ZkFormal.Near.Dsl

theorem natRowTraffic_bytes (row : List Nat) :
    natRowTraffic ValueTable.interactions row B_VBYTES true =
      if row.getD ValueTable.gb 0=1 then
        [[row.getD ValueTable.vid 0,row.getD ValueTable.pos 0,row.getD ValueTable.byte 0]] else [] := by
  by_cases h : row.getD ValueTable.gb 0=1
  all_goals simp_all [natRowTraffic,ValueTable.interactions,send,recv,natMultBits,rowNatEval,c,k,
    B_VBYTES,B_QSH,ValueTable.B_QVC,h]

theorem byteMessages_natTraffic (rows : List (List Nat)) :
    rows.flatMap (fun row => natRowTraffic ValueTable.interactions row B_VBYTES true) =
      byteMessages rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [List.flatMap_cons,ih,natRowTraffic_bytes]
    clear ih
    by_cases h : row.getD ValueTable.gb 0=1
    all_goals simp_all [byteMessages,h]

/-- The concrete field-traffic contract's VBYTES side is exactly the canonical
byte list previously proved for the native-compatible payload generators. -/
theorem recordsTraffic_bytes (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    (recordsTraffic vs).sends B_VBYTES =
      vs.flatMap (fun v => numberedBytes v.vid 0 v.bytes) := by
  change (recordsRows vs).flatMap _ = _
  rw [byteMessages_natTraffic,records_byteMessages vs hv]

theorem natRowTraffic_qvc (row : List Nat) (sd : Bool) :
    natRowTraffic ValueTable.interactions row ValueTable.B_QVC sd =
      if row.getD ValueTable.vf 0=1 then
        [[row.getD ValueTable.vid 0,row.getD ValueTable.tau 0,
          row.getD ValueTable.mBuffer 0+2*row.getD ValueTable.mRaw 0,
          if sd then 0 else row.getD ValueTable.users 0]] else [] := by
  cases sd <;> by_cases h : row.getD ValueTable.vf 0=1
  all_goals simp_all [natRowTraffic,ValueTable.interactions,send,recv,natMultBits,rowNatEval,c,k,
    ValueTable.mode,smul,B_VBYTES,B_QSH,ValueTable.B_QVC,h]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
