import ZkFormal.NearV3.Assembly.SchedulerNativeDigests

namespace ZkFormal.NearV3.Assembly
open NearSpec Render.UpsGen ZkFormal.Near

/-- One message from the same indexed native SHA preimage batch. -/
def nativeJobMessage (run : TreeRun) (v : Bytes) (tau j : Nat) : Msg :=
  let bytes:=(v::run.parts.map (fun p=>nodeEnc p.output)).getD j []
  digMsg (upsertJobId tau j) bytes.length ((sha256 bytes).map UInt8.toNat)

@[simp] theorem nativeJobMessage_zero (run : TreeRun) (v : Bytes) (tau : Nat) :
    nativeJobMessage run v tau 0=digMsg (upsertJobId tau 0) v.length ((sha256 v).map UInt8.toNat) := rfl

theorem nativeJobMessage_part {run : TreeRun} (v : Bytes) (tau : Nat) {k : Nat} {p : TreePart}
    (hp : run.parts[k]?=some p) :
    nativeJobMessage run v tau (k+1)=digMsg (upsertJobId tau (k+1))
      (nodeEnc p.output).length ((sha256 (nodeEnc p.output)).map UInt8.toNat) := by
  simp [nativeJobMessage,List.getD_eq_getElem?_getD,List.getElem?_map,hp]

private theorem from_expected (tau start : Nat) (xs : List Bytes) :
    Sha.Gen.expectedDigests (upsertShaFrom tau start xs)=
      (List.range xs.length).map (fun i=>digMsg (upsertJobId tau (start+i))
        (xs.getD i []).length ((sha256 (xs.getD i [])).map UInt8.toNat)) := by
  induction xs generalizing start with
  | nil=>rfl
  | cons x xs ih=>
    change (digMsg (upsertJobId tau start) (x.map UInt8.toNat).length
      ((sha256 ((x.map UInt8.toNat).map UInt8.ofNat)).map UInt8.toNat))::
      Sha.Gen.expectedDigests (upsertShaFrom tau (start+1) xs)=_
    rw [nativeBytes_roundtrip,List.length_map,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
      List.getD_cons_zero,List.getD_cons_succ,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    congr 2
    omega

/-- Exact whole native SHA batch, retaining every message and its occurrence. -/
theorem nativeJobMessages_batch (run : TreeRun) (v : Bytes) (tau : Nat) :
    Sha.Gen.expectedDigests (upsertShaJobs tau v run)=
      (List.range (run.parts.length+1)).map (nativeJobMessage run v tau) := by
  unfold upsertShaJobs
  rw [from_expected]
  simp only [List.length_cons,List.length_map,nativeJobMessage,Nat.zero_add]
  rfl

end ZkFormal.NearV3.Assembly
