import ZkFormal.NearV3.Assembly.UpsertShaJobs
import ZkFormal.Sha.Complete.Pad

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Sha.Gen ZkFormal.Sha.Complete

/-- Exact physical SHA rows, including one start row for every message. -/
theorem sha_message_rows (M : Msg) : (msgRows M).length=1+17*nb M := by
  rw [msgRows_eq]; simp

/-- At most72 padding bytes per message; every block occupies17 rows. -/
theorem sha_message_row_cost (M : Msg) :
    64*(msgRows M).length≤17*M.bytes.length+1288 := by
  have hp := nb_eq M
  have hz : (119-M.bytes.length%64)%64<64 := Nat.mod_lt _ (by decide)
  rw [sha_message_rows]
  omega

theorem sha_rows_cost (msgs : List Msg) :
    64*(honestRows msgs).length≤
      17*(msgs.map (fun M => M.bytes.length)).sum+1288*msgs.length := by
  induction msgs with
  | nil => simp [honestRows]
  | cons M ms ih =>
    have hm := sha_message_row_cost M
    simp only [honestRows,List.flatMap_cons,List.length_append] at ih ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- This only discharges the SHA arithmetic once the concrete total-byte and
message charges are established; it is not a native accepted-input budget. -/
theorem sha_rows_fit_of_cost {msgs : List Msg}
    (hc : 17*(msgs.map (fun M => M.bytes.length)).sum+1288*msgs.length≤64*2^22) :
    (honestRows msgs).length≤2^22 := by
  have h := sha_rows_cost msgs
  omega

/-- Exact concrete upsert preimage cost substituted into the physical row bound. -/
theorem upsertShaJobs_row_cost (tau : Nat) (v : NearSpec.Bytes) (run : Render.UpsGen.TreeRun) :
    64*(honestRows (upsertShaJobs tau v run)).length≤
      17*(v.length+(run.parts.map (fun p => (nodeEnc p.output).length)).sum)+
        1288*(run.parts.length+1) := by
  simpa only [upsertShaJobs_byte_count,upsertShaJobs_length] using sha_rows_cost (upsertShaJobs tau v run)

end ZkFormal.NearV3.Assembly
