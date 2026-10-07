import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficActive

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- The final active row emits the complete natural SIZE sum, without reduction bounds. -/
theorem size_row_messages {bs : List SrcpB} (h : SrcpWf bs) (r : Nat) (sd : Bool) :
    rowN (cell bs r) B_SIZE sd =
      if sd = true ∧ r = R bs - 1 then [[2, srcpSize bs]] else [] := by
  have hp := R_pos h
  by_cases hr : r = R bs - 1
  · subst r
    have he : R bs - 1 + 1 = R bs := by omega
    simp [rowN, B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC, cell_gz, he, last_size_cell h]
  · have he : r + 1 ≠ R bs := by omega
    simp [rowN, B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC, cell_gz, he, hr]

/-- SIZE is emitted exactly once, including when the active rows fill the trace. -/
theorem size_messages {bs : List SrcpB} (h : SrcpWf bs) (H : Nat) (hH : R bs ≤ H) (sd : Bool) :
    (List.range H).flatMap (fun r => rowN (cell bs r) B_SIZE sd) =
      if sd = true then [[2, srcpSize bs]] else [] := by
  have hr : (fun r => rowN (cell bs r) B_SIZE sd) =
      (fun r => if sd = true ∧ r = R bs - 1 then [[2, srcpSize bs]] else []) := by
    funext r; exact size_row_messages h r sd
  rw [hr]
  cases sd
  · simp
  · simp only [true_and, ite_true]
    apply flatMap_at
    have := R_pos h; omega

end ZkFormal.NearV3.Render.SrcpGen
