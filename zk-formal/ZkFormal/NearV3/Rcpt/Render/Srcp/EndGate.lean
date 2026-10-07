import ZkFormal.NearV3.Rcpt.Render.Srcp.Last

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

theorem cell_gz (bs : List SrcpB) (r : Nat) :
    cell bs r SrcpV3.gz = if r + 1 = R bs then 1 else 0 := by
  by_cases hr : r < R bs
  · by_cases he : r + 1 = R bs <;> simp [cell, hr, rowFrame, SrcpV3.gz, Frame.cell, he]
  · have he : r + 1 ≠ R bs := by omega
    simp [cell, hr, SrcpV3.gz, SrcpV3.sz, he]

theorem frame_active (B : SrcpB) (z : Nat) (k : Kind) :
    (frame B z k).rt.toNat + (frame B z k).sg.toNat = 1 := by
  cases k <;> rfl

theorem cell_active (bs : List SrcpB) (r : Nat) :
    cell bs r SrcpV3.rt + cell bs r SrcpV3.sg = if r < R bs then 1 else 0 := by
  by_cases hr : r < R bs
  · simp only [cell, hr, ite_true, rowFrame]
    exact frame_active _ _ _
  · simp [cell, hr, SrcpV3.rt, SrcpV3.sg, SrcpV3.sz]

theorem cell_active_int (bs : List SrcpB) (r : Nat) :
    (cell bs r SrcpV3.rt : Int) + (cell bs r SrcpV3.sg : Int) =
      if r < R bs then 1 else 0 := by
  have hh := congrArg (fun n : Nat => (n : Int)) (cell_active bs r)
  by_cases hr : r < R bs <;> simpa [hr] using hh

/-- The single SIZE gate implies a complete segment end. -/
theorem end_gate_sl {bs : List SrcpB} (h : SrcpWf bs) (r : Nat) :
    (cell bs r SrcpV3.gz : Int) * (1 - (cell bs r SrcpV3.sl : Int)) = 0 := by
  by_cases he : r + 1 = R bs
  · have hr : r = R bs - 1 := by omega
    subst r
    rw [(last_cells h).2.2.1]
    simp
  · rw [cell_gz, if_neg he]
    simp

/-- SIZE can only be followed by inactive padding on a physical transition. -/
theorem end_gate_next (bs : List SrcpB) (H r : Nat) (hr : r < H) :
    (if r + 1 = H then 0 else 1 : Int) * (cell bs r SrcpV3.gz : Int) *
      ((cell bs ((r + 1) % H) SrcpV3.rt : Int) +
        (cell bs ((r + 1) % H) SrcpV3.sg : Int)) = 0 := by
  by_cases hl : r + 1 = H
  · simp [hl]
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm, cell_active_int, cell_gz]
    by_cases he : r + 1 = R bs <;> simp [hl, he]

/-- Before SIZE is emitted, each segment end has an active successor. -/
theorem end_gate_continue (bs : List SrcpB) (H r : Nat) (hr : r < H) :
    (if r + 1 = H then 0 else 1 : Int) * (cell bs r SrcpV3.sl : Int) *
      (1 - (cell bs r SrcpV3.gz : Int)) *
      (1 - ((cell bs ((r + 1) % H) SrcpV3.rt : Int) +
        (cell bs ((r + 1) % H) SrcpV3.sg : Int))) = 0 := by
  by_cases hl : r + 1 = H
  · simp [hl]
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm, cell_active_int, cell_gz]
    by_cases ha : r + 1 < R bs
    · simp [ha]
    · by_cases he : r + 1 = R bs
      · simp [he]
      · have hp : R bs ≤ r := by omega
        simp [ha, he, padding_cell hp, SrcpV3.sl, SrcpV3.sz]

/-- Inactive padding never becomes active before physical wraparound. -/
theorem padding_next (bs : List SrcpB) (H r : Nat) (hr : r < H) :
    (if r + 1 = H then 0 else 1 : Int) *
      (1 - ((cell bs r SrcpV3.rt : Int) + (cell bs r SrcpV3.sg : Int))) *
      ((cell bs ((r + 1) % H) SrcpV3.rt : Int) +
        (cell bs ((r + 1) % H) SrcpV3.sg : Int)) = 0 := by
  by_cases hl : r + 1 = H
  · simp [hl]
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm, cell_active_int, cell_active_int]
    by_cases ha : r < R bs
    · simp [ha]
    · have hn : ¬ r + 1 < R bs := by omega
      simp [ha, hn]

end ZkFormal.NearV3.Render.SrcpGen
