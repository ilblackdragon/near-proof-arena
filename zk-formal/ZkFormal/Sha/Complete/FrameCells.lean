import ZkFormal.Sha.Complete.Help
import ZkFormal.Sha.Complete.Pad

/-!
# ZkFormal.Sha.Complete.FrameCells — framing cells of the honest rows

The framing columns (`F`, `Fprev`, `Nd`, `Last`, `P80`, `Seen`, `Pn`,
`Dmult`) of round / digest / start rows of a block `blkOf M b`, as
`if (arithmetic condition) then 1 else 0`, and the arithmetic facts about
`len`, `b`, `nb M` they are checked against.
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

@[simp] theorem blkOf_idx (M : Msg) (b : Nat) : (blkOf M b).idx = b := rfl
@[simp] theorem blkOf_len (M : Msg) (b : Nat) : (blkOf M b).len = M.bytes.length := rfl
@[simp] theorem blkOf_id (M : Msg) (b : Nat) : (blkOf M b).id = M.id := rfl
@[simp] theorem blkOf_nblk (M : Msg) (b : Nat) : (blkOf M b).nblk = nb M := rfl
@[simp] theorem blkOf_dmult (M : Msg) (b : Nat) : (blkOf M b).dmult = M.dmult := rfl

section
variable (M : Msg) (b j : Nat)

theorem r_F (q : Nat) (hq : q < 16) : roundCell j (blkOf M b) (colF q) =
    if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 := by
  rw [rc_F j _ q hq]
  by_cases h1 : j < 4 <;> by_cases h2 : 64 * b + (16 * j + q) < M.bytes.length <;> simp [Blk.isData, h1, h2]

theorem r_Fprev : roundCell j (blkOf M b) colFprev =
    if j = 0 then 1 else if j < 4 ∧ 64 * b + (16 * j - 1) < M.bytes.length then 1 else 0 := by
  rw [rc_Fprev]
  by_cases h1 : j < 4 <;> by_cases h2 : 64 * b + (16 * j - 1) < M.bytes.length <;> simp [Blk.isData, h1, h2]

theorem r_Nd : roundCell j (blkOf M b) colNd = min M.bytes.length (64 * b + 16 * (min j 3 + 1)) := by
  rw [rc_Nd]; rfl

theorem r_Last : roundCell j (blkOf M b) colLast = if b + 1 = nb M then 1 else 0 := by
  rw [rc_Last]; simp [Blk.last]

theorem r_P80 : roundCell j (blkOf M b) colP80 =
    if 64 * b ≤ M.bytes.length ∧ M.bytes.length < 64 * b + 64 then 1 else 0 := by
  rw [rc_P80]
  by_cases h1 : 64 * b ≤ M.bytes.length <;> by_cases h2 : M.bytes.length < 64 * b + 64 <;> simp [Blk.p80, h1, h2]

theorem r_Seen : roundCell j (blkOf M b) colSeen = if M.bytes.length < 64 * b then 1 else 0 := by
  rw [rc_Seen]
  by_cases h1 : M.bytes.length < 64 * b <;> simp [Blk.seen, h1]

theorem r_Pn : roundCell j (blkOf M b) colPn =
    if (64 * b ≤ M.bytes.length ∧ M.bytes.length < 64 * b + 64) ∧ ¬ (b + 1 = nb M) then 1 else 0 := by
  rw [rc_Pn]
  by_cases h1 : 64 * b ≤ M.bytes.length <;> by_cases h2 : M.bytes.length < 64 * b + 64 <;>
    by_cases h3 : b + 1 = nb M <;> simp [Blk.p80, Blk.last, h1, h2, h3]

theorem d_Nd : digestCell (blkOf M b) colNd = min M.bytes.length (64 * b + 64) := by
  rw [dc_Nd]; rfl

theorem d_Last : digestCell (blkOf M b) colLast = if b + 1 = nb M then 1 else 0 := by
  rw [dc_Last]; simp [Blk.last]

theorem d_P80 : digestCell (blkOf M b) colP80 =
    if 64 * b ≤ M.bytes.length ∧ M.bytes.length < 64 * b + 64 then 1 else 0 := by
  rw [dc_P80]
  by_cases h1 : 64 * b ≤ M.bytes.length <;> by_cases h2 : M.bytes.length < 64 * b + 64 <;> simp [Blk.p80, h1, h2]

theorem d_Seen : digestCell (blkOf M b) colSeen = if M.bytes.length < 64 * b then 1 else 0 := by
  rw [dc_Seen]
  by_cases h1 : M.bytes.length < 64 * b <;> simp [Blk.seen, h1]

theorem d_Pn : digestCell (blkOf M b) colPn =
    if (64 * b ≤ M.bytes.length ∧ M.bytes.length < 64 * b + 64) ∧ ¬ (b + 1 = nb M) then 1 else 0 := by
  rw [dc_Pn]
  by_cases h1 : 64 * b ≤ M.bytes.length <;> by_cases h2 : M.bytes.length < 64 * b + 64 <;>
    by_cases h3 : b + 1 = nb M <;> simp [Blk.p80, Blk.last, h1, h2, h3]

theorem d_Dmult : digestCell (blkOf M b) colDmult = if b + 1 = nb M ∧ M.dmult = true then 1 else 0 := by
  rw [dc_Dmult]; simp [Blk.last]
end

theorem s_zero (id c : Nat) (h1 : 256 ≤ c) (h2 : c ≠ colS) (h3 : c ≠ colId) : startCell id c = 0 :=
  sc_other id c h1 h2 h3

/-- Row shapes appearing as the current row of a step. -/
inductive CurRow : Row → Prop
  | start (M : Msg) (hM : MOk M) : CurRow (.start M.id)
  | round (M : Msg) (b j : Nat) (hM : MOk M) (hb : b < nb M) (hj : j < 16) : CurRow (.round j (blkOf M b))
  | digest (M : Msg) (b : Nat) (hM : MOk M) (hb : b < nb M) : CurRow (.digest (blkOf M b))
  | pad : CurRow .pad

theorem curRow_of_step (cur nx : Row) (hs : Step cur nx) : CurRow cur := by
  cases hs with
  | start M hM => exact .start M hM
  | round M b j hM hb hj => exact .round M b j hM hb (by omega)
  | r15 M b hM hb => exact .round M b 15 hM hb (by decide)
  | dnext M b hM hb => exact .digest M b hM (by omega)
  | dlast M b hM hb _ _ => exact .digest M b hM (by omega)
  | pad _ _ => exact .pad

/-! ## Counting data flags -/

theorem count_lt (a L : Nat) : ∀ n,
    ((List.range n).map fun q => ((if a + q < L then 1 else 0 : Nat) : Int)).sum = (min n (L - a) : Nat)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, count_lt a L n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split <;> omega

end ZkFormal.Sha.Complete
