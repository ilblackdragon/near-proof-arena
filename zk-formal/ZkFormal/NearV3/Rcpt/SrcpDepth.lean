import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofInputWf
import ZkFormal.NearV3.Rcpt.Candidates.SourceCount
import ZkFormal.NearV3.Rcpt.Candidates.SourceBudget

/-!
# ZkFormal.NearV3.Rcpt.SrcpDepth — the source Merkle-path budget `Dp0` (RelD0a A10)

RelD0a's conjunct A10 (`w.path_depth`, `NearSpecV3.a10`, user decision 2026-10-09) bounds the
Merkle path of every used source receipt proof by `Dp0` items. This module derives `Dp0` and
discharges the `srcpV3` height obligation from it.

**Rows.** `srcpV3` spends, per used proof (list `j`), one root row, a 32-row leaf segment and
one 64-row segment per path item (`SrcpGen.R_eq`: exactly `srcpRows`, no spare rows):
`srcpRows bs = Σ_j (33 + 64·|path_j|)`. With at most `1984 = 31·64` used proofs
(`Rcpt.Candidates.usedProofs_count`, `prepD0_source_count`) and every path `≤ D`:
`srcpRows ≤ 1984·(33 + 64·D)`.

* `D = 32`: `1984 · 2081 = 4,128,704 ≤ 2^22 = 4,194,304` (margin 65,600 rows);
* `D = 33`: `1984 · 2145 = 4,255,680 > 2^22`.

So **`Dp0 = 32` is the largest depth that keeps `srcpV3` within `2^22`** (`dp0_largest`; the
design's rounder estimate `1984·(2 + D)·64` would give 31). It is `≥ 16`, and nearcore's
producer emits `⌈log₂ #shards⌉ ≤ 6` items at `≤ 64` shards.

**Other budgets at `Dp0`.** Receipt-side SHA rows (`rcptShaRows`, A1 worst case, 35 rows per
64-byte path message) `3,501,199 < 2^22` (`rcptSha_A10`); the source-only SHA rows
`2,257,792 < 2^22` (one SHA table, `sourceSha_A10`); SHA message indices `K_SRC + 16·q` with
`q ≤ 1984·33 = 65,472` segments (`srcpSegments_A10`). The `8 MiB` proof-size model already
counts `srcpV3` at its aligned cap `2^22` (`Size.V3.paddedTwoShaS`), so `Dp0` does not change
the aligned bound.
-/

namespace ZkFormal.NearV3.Rcpt.SrcpDepth

open NearSpec NearSpecV3 ZkFormal.NearV3.Render.SrcpGen

/-- Used source proofs per claim (`31` source blocks × `64` slots). -/
def maxLists : Nat := 1984

/-- `srcpV3` rows at `L` lists of path depth `≤ D`. -/
def srcpRowsMax (L D : Nat) : Nat := L * (33 + 64 * D)

theorem srcpRows_le (bs : List SrcpB) (D : Nat) (hd : ∀ B ∈ bs, B.path.length ≤ D) :
    srcpRows bs ≤ srcpRowsMax bs.length D := by
  induction bs with
  | nil => simp [srcpRows, srcpRowsMax]
  | cons B rest ih =>
    have h1 := hd B (by simp)
    have h2 := ih (fun B' hB' => hd B' (by simp [hB']))
    simp only [srcpRows, srcpRowsMax, List.map_cons, List.sum_cons, List.length_cons] at *
    have : 64 * B.path.length ≤ 64 * D := Nat.mul_le_mul_left _ h1
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **The derivation of `Dp0`**: the largest depth whose worst case fits `2^22` rows. -/
theorem dp0_largest : srcpRowsMax maxLists Dp0 = 4128704 ∧ srcpRowsMax maxLists Dp0 ≤ 2 ^ 22 ∧
    2 ^ 22 < srcpRowsMax maxLists (Dp0 + 1) ∧ 16 ≤ Dp0 ∧ Dp0 = 32 := by decide

theorem srcpRows_replicate (n : Nat) (B : SrcpB) :
    srcpRows (List.replicate n B) = srcpRowsMax n B.path.length := by
  induction n with
  | zero => simp [srcpRows, srcpRowsMax]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [srcpRows, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    unfold srcpRowsMax
    rw [Nat.add_comm]
    exact (Nat.succ_mul n _).symm

/-- The worst case at `Dp0 + 1` is attained: `1984` lists, each with `33` path items. -/
theorem dp0_tight : 2 ^ 22 <
    srcpRows (List.replicate maxLists { (default : SrcpB) with path := List.replicate (Dp0 + 1) default }) := by
  rw [srcpRows_replicate, List.length_replicate]
  exact dp0_largest.2.2.1

/-- The deployed `srcpV3` cap is `2^22`. -/
theorem srcp_cap : SrcpV3.maxLog = 22 := rfl

/-- **`srcpV3` height from A10**: at most `1984` lists, every path `≤ Dp0` ⇒ `≤ 2^maxLog`. -/
theorem srcpRows_le_A10 (bs : List SrcpB) (hl : bs.length ≤ maxLists)
    (hd : ∀ B ∈ bs, B.path.length ≤ Dp0) : srcpRows bs ≤ 2 ^ SrcpV3.maxLog := by
  have h1 := srcpRows_le bs Dp0 hd
  have h2 : srcpRowsMax bs.length Dp0 ≤ srcpRowsMax maxLists Dp0 :=
    Nat.mul_le_mul_right _ hl
  have h3 := dp0_largest.2.1
  rw [srcp_cap]
  omega

/-- The compiled source blocks keep each proof's path length. -/
theorem blocksOfProofs_path (xs : List ProofInput) :
    ∀ B ∈ blocksOfProofs xs, ∃ x ∈ xs, B.path.length = x.entry.proof.path.length := by
  intro B hB
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hB
  rw [blocksOfProofs_get xs i hi]
  have hi' : i < xs.length := by simpa using hi
  exact ⟨xs[i], List.getElem_mem hi', by simp [blockOfProof]⟩

/-- **The `ProofInputsOk.rows` obligation from A10** (and the 1984-list envelope). -/
theorem proofInputs_rows_A10 (xs : List ProofInput) (hl : xs.length ≤ maxLists)
    (hd : ∀ x ∈ xs, x.entry.proof.path.length ≤ Dp0) :
    srcpRows (blocksOfProofs xs) ≤ 2 ^ SrcpV3.maxLog := by
  apply srcpRows_le_A10 _ (by simpa using hl)
  intro B hB
  obtain ⟨x, hx, he⟩ := blocksOfProofs_path xs B hB
  rw [he]
  exact hd x hx

/-- A10 unfolded: every used source proof's path is `≤ Dp`. -/
theorem a10_paths {Dp : Nat} {cb wb : Bytes} {k : WalkD0} {sw : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok sw) (h : a10 Dp cb wb = true) :
    ∀ e ∈ usedProofs k sw, e.proof.path.length ≤ Dp := by
  unfold a10 at h
  rw [hk, hw] at h
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

/-- Every RelD0a witness: used source paths are `≤ Dp0`. -/
theorem relD0a_paths {B : Nat} {cb wb : Bytes} {k : WalkD0} {sw : StateWitness}
    (h : RelD0a B cb wb) (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok sw) :
    ∀ e ∈ usedProofs k sw, e.proof.path.length ≤ Dp0 :=
  a10_paths hk hw h.2.2.2.2.2.2.2

/-- Receipt-side SHA rows at the A1 worst case with depth `Dp0` fit one SHA table. -/
theorem rcptSha_A10 : rcptShaRows 4481 maxLists Dp0 = 3501199 ∧
    rcptShaRows 4481 maxLists Dp0 + 1 ≤ 2 ^ 22 := by decide

/-- Source-proof SHA rows alone (leaf rehash + `Dp0` path messages per list). -/
theorem sourceSha_A10 : Candidates.sourceShaFor maxLists (maxLists * Dp0) = 2257792 ∧
    Candidates.sourceShaFor maxLists (maxLists * Dp0) ≤ 2 ^ 22 := by decide

/-- Source message segments (leaf + path items) stay far below the `2^22` id index space. -/
theorem srcpSegments_A10 : maxLists * (1 + Dp0) = 65472 ∧ maxLists * (1 + Dp0) < 2 ^ 22 := by
  decide

end ZkFormal.NearV3.Rcpt.SrcpDepth
