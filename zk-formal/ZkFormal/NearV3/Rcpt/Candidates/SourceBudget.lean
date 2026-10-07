import ZkFormal.NearV3.Rcpt.ShaRows
import ZkFormal.Algebra.Fp

/-! Isolated budget arithmetic. No active table or verifier parameter is changed.
Encoding coverage and list-count derivations are separate semantic obligations. -/
namespace ZkFormal.NearV3.Rcpt.Candidates

abbrev witnessBytes : Nat := 8388608
abbrev sourceLists : Nat := 1984
abbrev distinctPathItems : Nat := witnessBytes / 33

def sourceRowsFor (lists paths : Nat) : Nat := 33 * lists + 64 * paths
def sourcePreimagesFor (lists paths : Nat) : Nat := 32 * lists + 64 * paths
def sourceShaFor (lists paths : Nat) : Nat := lists * msgRows 32 + paths * msgRows 64

/-- Every 33-byte path item charged to the witness has this global distinct-item bound. -/
theorem encoded_paths_bound (d : Nat) (h : 33 * d ≤ witnessBytes) : d ≤ distinctPathItems := by
  simp only [sourceLists, distinctPathItems, witnessBytes] at *
  omega

/-- Replaying the same last-wins proof at each occurrence incurs the multiplicity factor. -/
theorem occurrence_bounds (L d : Nat) (hL : L ≤ sourceLists) (hd : d ≤ distinctPathItems) :
    L * d ≤ 504332800 ∧ sourceRowsFor L (L * d) ≤ 32277364672 ∧
    sourcePreimagesFor L (L * d) ≤ 32277362688 ∧ sourceShaFor L (L * d) ≤ 17651683712 := by
  have hm := Nat.mul_le_mul hL hd
  simp only [sourceRowsFor, sourcePreimagesFor, sourceShaFor, msgRows] at *
  simp only [sourceLists, distinctPathItems, witnessBytes] at *
  omega

/-- A deduplicated source proof lane avoids occurrence multiplication, but still needs
more than one table at the current field's rate-1/16 maximum trace size. -/
theorem unique_bounds (L d : Nat) (hL : L ≤ sourceLists) (hd : d ≤ distinctPathItems) :
    sourceRowsFor L d ≤ 16334272 ∧ sourcePreimagesFor L d ≤ 16332288 ∧
    sourceShaFor L d ≤ 8932712 := by
  simp only [sourceRowsFor, sourcePreimagesFor, sourceShaFor, msgRows]
  simp only [sourceLists, distinctPathItems, witnessBytes] at *
  omega

theorem budget_values : distinctPathItems = 254200 ∧
    sourceRowsFor sourceLists (sourceLists * distinctPathItems) = 32277364672 ∧
    sourcePreimagesFor sourceLists (sourceLists * distinctPathItems) = 32277362688 ∧
    sourceShaFor sourceLists (sourceLists * distinctPathItems) = 17651683712 ∧
    sourceRowsFor sourceLists distinctPathItems = 16334272 ∧
    sourcePreimagesFor sourceLists distinctPathItems = 16332288 ∧
    sourceShaFor sourceLists distinctPathItems = 8932712 := by decide

/-- The per-occurrence envelope requires log35 source and SHA tables, exceeding the
field and existing message-id representation; a cap increase alone is insufficient. -/
theorem occurrence_capacity :
    2 ^ 34 < 32277364672 ∧ 32277364672 ≤ 2 ^ 35 ∧
    2 ^ 34 < 17651683712 ∧ 17651683712 ≤ 2 ^ 35 ∧
    ZkFormal.Algebra.P < 16 * (sourceLists * (1 + distinctPathItems)) := by decide

/-- Dedup needs log24 if unsplit. Two log23 partitions fit each source-only row envelope,
with log27 LDE at blowup16. Other SHA work still must be added before admission. -/
theorem unique_capacity :
    2 ^ 23 < 16334272 ∧ 16334272 ≤ 2 * 2 ^ 23 ∧
    2 ^ 23 < 8932712 ∧ 8932712 ≤ 2 * 2 ^ 23 ∧
    23 + 4 = ZkFormal.Algebra.Fp.twoAdicity ∧ 27 < 24 + 4 := by decide

/-- Add the existing non-source receipt and trie envelopes (B0=1,998,836) to the
unique source envelope. This retains all old A1 bounds but drops the unproved depth-six assumption. -/
theorem unique_total_sha_budget :
    trieShaRows 1998836 + (rcptShaRows 4481 sourceLists 0 - sourceLists * msgRows 32) +
      sourceShaFor sourceLists distinctPathItems = 12674664 ∧
    12674664 ≤ 2 * 2 ^ 23 := by decide

end ZkFormal.NearV3.Rcpt.Candidates
