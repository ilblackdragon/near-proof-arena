/-!
# ZkFormal.NearV3.Rcpt.ShaRows — SHA rows of the receipt side (A1), single- or two-table

An L5 SHA message of `len` bytes takes `1 + 17·⌈(len + 9)/64⌉` rows (start row, 17 rows per
block).  The receipt side hashes, for `n` applied receipts, `L` applied source lists and path
depth `d` (worst-case lengths of D0: account ids `≤ 64` bytes, `kt ≤ 1`, so a receipt's borsh is
`≤ 347` bytes):

* `RC(j)` (`12 + Σ borsh`): `≤ L + 17·⌊(84·L + 347·n)/64⌋` rows in total;
* `PEO(r)` (`≤ 133` bytes): 52 rows; `LEAF(r)` (68): 35; `RID(r)` (48): 18; `VPOST` of each
  written account (72): 35; outcome tree (`mrk`, `n − 1` nodes of 64 bytes): 35 each;
* `srcp`: per list the leaf rehash (32 bytes, 18 rows) and `d` path messages (64 bytes, 35 each).

The routing to an SHA instance is a bus choice of the assembly; these counts do not depend on
it.  With **one** shared SHA table the budget is `trie (5/4·B0) + rcptShaRows ≤ 2^22`.
-/

namespace ZkFormal.NearV3.Rcpt

/-- Rows of one SHA message of `len` bytes. -/
def msgRows (len : Nat) : Nat := 1 + 17 * ((len + 9 + 63) / 64)

/-- Upper bound on the receipt-side SHA rows. -/
def rcptShaRows (n L d : Nat) : Nat :=
  (L + 17 * ((84 * L + 347 * n) / 64)) +          -- RC(j)
  n * (msgRows 133 + msgRows 68 + msgRows 48 + msgRows 72) +   -- PEO, LEAF, RID, VPOST
  (n - 1) * msgRows 64 +                           -- outcome tree
  L * (msgRows 32 + d * msgRows 64)                -- srcp

/-- Trie side as budgeted by the spec lane (`1.25` SHA rows per unfolded byte). -/
def trieShaRows (B0 : Nat) : Nat := B0 * 5 / 4

/-- The single-table row budget. -/
def singleShaOk (B0 n L d : Nat) : Bool := decide (trieShaRows B0 + rcptShaRows n L d ≤ 2 ^ 22)

theorem msgRows_vals : msgRows 133 = 52 ∧ msgRows 68 = 35 ∧ msgRows 48 = 18 ∧ msgRows 72 = 35 ∧
    msgRows 64 = 35 ∧ msgRows 32 = 18 := by decide

/-- A1 worst case: `n = 4481`, `L = 31·64 = 1984` lists, path depth `6` (`≤ 64` shards). -/
theorem rcptShaRows_A1 : rcptShaRows 4481 1984 6 = 1695759 := by decide

/-- With `B0 = 2,000,000` one table overflows by 1,455 rows at this worst case … -/
theorem single_2M_fails : singleShaOk 2000000 4481 1984 6 = false := by decide

/-- … and fits for `B0 = 1,998,836`. -/
theorem single_fits : singleShaOk 1998836 4481 1984 6 = true := by decide
theorem single_tight : singleShaOk 1998837 4481 1984 6 = false := by decide

end ZkFormal.NearV3.Rcpt
