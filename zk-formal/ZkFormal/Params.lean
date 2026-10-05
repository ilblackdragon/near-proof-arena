/-!
# ZkFormal.Params — the security budget is a kernel `Nat` check

The admission type demands `num * 2^targetBits ≤ den` for the certified
bound `num/den`, decided by the kernel (`decide +kernel`, never
`native_decide`).  This file checks the dominant terms of the proposed
parameter sets (DESIGN.md §8) with the kernel's GMP-backed `Nat` arithmetic
on numbers of ~10^4 bits.  Each check takes milliseconds.

Common parameters (rate 1/16, largest LDE domain `n = 2^26`, degree bound
`D = 2^22`):
* query phase: `k` oracle answers ("chunks"), each giving 9 positions of 26
  bits (234 ≤ 256 bits).  A chunk is good for a cheating prover iff its 9
  positions lie in the agreement set, of size at most `n - e`, so
  `g = (n - e)^9 · 2^(256-234)` of the `2^256` answers are good.
* query-phase queries: adversary `2^64`, honest prover `2^40 · k`,
  verifier `k`.
* commit phase: single-answer challenges in `K = F_p^8` (BabyBear), each bad
  for at most `2^36 · 3^8` of the `2^256` answers (≤ 2^36 bad field
  elements — the largest is the multiset-fingerprint round, degree
  ≤ #messages × width — and ≤ 3^8 hash preimages per field element), over all
  `2^64 + 2^40·64 + 64` challenge queries.
* wide-digest (512-bit) collisions and inversions: `≤ 2^3 · Q²` pair events
  at `2^-512` each, `Q ≤ 2^70` oracle queries in total.
-/

namespace ZkFormal.Params

def n : Nat := 2 ^ 26
def D : Nat := 2 ^ 22
def qCommit : Nat := 2 ^ 64 + 2 ^ 40 * 64 + 64
def qAll : Nat := 2 ^ 70
def commitBad : Nat := 2 ^ 36 * 3 ^ 8

/-- Query-phase queries for `k` chunks per proof. -/
def qQuery (k : Nat) : Nat := 2 ^ 64 + 2 ^ 40 * k + k

/-- Total bound `num / den` over the common denominator `(2^256)^k · 2^512`,
for agreement radius `e` and `k` chunks. -/
def den (k : Nat) : Nat := (2 ^ 256) ^ k * 2 ^ 512
def num (e k : Nat) : Nat :=
  qQuery k * ((n - e) ^ 9 * 2 ^ (256 - 234)) ^ k * 2 ^ 512 +   -- query phase
  qCommit * commitBad * (2 ^ 256) ^ (k - 1) * 2 ^ 512 +         -- commit-phase challenges
  8 * qAll * qAll * (2 ^ 256) ^ k                               -- wide-digest pair events

/-! ### Target: unique-decoding radius `e = (n - D)/2`, 216 queries -/

def e2 : Nat := (n - D) / 2

theorem udr2_ok : num e2 24 * 2 ^ 128 ≤ den 24 := by decide +kernel

/-- Margin: the bound is below `2^-132`. -/
theorem udr2_margin : num e2 24 * 2 ^ 132 ≤ den 24 := by decide +kernel

/-- 207 queries (23 chunks) would not reach the target. -/
theorem udr2_207_fails : ¬ (num e2 23 * 2 ^ 128 ≤ den 23) := by decide +kernel

/-! ### Fallback: elementary `d/3` radius `e = (n - D)/3`, 360 queries -/

def e3 : Nat := (n - D) / 3

theorem udr3_ok : num e3 40 * 2 ^ 128 ≤ den 40 := by decide +kernel

theorem udr3_351_fails : ¬ (num e3 39 * 2 ^ 128 ≤ den 39) := by decide +kernel

/-! ### L3 radius (REQUESTS R-L3-2): `e = (n - D)/2 - 1`

DEEP decoding needs `n - 2e ≥ D + 1`; L3's `RbrWith` instance uses
`agreeUdr = n - ((n - n/16)/2 - 1)`.  The target set still clears 2^-132. -/

def e2' : Nat := (n - D) / 2 - 1

theorem udr2'_ok : num e2' 24 * 2 ^ 128 ≤ den 24 := by decide +kernel

theorem udr2'_margin : num e2' 24 * 2 ^ 132 ≤ den 24 := by decide +kernel

end ZkFormal.Params
