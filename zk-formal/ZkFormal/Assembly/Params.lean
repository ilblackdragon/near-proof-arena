import ZkFormal.Udr.Rbr
import ZkFormal.Bcs.Budget

/-!
# ZkFormal.Assembly.Params — the numeric instantiation of L2's transport bound (lane L7)

`Bcs.Transport.stark_romSound_rbr` bounds the winning probability by
`bcsNum K (bad·Dm) (G^K) … / 2^(256K)` where `G` must dominate
`agree(2^n0)^p · 2^(256 − p·n0)` over every admissible header (`n0` = query-domain
log, `p` = positions per chunk).  This file fixes concrete `G`s and checks the
whole budget with the kernel (`decide +kernel` on `Nat`, no `native_decide`).

Inputs:
* `agree = Udr.agreeUdr 4` (L3, radius `(n − D)/2 − 1`, rate 1/16); the fallback
  radius `(n − D)/3` is `agree3`.
* `bad = Udr.Np.badBudget = 2^36` field elements per round (L3) times the decoder
  fiber `Dm = 2·3^8` (`Bcs.Transport.hdec_deployed`): `bad·Dm ≤ 2^50`.
* `p = 9` positions of `26` bits per chunk; `n0 ≤ 26` on admissible headers.

**Finding (smallest query domains).** `agree(2^q)/2^q = 17/32 + 1/2^q` is largest
for the *smallest* domain.  Admissible headers allow every table height `≥ 2`, so
`n0` can be as small as `5` (`2^1` rows × blowup 16).  With 24 chunks (216
queries) the query-phase term at `n0 ∈ {5, 6, 7}` exceeds `2^-129`
(`udr2_K24_q5_fails`: ≈ 2^-115 at `n0 = 5`), so **the deployed default
`Params` (24 chunks, no lower bound on `n0`) cannot be certified at 2^-128 by
this analysis.**  Either fix works and is kernel-checked below:
* 26 chunks (234 queries), every `n0 ∈ [5, 26]`: `udr2_K26_ok` (≤ 2^-129.2 for the
  query term; proof size +8%);
* 24 chunks with admissible headers restricted to `n0 ≥ 8`: `udr2_K24_min8_ok`.
Fallback radius `(n − D)/3`: 40 chunks (360 queries), every `n0 ∈ [5, 26]`:
`udr3_K40_ok`.
-/

namespace ZkFormal.Assembly

open ArenaCore ArenaCore.Security

/-- Fallback (d/3) agreement bound on a domain of size `n`, rate `2^-b`. -/
def agree3 (logBlowup n : Nat) : Nat := n - (n - n / 2 ^ logBlowup) / 3

/-- Good-answer count of one chunk on a domain of log-size `q`
(9 positions of 26 bits). -/
def chunkGood (agree : Nat → Nat) (q : Nat) : Nat := agree (2 ^ q) ^ 9 * 2 ^ (256 - 9 * q)

/-- Query-phase queries with `K` chunks per proof/verification. -/
def qChunks (K : Nat) : Nat := 2 ^ 64 + 2 ^ 40 * K + K

/-- The budget's query-phase condition (`BudgetStmt`'s `hG`) for `G = g^K`. -/
def QueryOk (K g : Nat) : Prop := g ^ K * qChunks K * 2 ^ 129 ≤ roRange ^ K

/-- `g` dominates the chunk-good count on every domain log in `[lo, 26]`. -/
def Dominates (agree : Nat → Nat) (lo g : Nat) : Prop :=
  ∀ q, q < 27 → lo ≤ q → chunkGood agree q ≤ g

instance (agree : Nat → Nat) (lo g : Nat) : Decidable (Dominates agree lo g) :=
  inferInstanceAs (Decidable (∀ q, q < 27 → lo ≤ q → _))

instance (K g : Nat) : Decidable (QueryOk K g) := inferInstanceAs (Decidable (_ ≤ _))

/-! ## The concrete `G`s (the maximum is attained at the smallest domain) -/

/-- UDR2 (L3 radius), smallest domain `2^5`. -/
def g2_5 : Nat := chunkGood (Udr.agreeUdr 4) 5
/-- UDR2, smallest domain `2^8`. -/
def g2_8 : Nat := chunkGood (Udr.agreeUdr 4) 8
/-- UDR3 fallback, smallest domain `2^5`. -/
def g3_5 : Nat := chunkGood (agree3 4) 5

theorem g2_5_dom : Dominates (Udr.agreeUdr 4) 5 g2_5 := by decide +kernel
theorem g2_8_dom : Dominates (Udr.agreeUdr 4) 8 g2_8 := by decide +kernel
theorem g3_5_dom : Dominates (agree3 4) 5 g3_5 := by decide +kernel

/-! ## Kernel-checked budgets (query-phase term ≤ 2^-129; `budget` adds the rest) -/

/-- **Target, 26 chunks (234 queries), any admissible domain.** -/
theorem udr2_K26_ok : QueryOk 26 g2_5 := by decide +kernel

/-- **Target, 24 chunks (216 queries), domains `≥ 2^8`.** -/
theorem udr2_K24_min8_ok : QueryOk 24 g2_8 := by decide +kernel

/-- The deployed default (24 chunks) fails at the smallest admissible domain `2^5`. -/
theorem udr2_K24_q5_fails : ¬ QueryOk 24 (chunkGood (Udr.agreeUdr 4) 5) := by decide +kernel

/-- … and at `2^7` (so `n0 ≥ 8` is the exact threshold for 24 chunks). -/
theorem udr2_K24_q7_fails : ¬ QueryOk 24 (chunkGood (Udr.agreeUdr 4) 7) := by decide +kernel

/-- **Fallback, d/3 radius, 40 chunks (360 queries), any admissible domain.** -/
theorem udr3_K40_ok : QueryOk 40 g3_5 := by decide +kernel

/-- 39 chunks are not enough for the fallback. -/
theorem udr3_K39_fails : ¬ QueryOk 39 g3_5 := by decide +kernel

/-! ## The commit-phase `bad` -/

/-- Per-round bad count over oracle answers: `2^36` field elements (L3's
`badBudget`) times the challenge-decoder fiber `2·3^8` (L1/L2 `hdec_deployed`). -/
def badAnswers : Nat := 2 ^ 36 * (2 * 3 ^ 8)

theorem badAnswers_le : badAnswers ≤ 2 ^ 50 := by decide

/-! ## The full bound `num · 2^128 ≤ den` -/

/-- Full numeric bound at the profile budgets (2^64 hash, 2^40 prover queries)
for any honest-prover / verifier unit budgets `≤ 2^30` and `K` chunk queries per
proof and per verification. -/
theorem full_ok (K g NPu NVu : Nat) (hK : 2 ≤ K) (hPu : NPu ≤ 2 ^ 30) (hVu : NVu ≤ 2 ^ 30)
    (hq : QueryOk K g) :
    Bcs.bcsNum K badAnswers (g ^ K) (2 ^ 64) (2 ^ 40) NPu NVu K K * 2 ^ 128 ≤ roRange ^ K :=
  Bcs.budget K badAnswers (g ^ K) NPu NVu K K hK badAnswers_le hPu hVu hq

theorem full_K26 (NPu NVu : Nat) (hPu : NPu ≤ 2 ^ 30) (hVu : NVu ≤ 2 ^ 30) :
    Bcs.bcsNum 26 badAnswers (g2_5 ^ 26) (2 ^ 64) (2 ^ 40) NPu NVu 26 26 * 2 ^ 128 ≤ roRange ^ 26 :=
  full_ok 26 g2_5 NPu NVu (by decide) hPu hVu udr2_K26_ok

theorem full_K24_min8 (NPu NVu : Nat) (hPu : NPu ≤ 2 ^ 30) (hVu : NVu ≤ 2 ^ 30) :
    Bcs.bcsNum 24 badAnswers (g2_8 ^ 24) (2 ^ 64) (2 ^ 40) NPu NVu 24 24 * 2 ^ 128 ≤ roRange ^ 24 :=
  full_ok 24 g2_8 NPu NVu (by decide) hPu hVu udr2_K24_min8_ok

theorem full_K40_udr3 (NPu NVu : Nat) (hPu : NPu ≤ 2 ^ 30) (hVu : NVu ≤ 2 ^ 30) :
    Bcs.bcsNum 40 badAnswers (g3_5 ^ 40) (2 ^ 64) (2 ^ 40) NPu NVu 40 40 * 2 ^ 128 ≤ roRange ^ 40 :=
  full_ok 40 g3_5 NPu NVu (by decide) hPu hVu udr3_K40_ok

end ZkFormal.Assembly
