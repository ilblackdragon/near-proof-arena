import NearSpecV3.D2.RuntimeD2

/-!
# Supply: where NEAR can be minted, and the 2.5 %-per-annum inflation bound

Two questions about the D2 runtime as modelled here, and what this module does and does not prove
about them:

1. **Is new NEAR created anywhere other than validator rewards?**
2. **Is the amount created within 2.5 % of the total supply per annum?**

* §1 `Inflation`: the epoch reward formula of `chain/epoch-manager/src/reward_calculator.rs:64-90`,
  proved to mint at most `supply · epoch_duration / (40 · year)` — an annualised 2.5 %
  (`max_inflation_rate = 1/40` from PV 48 on; `core/primitives/res/epoch_configs/mainnet/85.json`,
  which PV 86 also uses). Over a window of at most one year the total minted is at most `1/40` of
  the supply at the end of the window (`≤ 1/39` of the supply at its start). One epoch spanning a
  full year mints exactly `supply/40`, which is what "2.5 % per annum" denotes.
* §2 `Split`: the minted amount splits `10 %` protocol treasury + `90 %` validators
  (`protocol_reward_rate = 1/10`, hardcoded for the production genesis,
  `reward_calculator.rs:64-67`), and the per-validator stake- and uptime-weighted shares, computed
  with floor divisions, sum to at most the validator budget. So neither branch of the split can
  exceed the epoch budget. §2.2 models the uptime clip (`:119-131`) so that the shares' fraction
  bound is *derived* rather than assumed, and proves the accumulator `calculate_reward` returns —
  the value stored as `minted_amount` — equals the ledger total.
* §3 `Header`: `Block::verify_total_supply_checked` (`core/primitives/src/block.rs:315-343`) and the
  `minted_amount` plumbing of `chain/chain/src/chain.rs:2520-2533`. Acceptance forces
  `total_supply(block) = total_supply(prev) + minted − balance_burnt`, and `minted` is `0` unless the
  block starts an epoch: that is the "nowhere else" claim at block granularity.
* §4 is in `NearSpecV3/SupplyRuntime.lean`: the account-level accounting of the runtime's own balance
  writes, where `validatorUpdate` (`D2/Validators.lean:36-67`) is the only write that raises the sum
  of `amount + locked` without a matching debit.

## The named results

| question | theorem |
|----------|---------|
| one epoch mints at most 2.5 % | `epochMint_le_supply_div_40` |
| a full-year epoch mints exactly 2.5 % | `epochMint_full_year` |
| a one-year window mints at most 2.5 % of its end supply | `yearMinted_le_div_40` |
| … i.e. at most 2.56 % of its start supply | `yearMinted_le_start_div_39` |
| mainnet's 7.2 h epoch mints ≤ supply/48666 | `mainnetEpochMint_le_div_48666` |
| treasury + validator shares ≤ the epoch's mint | `treasury_add_shares_le`, `sumValidatorRewards_le_budget` |
| the epoch manager's reward ledger sums to ≤ the mint | `rewardLedger_sum_le_mint` |
| … with the share bound *derived* from the uptime clip | `rewardLedger_sum_le_mint'`, `sumLedgerRows_le_budget` |
| `minted_amount` = the total of the reward map | `epochActualReward_eq_ledger` |
| `minted_amount` ≤ 2.5 % of supply, clip only | `mintedAmount_le_supply_div_40` |
| the rewards credited on one shard ≤ 2.5 % of supply | `creditedRewards_le_supply_div_40` |
| the Rust double floor is the single-floor share | `validatorReward_eq_rust` |
| an accepted header satisfies the supply identity | `verifyTotalSupply_accept` |
| a non-epoch block cannot raise supply | `verifyTotalSupply_nonEpoch_le` |
| an epoch-start block raises supply by ≤ 2.5 % | `verifyTotalSupply_epochStart_le` |
| a run's final supply = start + mints − burns | `supplyRun_conservation` |
| a one-year run raises supply by ≤ 2.5 % | `supplyRun_year_increase_le` |
| the validator update raises an account by its reward | `SupplyRuntime.validatorStep_total` |
| every other balance write conserves or burns | `SupplyRuntime.stakeStep_total`, `fromGasKeyStep_total`, … |

## What this module does **not** prove (read before quoting it)

* **The chunk statement does not carry `total_supply`.** `decodeBlockV6` (`Wire.lean:306`) decodes the
  header field and discards it, and `checkD2CoreObs` (`ChunkValidationD2.lean:115-295`, the burnt comparison at `:260`) compares
  `H.prevBalanceBurnt` against the computed burnt amount but nothing about supply. `Rel_D2` therefore
  authenticates the *burnt* half of the supply identity and not the *minted* half. §3 models the
  block-level check that supplies the missing half; it is not part of `Rel_D2` yet.
* **The chunk statement does not recompute the reward amounts — and by design cannot.** The
  `validatorRewards` a chunk applies arrive in the claim's facts, and `checkD2CoreObs` only checks that
  a `validatorUpdate` is *present* exactly when the block starts an epoch
  (`ChunkValidationD2.lean:188-190`), not that its amounts equal the epoch's computed ledger. In Rust
  those amounts come from the epoch manager's own `compute_stake_return_info`
  (`chain/chain/src/runtime/mod.rs:238-246`), which returns `EpochInfo.validator_reward` verbatim
  (`chain/epoch-manager/src/lib.rs:1274`). The claim carries no production stats, `total_supply` or
  `epoch_duration`, so the ledger **cannot be recomputed from claim bytes**; `spec/claim-v3.md` classes
  `validator_update` as trusted (`T10`) and says `Rel` "can only check the trusted values for internal
  consistency; it cannot check that they are true".
  What §2.2 adds is that the arithmetic no longer needs to trust the *shape* of the ledger: the uptime
  clip is modelled, so `Σ rows ≤ validatorBudget mint` is derived rather than assumed, and
  `mintedAmount_le_supply_div_40` / `creditedRewards_le_supply_div_40` bound the minted amount and the
  amount credited on one shard by 2.5 % **whatever** rows the trusted facts carry. The residual gap is
  therefore not arithmetic but the trust boundary itself.
* §1–§2 prove bounds on the *formula*. That the epoch manager's `minted_amount` is produced by this
  formula, and that mainnet takes the hardcoded treasury branch, are facts about
  `reward_calculator.rs` cited here, not modelled in Lean.
* `U256`→`u128` truncation and `checked_*` overflow panics are modelled as plain `Nat` arithmetic
  with explicit `≥ 2^128` guards, as `D2/Validators.lean` does. The epoch-manager's own arithmetic is
  `U256` with a final `.as_u128()` truncation (`reward_calculator.rs:76`), which is a *narrowing* of
  the value proved bounded here.

## Three things "2.5 % per annum" does and does not mean here

* **It is a rate, not a per-epoch cap.** `epoch_duration` is the *measured* timestamp difference since
  the previous epoch's last block (`chain/epoch-manager/src/lib.rs:826-827`), so a long epoch mints
  proportionally more in one go: `epochMint_mul_yearNs` gives `supply/20` for a two-year epoch. What
  is capped is the rate, so the bound holds for a *window* whose epoch durations sum to at most a
  year (§1.2, §3.2) — which, since the durations are timestamps, is exactly what a calendar year's
  epochs do.
* **It bounds the gross mint, not net inflation.** Burns (`balance_burnt`) only lower the supply
  (§3), so net inflation over a year is at most the 2.5 % gross figure, and is typically less.
* **The treasury's 10 % is inside the cap, not on top of it.** `epoch_actual_reward` starts at the
  treasury's cut and the validator shares are added to it (`reward_calculator.rs:90, 143`), and the
  treasury's cut is a row of the same `validatorReward` map the runtime consumes (`:81`), so both
  branches are funded by the one `epoch_total_reward`.
-/

namespace NearSpecV3.D2

/-- NEAR in one account: `amount + locked` (`Account::amount` + `Account::locked`). The full measure
also counts gas-key balances and burnt tokens; those live in `NearSpecV3/SupplyRuntime.lean`. -/
def Acct.total (x : Acct) : Nat := x.amount + x.locked

end NearSpecV3.D2

namespace NearSpecV3.Supply

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Sums -/

/-- Left-fold sum, matching the runtime's `foldl (· + ·) 0`. -/
def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

theorem sumNat_append (a b : List Nat) : sumNat (a ++ b) = sumNat a + sumNat b := by
  induction a with
  | nil => simp [sumNat]
  | cons x xs ih => simp only [List.cons_append, sumNat, ih]; omega

theorem sumNat_map_mul {α : Type} (l : List α) (f : α → Nat) (k : Nat) :
    sumNat (l.map fun x => k * f x) = k * sumNat (l.map f) := by
  induction l with
  | nil => simp [sumNat]
  | cons x xs ih => simp only [List.map_cons, sumNat, ih, Nat.mul_add]

theorem sumNat_map_le {α : Type} {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    sumNat (l.map f) ≤ sumNat (l.map g) := by
  induction l with
  | nil => simp [sumNat]
  | cons x xs ih =>
    simp only [List.map_cons, sumNat]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Floors only lose, added: `⌊a/c⌋ + ⌊b/c⌋ ≤ ⌊(a+b)/c⌋`. -/
theorem div_add_div_le (a b c : Nat) : a / c + b / c ≤ (a + b) / c := by
  cases c with
  | zero => simp
  | succ c =>
    rw [Nat.add_div (Nat.succ_pos c)]
    exact Nat.le_add_right _ _

theorem sumNat_div_le (c : Nat) (l : List Nat) : sumNat (l.map (· / c)) ≤ sumNat l / c := by
  induction l with
  | nil => simp [sumNat]
  | cons x xs ih =>
    simp only [List.map_cons, sumNat]
    exact Nat.le_trans (Nat.add_le_add_left ih _) (div_add_div_le x (sumNat xs) c)

/-! ## §1 The epoch reward formula

`calculate_reward` (`reward_calculator.rs:69-76`) computes, in `U256` with a final `.as_u128()`
truncation,

  `epoch_total_reward = max_inflation_rate · total_supply · epoch_duration`
                        `/ (num_seconds_per_year · max_inflation_rate.denom · NUM_NS_IN_SECOND)`

with `NUM_SECONDS_IN_A_YEAR = 24·60·60·365` and `NUM_NS_IN_SECOND = 10^9`
(`reward_calculator.rs:9-10`). The `Nat` division below is that floor division.
-/

def secondsPerYear : Nat := 24 * 60 * 60 * 365
def nsPerSecond : Nat := 1000000000
/-- `NUM_SECONDS_IN_A_YEAR · NUM_NS_IN_SECOND`: a year in nanoseconds. -/
def yearNs : Nat := secondsPerYear * nsPerSecond

theorem secondsPerYear_eq : secondsPerYear = 31536000 := by decide
theorem nsPerSecond_eq : nsPerSecond = 1000000000 := by decide
theorem yearNs_eq : yearNs = 31536000000000000 := by decide
theorem yearNs_pos : 0 < yearNs := by decide

/-- `max_inflation_rate` numerator, mainnet from PV 48 (`epoch_configs/mainnet/85.json`: `[1, 40]`).
The genesis config field reads `[0, 1]` (`mainnet_genesis.json`) but the epoch config overrides it. -/
def maxInflationNum : Nat := 1
def maxInflationDen : Nat := 40

/-- `protocol_reward_rate = 1/10`, hardcoded for `PROD_GENESIS_PROTOCOL_VERSION`
(`reward_calculator.rs:64-70`); the mainnet genesis value `[0, 1]` is overridden by that branch. -/
def protocolRewardNum : Nat := 1
def protocolRewardDen : Nat := 10

/-- `epoch_total_reward` (`reward_calculator.rs:69-76`), the amount minted for an epoch. -/
def epochTotalReward (inflNum inflDen supply epochNs : Nat) : Nat :=
  inflNum * supply * epochNs / (secondsPerYear * inflDen * nsPerSecond)

/-- Mainnet's epoch mint at `max_inflation_rate = 1/40`, in the `40 · year` form used below. -/
def epochMint (supply epochNs : Nat) : Nat := supply * epochNs / (maxInflationDen * yearNs)

/-- The mainnet mint is the general formula at `1/40`. -/
theorem epochMint_eq_epochTotalReward (supply epochNs : Nat) :
    epochMint supply epochNs = epochTotalReward 1 40 supply epochNs := by
  unfold epochMint epochTotalReward maxInflationDen secondsPerYear nsPerSecond yearNs
  simp only [Nat.one_mul]
  ac_rfl

/-- The treasury's cut, `epoch_protocol_treasury` (`reward_calculator.rs:77-83`). -/
def treasuryReward (total : Nat) : Nat := total * protocolRewardNum / protocolRewardDen

/-- The validators' budget, `epoch_validator_reward` (`reward_calculator.rs:89`). -/
def validatorBudget (total : Nat) : Nat := total - treasuryReward total

/-! ### §1.1 An epoch -/

/-- **An epoch spanning a full year mints exactly 2.5 % of the supply**: the rate the parameter
`max_inflation_rate = 1/40` denotes. -/
theorem epochMint_full_year (supply : Nat) : epochMint supply yearNs = supply / 40 := by
  unfold epochMint
  exact Nat.mul_div_mul_right supply 40 yearNs_pos

/-- **An epoch mints at most `1/40` of the supply**, for any duration up to a year. -/
theorem epochMint_le_supply_div_40 {supply epochNs : Nat} (h : epochNs ≤ yearNs) :
    epochMint supply epochNs ≤ supply / 40 := by
  unfold epochMint
  refine Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left supply h)) ?_
  exact Nat.le_of_eq (Nat.mul_div_mul_right supply 40 yearNs_pos)

/-- The annual rate pro-rated to an epoch's share of the year, floored, is at most the epoch's mint:
flooring `supply` to `supply/40` first loses at most `40` units, so the pro-rated figure is a lower
bound and not an upper one. The upper bounds are `epochMint_le_supply_div_40` and
`yearMinted_le_div_40`. -/
theorem annualised_le_epochMint (supply epochNs : Nat) :
    supply / 40 * epochNs / yearNs ≤ epochMint supply epochNs := by
  unfold epochMint
  have hX : supply / 40 * epochNs * 40 ≤ supply * epochNs := by
    have h := Nat.mul_le_mul_right epochNs (Nat.div_mul_le_self supply 40)
    calc supply / 40 * epochNs * 40 = (supply / 40 * 40) * epochNs := by ac_rfl
      _ ≤ supply * epochNs := h
  have e : supply / 40 * epochNs / yearNs = supply / 40 * epochNs * 40 / (40 * yearNs) := by
    rw [Nat.mul_comm 40 yearNs]
    exact (Nat.mul_div_mul_right (n := supply / 40 * epochNs) (k := yearNs)
      (by decide : 0 < 40)).symm
  rw [e]
  exact Nat.div_le_div_right hX

/-- **The rate is what is capped, not the epoch.** `epoch_duration` is the *measured* time since the
previous epoch's last block (`chain/epoch-manager/src/lib.rs:826-827`), so a long epoch mints more in
one go. A two-year epoch mints `supply/20` — but still at 2.5 %/year. -/
theorem epochMint_mul_yearNs (supply k : Nat) :
    epochMint supply (k * yearNs) = k * supply / 40 := by
  unfold epochMint maxInflationDen
  have h : supply * (k * yearNs) = (supply * k) * yearNs := by ac_rfl
  rw [h, Nat.mul_div_mul_right (supply * k) 40 yearNs_pos, Nat.mul_comm supply k]

/-- A two-year epoch mints exactly `supply/20`: double the per-epoch figure, same annual rate. -/
theorem epochMint_two_years (supply : Nat) : epochMint supply (2 * yearNs) = supply / 20 := by
  rw [epochMint_mul_yearNs supply 2]
  omega

/-! ### §1.2 Over a year: the total minted is at most `1/40` of the end supply

Epochs are much shorter than a year — mainnet's `epoch_length` is 43200 blocks
(`epoch_configs/mainnet/85.json`), which at the 600 ms target block time (`MIN_BLOCK_PRODUCTION_DELAY`)
is 7.2 h and at the historically observed ~1 s/block is ≈ 12 h — so a year holds ~730–1217 epochs and
each epoch's mint is computed on the supply *at that epoch*. If every epoch's supply is at most `Send`
and the epoch durations in the window sum to at most one year, the window's total mint is at most
`Send/40`: each term is at most `Send · tᵢ/(40 · year)` and the `tᵢ` sum to at most a year. This is the
honest, compounding-free reading — inflation over a one-year window is at most 2.5 % *of the supply at
the window's end*. Note the duration is *measured* wall-clock, so it is neither the 600 ms target nor a
fixed constant; both figures are instantiations of the same bound.
-/

/-- The mint of a list of `(supply, epoch_duration)` pairs. -/
def yearMinted (pairs : List (Nat × Nat)) : Nat :=
  sumNat (pairs.map fun p => epochMint p.1 p.2)

theorem yearMinted_eq (pairs : List (Nat × Nat)) :
    yearMinted pairs = sumNat (pairs.map fun p => p.1 * p.2 / (maxInflationDen * yearNs)) := rfl

/-- **The annual bound.** Every epoch's supply at most `Send`, the durations summing to at most one
year ⇒ the window mints at most `Send/40`. -/
theorem yearMinted_le_div_40 {pairs : List (Nat × Nat)} {Send : Nat}
    (hS : ∀ p ∈ pairs, p.1 ≤ Send)
    (hT : sumNat (pairs.map (·.2)) ≤ yearNs) :
    yearMinted pairs ≤ Send / 40 := by
  rw [yearMinted_eq]
  -- replace each epoch's supply by the upper bound `Send`, then let the floors lose
  have hstep : sumNat (pairs.map fun p => p.1 * p.2 / (maxInflationDen * yearNs))
      ≤ sumNat (pairs.map fun p => Send * p.2) / (maxInflationDen * yearNs) := by
    refine Nat.le_trans ?_ (sumNat_div_le _ _)
    rw [List.map_map]
    refine sumNat_map_le ?_
    intro p hp
    exact Nat.div_le_div_right (Nat.mul_le_mul_right p.2 (hS p hp))
  refine Nat.le_trans hstep ?_
  rw [sumNat_map_mul pairs (·.2) Send]
  refine Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left Send hT)) ?_
  exact Nat.le_of_eq (Nat.mul_div_mul_right Send 40 yearNs_pos)

/-- A one-year window as a single epoch: exactly 2.5 % of the supply. -/
theorem yearMinted_full_year (supply : Nat) :
    yearMinted [(supply, yearNs)] = supply / 40 := by
  simp only [yearMinted, List.map_cons, List.map_nil, sumNat, epochMint_full_year, Nat.add_zero]

/-- **2.5 % per annum, as growth of the supply.** With `Sstart` the supply at the window's start,
`Send` at its end and `minted` the window's mint, `Send ≤ Sstart + minted` (burns only lower it), so
`40 · minted ≤ Sstart + minted`, i.e. `minted ≤ Sstart/39 ≈ 2.56 %` of the starting supply, and
`≤ Send/40 = 2.5 %` of the ending supply. Both bounds are tight for the one-epoch case. -/
theorem yearMinted_le_start_div_39 {pairs : List (Nat × Nat)} {Send Sstart minted : Nat}
    (hm : minted = yearMinted pairs)
    (hS : ∀ p ∈ pairs, p.1 ≤ Send)
    (hT : sumNat (pairs.map (·.2)) ≤ yearNs)
    (hEnd : Send ≤ Sstart + minted) :
    minted ≤ Sstart / 39 := by
  subst hm
  have h40 : 40 * yearMinted pairs ≤ Send := by
    have h := yearMinted_le_div_40 hS hT
    have := (Nat.le_div_iff_mul_le (by decide : 0 < 40)).mp h
    simpa [Nat.mul_comm] using this
  omega

/-! ## §2 The treasury / validator split

`epoch_actual_reward` starts at the treasury's cut and each validator's share is added to it
(`reward_calculator.rs:90, 143`), so the minted amount is `treasury + Σ validator shares`.
-/

theorem treasury_le_self (t : Nat) : treasuryReward t ≤ t := by
  unfold treasuryReward protocolRewardNum protocolRewardDen
  simpa using Nat.div_le_self (t * 1) 10

/-- The treasury takes at most a tenth of the mint. -/
theorem treasury_mul_ten_le (t : Nat) : treasuryReward t * 10 ≤ t := by
  unfold treasuryReward protocolRewardNum protocolRewardDen
  simpa using Nat.div_mul_le_self (t * 1) 10

theorem treasury_add_validatorBudget (t : Nat) : treasuryReward t + validatorBudget t = t := by
  have h := treasury_le_self t
  unfold validatorBudget
  omega

/-- The split is exhaustive: treasury + validator budget = the mint, so the two branches together
mint exactly the epoch's budget and no more. -/
theorem split_exhaustive (total treasury validator : Nat)
    (ht : treasury = treasuryReward total) (hv : validator ≤ validatorBudget total) :
    treasury + validator ≤ total := by
  subst ht
  have h1 := treasury_le_self total
  unfold validatorBudget at hv
  omega

/-- A validator's share (`reward_calculator.rs:112-143`): the budget times its uptime fraction times
its stake fraction. The Rust code divides twice — `/ uptime_denum` then `/ total_stake` — but two
successive floor divisions are exactly one floor over the product (`Nat.div_div_eq_div_mul`), so the
single-floor form below is the value the Rust code credits, not an over-approximation. -/
def validatorReward (budget uptimeNum uptimeDen stake totalStake : Nat) : Nat :=
  budget * uptimeNum * stake / (uptimeDen * totalStake)

/-- The Rust code's two floors are this definition's one floor, so the split lemmas apply to the
credits the epoch manager actually makes. -/
theorem validatorReward_eq_rust (budget uptimeNum uptimeDen stake totalStake : Nat) :
    validatorReward budget uptimeNum uptimeDen stake totalStake
      = budget * uptimeNum * stake / uptimeDen / totalStake := by
  unfold validatorReward
  exact (Nat.div_div_eq_div_mul _ _ _).symm

/-- A validator's share never exceeds the budget, when its uptime fraction is at most 1 and its stake
is at most the total stake (both hold in the epoch manager: uptime is `produced/expected ≤ 1` and the
stake is one of the summands of the total). -/
theorem validatorReward_le_budget {budget uptimeNum uptimeDen stake totalStake : Nat}
    (hu : uptimeNum ≤ uptimeDen) (hs : stake ≤ totalStake) (hd : 0 < uptimeDen)
    (ht : 0 < totalStake) :
    validatorReward budget uptimeNum uptimeDen stake totalStake ≤ budget := by
  unfold validatorReward
  have hX : 0 < uptimeDen * totalStake := Nat.mul_pos hd ht
  have hnum : budget * uptimeNum * stake ≤ budget * (uptimeDen * totalStake) := by
    calc budget * uptimeNum * stake ≤ budget * uptimeDen * stake :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left budget hu)
      _ = budget * (uptimeDen * stake) := by ac_rfl
      _ ≤ budget * (uptimeDen * totalStake) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs)
  refine Nat.le_trans (Nat.div_le_div_right hnum) ?_
  rw [Nat.mul_comm budget (uptimeDen * totalStake), Nat.mul_div_right budget hX]
  exact Nat.le_refl budget

/-! ### §2.1 The shares sum to at most the budget

The validator shares are computed one validator at a time, each as a floor-divided fraction of the
budget, so their sum loses to the budget by the floors and by the stake and uptime fractions being
at most 1. This is the "the split cannot overshoot" half of §2: the epoch mints `treasury + Σ shares`
and `treasury + Σ shares ≤ treasury + validatorBudget = the mint`.
-/

/-- **The validator shares sum to at most the budget.** Given each share's uptime numerator at most
its denominator and the stakes summing to at most the total stake. -/
theorem sumValidatorRewards_le_budget {budget uptimeDen totalStake : Nat}
    (hd : 0 < uptimeDen) (ht : 0 < totalStake)
    (pairs : List (Nat × Nat))
    (hu : ∀ p ∈ pairs, p.2 ≤ uptimeDen)
    (hs : sumNat (pairs.map (·.1)) ≤ totalStake) :
    sumNat (pairs.map fun p => validatorReward budget p.2 uptimeDen p.1 totalStake) ≤ budget := by
  have hD : 0 < uptimeDen * totalStake := Nat.mul_pos hd ht
  simp only [validatorReward]
  have h1 : sumNat (pairs.map fun p => budget * p.2 * p.1 / (uptimeDen * totalStake))
      ≤ sumNat (pairs.map fun p => budget * p.2 * p.1) / (uptimeDen * totalStake) := by
    refine Nat.le_trans ?_ (sumNat_div_le _ _)
    rw [List.map_map]
    exact Nat.le_refl _
  refine Nat.le_trans h1 ?_
  have hnum : sumNat (pairs.map fun p => budget * p.2 * p.1)
      ≤ budget * uptimeDen * totalStake := by
    have hstep : sumNat (pairs.map fun p => budget * p.2 * p.1)
        ≤ sumNat (pairs.map fun p => budget * uptimeDen * p.1) := by
      refine sumNat_map_le ?_
      intro p hp
      exact Nat.mul_le_mul_right p.1 (Nat.mul_le_mul_left budget (hu p hp))
    refine Nat.le_trans hstep ?_
    rw [sumNat_map_mul pairs (·.1) (budget * uptimeDen)]
    exact Nat.mul_le_mul_left (budget * uptimeDen) hs
  refine Nat.le_trans (Nat.div_le_div_right hnum) ?_
  rw [Nat.mul_assoc, Nat.mul_comm budget (uptimeDen * totalStake), Nat.mul_div_right budget hD]
  exact Nat.le_refl budget

/-- **The split cannot overshoot the epoch's mint.** A treasury cut plus validator shares that fit
the validator budget sum to at most the minted amount. -/
theorem treasury_add_shares_le {total treasury shares : Nat}
    (ht : treasury = treasuryReward total) (hv : shares ≤ validatorBudget total) :
    treasury + shares ≤ total := by
  subst ht
  have h1 := treasury_le_self total
  unfold validatorBudget at hv
  omega

/-- **The amount the epoch manager actually mints is at most the epoch's budget.** `calculate_reward`
(`reward_calculator.rs:50-146`) returns `epoch_actual_reward`, which starts at the treasury's cut
(`:90`) and has each validator's share added (`:143`), so it is `treasury + Σ shares`; §2 bounds that
by the budget. The zero-validator path (`:85-87`) returns `ZERO`, which is trivially within it. -/
theorem epochActualReward_le_mint {mint treasury shares : Nat}
    (ht : treasury = treasuryReward mint) (hv : shares ≤ validatorBudget mint) :
    treasury + shares ≤ mint :=
  treasury_add_shares_le ht hv

/-- **Mainnet's actual epoch mint is at most 2.5 % of the supply.** Composing the budget bound with
§1.1: whatever the validator shares and the treasury cut work out to, the amount the epoch manager
reports as minted (`epoch_actual_reward`) is at most `epochMint supply epochNs`, which is at most
`supply/40` for any epoch of at most a year. -/
theorem epochActualReward_le_supply_div_40 {supply epochNs mint treasury shares : Nat}
    (hm : mint = epochMint supply epochNs)
    (ht : treasury = treasuryReward mint) (hv : shares ≤ validatorBudget mint)
    (hNs : epochNs ≤ yearNs) :
    treasury + shares ≤ supply / 40 := by
  have h1 := epochActualReward_le_mint ht hv
  have h2 := epochMint_le_supply_div_40 (supply := supply) hNs
  omega

/-- The epoch manager's reward ledger: the treasury's cut as one row (`reward_calculator.rs:81`) plus
a row per validator (`:168`). Its sum is `epoch_actual_reward`, the value the block header reports as
`minted_amount` (`chain/chain/src/chain.rs:2520-2522`). -/
def rewardLedger (treasury : Nat) (validators : List Nat) : List Nat := treasury :: validators

theorem sum_rewardLedger (t : Nat) (vs : List Nat) :
    sumNat (rewardLedger t vs) = t + sumNat vs := by simp [rewardLedger, sumNat]

/-- **The ledger the epoch manager credits sums to at most the epoch's mint.** Every row of the
`HashMap` `calculate_reward` returns is either the treasury's cut or a validator's share; §2 bounds the
cut by a tenth and the shares by the validator budget, so the whole ledger is at most the epoch's
`epoch_total_reward`. Since `epoch_actual_reward` is exactly the sum of that ledger's rows, this bounds
the `minted_amount` the header reports. -/
theorem rewardLedger_sum_le_mint {mint treasury : Nat} {validators : List Nat}
    (ht : treasury = treasuryReward mint)
    (hv : sumNat validators ≤ validatorBudget mint) :
    sumNat (rewardLedger treasury validators) ≤ mint := by
  rw [sum_rewardLedger]
  exact treasury_add_shares_le ht hv

/-! ### §2.2 The clip, and why the shares fit the budget

`calculate_reward` (`reward_calculator.rs:119-146`) does not take the validator's uptime fraction on
faith: it computes

  `uptime_numer = (avg_p · min_den − min_num · avg_d) · max_den`
  `uptime_denum = (max_num · min_den − min_num · max_den) · avg_d`
  `uptime_numer = if uptime_numer > uptime_denum then uptime_denum else uptime_numer`

(`:119-131`) — the `min` that clips the multiplier to 1 — and only then divides the budget by the two
floors of §2. §2.1's `sumValidatorRewards_le_budget` *assumes* the resulting numerator is at most the
denominator; §2.2 proves that from the clip, so the assumption is not an extra trust requirement on
the epoch manager.

Both threshold subtractions (`max_num · min_den − min_num · max_den` and the `avg` one) are modelled
with truncated `Nat` subtraction, so they are the Rust values provided the subtrahend does not exceed
the minuend. For the genesis defaults that holds: `online_min_threshold = 90/100` and
`online_max_threshold = 99/100` (`core/chain-configs/src/genesis_config.rs:43-49`), so the threshold
subtraction cross-multiplies to `99 · 100 − 90 · 100 = 900 > 0`. The `avg` subtraction is the epoch
manager's own `produced/expected` comparison and is non-negative whenever a validator produced no more
than it was expected to. Neither is re-proved here; both are guarded by the epoch manager, not by the
relation. -/

/-- `ValidatorStats` (`core/primitives/src/types/chunk_validator_stats.rs:10-14`). The relation only
needs the ratio, so the raw counts are not modelled. -/
abbrev VStats := Nat × Nat

/-- The uptime multiplier before the clip (`reward_calculator.rs:119-127`), as an unreduced
fraction. `avg` is the online production ratio, `minNum`/`minDen`/`maxNum`/`maxDen` the online
thresholds. -/
def uptimeRaw (avg : Nat × Nat) (minNum minDen maxNum maxDen : Nat) : Nat × Nat :=
  let onlineNum := maxNum * minDen - minNum * maxDen
  ((avg.1 * minDen - minNum * avg.2) * maxDen, onlineNum * avg.2)

/-- ``uptime_numer = if uptime_numer > uptime_denum then uptime_denum else uptime_numer``
(`reward_calculator.rs:128-131`): the multiplier is clipped to at most 1. -/
def uptimeClipped (avg : Nat × Nat) (minNum minDen maxNum maxDen : Nat) : Nat × Nat :=
  let u := uptimeRaw avg minNum minDen maxNum maxDen
  (if u.1 > u.2 then u.2 else u.1, u.2)

/-- **The clip makes the multiplier at most 1.** -/
theorem uptimeClipped_num_le_den (avg : Nat × Nat) (minNum minDen maxNum maxDen : Nat) :
    (uptimeClipped avg minNum minDen maxNum maxDen).1
      ≤ (uptimeClipped avg minNum minDen maxNum maxDen).2 := by
  unfold uptimeClipped uptimeRaw
  simp only
  by_cases h : (avg.1 * minDen - minNum * avg.2) * maxDen
      > (maxNum * minDen - minNum * maxDen) * avg.2
  · rw [ite_eq_left h]; exact Nat.le_refl _
  · rw [ite_eq_right h]; exact Nat.le_of_not_gt h

/-- The clipped denominator is the online-threshold gap times the production denominator. -/
theorem uptimeClipped_den (avg : Nat × Nat) (minNum minDen maxNum maxDen : Nat) :
    (uptimeClipped avg minNum minDen maxNum maxDen).2
      = (maxNum * minDen - minNum * maxDen) * avg.2 := by
  unfold uptimeClipped uptimeRaw
  simp only

/-- The clipped denominator is positive whenever the online thresholds are ordered and the validator
had anything to produce. -/
theorem uptimeClipped_den_pos (avg : Nat × Nat) (minNum minDen maxNum maxDen : Nat)
    (hmon : 0 < maxNum * minDen - minNum * maxDen) (havg : 0 < avg.2) :
    0 < (uptimeClipped avg minNum minDen maxNum maxDen).2 := by
  rw [uptimeClipped_den]
  exact Nat.mul_pos hmon havg

/-- One validator's row of `calculate_reward` (`reward_calculator.rs:134-145`):
`budget · uptime_num · stake / uptime_den / total_stake`, with `uptimeNum`/`uptimeDen` the **clipped**
fraction. The denominator is per-validator: it carries that validator's own production ratio
(`uptime_denum = online_numer · average_produced_denom`, `:123`). -/
def ledgerRow (budget stake totalStake uptimeNum uptimeDen : Nat) : Nat :=
  budget * uptimeNum * stake / uptimeDen / totalStake

/-- **No ledger row exceeds the budget, and this follows from the clip.** The clipped multiplier is at
most 1 (§2.2's `uptimeClipped_num_le_den`) and the validator's stake is at most the total stake, so
the product of the two fractions is at most 1 and the floors only lower it. -/
theorem ledgerRow_le_budget {budget stake totalStake uptimeNum uptimeDen : Nat}
    (hclip : uptimeNum ≤ uptimeDen) (hs : stake ≤ totalStake)
    (hd : 0 < uptimeDen) (ht : 0 < totalStake) :
    ledgerRow budget stake totalStake uptimeNum uptimeDen ≤ budget := by
  unfold ledgerRow
  have hX : 0 < uptimeDen * totalStake := Nat.mul_pos hd ht
  have hnum : budget * uptimeNum * stake ≤ budget * (uptimeDen * totalStake) := by
    calc budget * uptimeNum * stake ≤ budget * uptimeDen * stake :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left budget hclip)
      _ = budget * (uptimeDen * stake) := by ac_rfl
      _ ≤ budget * (uptimeDen * totalStake) :=
          Nat.mul_le_mul_left budget (Nat.mul_le_mul_left uptimeDen hs)
  calc budget * uptimeNum * stake / uptimeDen / totalStake
      = budget * uptimeNum * stake / (uptimeDen * totalStake) := Nat.div_div_eq_div_mul _ _ _
    _ ≤ budget * (uptimeDen * totalStake) / (uptimeDen * totalStake) :=
          Nat.div_le_div_right hnum
    _ = budget := by
          rw [Nat.mul_comm budget (uptimeDen * totalStake)]
          exact Nat.mul_div_right _ hX

/-- **The clip alone caps a row by the stake-proportional share of the budget.** This is the form the
summation needs: the row's own `uptimeDen` is eliminated, so rows with different denominators can be
added. -/
theorem ledgerRow_le_share {budget stake totalStake uptimeNum uptimeDen : Nat}
    (hclip : uptimeNum ≤ uptimeDen) (hd : 0 < uptimeDen) :
    ledgerRow budget stake totalStake uptimeNum uptimeDen ≤ budget * stake / totalStake := by
  unfold ledgerRow
  calc budget * uptimeNum * stake / uptimeDen / totalStake
      ≤ budget * uptimeDen * stake / uptimeDen / totalStake :=
          Nat.div_le_div_right
            (Nat.div_le_div_right (Nat.mul_le_mul_right stake
              (Nat.mul_le_mul_left budget hclip)))
    _ = budget * stake / totalStake := by
          have h1 : budget * uptimeDen * stake = (budget * stake) * uptimeDen := by
            ac_rfl
          rw [h1, Nat.mul_div_cancel (budget * stake) hd]

/-- A validator's `(stake, uptimeNum)` row, with the clipped uptime fraction that `calculate_reward`
computes for it. -/
abbrev VRow := Nat × Nat × Nat

/-- The total stake over the validator set: the Rust `validator_stake.values().sum()`. -/
def rowSum (rows : List VRow) : Nat := sumNat (rows.map (·.1))

/-- **The sum of every validator row is at most the budget.** Each row is capped by its
stake-proportional share of the budget (`ledgerRow_le_share`, from the clip, with the row's own
uptime denominator), and the shares sum to at most the budget because the stakes sum to at most the
total stake and floors only lose (`sumNat_div_le`). -/
theorem sumLedgerRows_le_budget {budget totalStake : Nat}
    (ht : 0 < totalStake) (rows : List VRow)
    (hclip : ∀ p ∈ rows, p.2.1 ≤ p.2.2)
    (hd : ∀ p ∈ rows, 0 < p.2.2)
    (hs : rowSum rows ≤ totalStake) :
    sumNat (rows.map fun p => ledgerRow budget p.1 totalStake p.2.1 p.2.2) ≤ budget := by
  have hshare : sumNat (rows.map fun p => ledgerRow budget p.1 totalStake p.2.1 p.2.2)
      ≤ sumNat (rows.map fun p => budget * p.1 / totalStake) :=
    sumNat_map_le (fun p hp => ledgerRow_le_share (hclip p hp) (hd p hp))
  refine Nat.le_trans hshare ?_
  have h1 : sumNat (rows.map fun p => budget * p.1 / totalStake)
      ≤ sumNat (rows.map fun p => budget * p.1) / totalStake := by
    have := sumNat_div_le totalStake (rows.map fun p => budget * p.1)
    rwa [List.map_map] at this
  refine Nat.le_trans h1 ?_
  have hnum : sumNat (rows.map fun p => budget * p.1) ≤ budget * totalStake := by
    rw [sumNat_map_mul rows (·.1) budget]
    exact Nat.mul_le_mul_left budget hs
  refine Nat.le_trans (Nat.div_le_div_right hnum) ?_
  rw [Nat.mul_comm budget totalStake, Nat.mul_div_right budget ht]
  exact Nat.le_refl budget

/-- Filtering a list can only lower the sum of a non-negative function. -/
theorem sumNat_filter_le {α : Type} (p : α → Bool) (f : α → Nat) (l : List α) :
    sumNat ((l.filter p).map f) ≤ sumNat (l.map f) := by
  induction l with
  | nil => simp [sumNat]
  | cons x xs ih =>
    simp only [List.filter_cons, List.map_cons, sumNat]
    split
    · exact Nat.add_le_add_left ih _
    · exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- **The whole epoch ledger is within the mint, with the shares' fraction bound coming from the
clip.** This is `rewardLedger_sum_le_mint` with its `shares ≤ validatorBudget` hypothesis *proved*
from §2.2 rather than assumed: the ledger is the treasury's cut plus the rows of
`calculate_reward`, each row is at most its stake-proportional share of the budget by the clip, and the
stakes sum to the total stake. -/
theorem rewardLedger_sum_le_mint' {mint totalStake : Nat}
    (htot : 0 < totalStake) (rows : List VRow)
    (hclip : ∀ p ∈ rows, p.2.1 ≤ p.2.2)
    (hd : ∀ p ∈ rows, 0 < p.2.2)
    (hs : rowSum rows ≤ totalStake) :
    sumNat (rewardLedger (treasuryReward mint)
      (rows.map fun p => ledgerRow (validatorBudget mint) p.1 totalStake p.2.1 p.2.2)) ≤ mint := by
  rw [sum_rewardLedger]
  exact treasury_add_shares_le rfl (sumLedgerRows_le_budget htot rows hclip hd hs)

/-- **The rewards credited on one shard are within the epoch's mint.** The runtime filters the epoch
ledger to this shard's accounts (`D2/Validators.lean:40`, mirroring
`chain/chain/src/runtime/mod.rs:239-244`), and `validatorUpdate` writes exactly those rows
(`SupplyConfinement.validatorUpdate_keeps` confines the write set to them). A filtered sublist sums to
at most the full list, so the credited amount is bounded by the ledger, which §2.2 bounds by the
budget and hence by the mint. -/
theorem creditedRewards_le_mint {mint totalStake : Nat}
    (htot : 0 < totalStake) (rows : List VRow)
    (hclip : ∀ p ∈ rows, p.2.1 ≤ p.2.2)
    (hd : ∀ p ∈ rows, 0 < p.2.2)
    (hs : rowSum rows ≤ totalStake) (onShard : VRow → Bool) :
    sumNat ((rows.filter onShard).map fun p =>
        ledgerRow (validatorBudget mint) p.1 totalStake p.2.1 p.2.2)
      ≤ mint := by
  refine Nat.le_trans (sumNat_filter_le onShard _ rows) ?_
  exact Nat.le_trans (sumLedgerRows_le_budget htot rows hclip hd hs) (Nat.sub_le _ _)

/-- `calculate_reward`'s accumulator (`reward_calculator.rs:83-143`): it starts at the treasury's cut
(`:90`) and adds each validator's row (`:143`), returning `(res, epoch_actual_reward)`. The second
component is what `EpochInfo.minted_amount` stores (`chain/epoch-manager/src/lib.rs:822,889`) and the
first is what `EpochInfo.validator_reward` stores (`core/primitives/src/epoch_info.rs:56`). So the map
and the header's `minted_amount` are two views of one construction, not independent quantities. -/
def epochActualReward (mint : Nat) (rows : List (Nat × Nat)) : Nat :=
  treasuryReward mint + sumNat (rows.map (·.1))

/-- **`minted_amount` is exactly the total of the reward map.** This is the structural link between the
two components `calculate_reward` returns: whatever rows the ledger has, their sum plus the treasury's
cut is the value the header reports as minted. -/
theorem epochActualReward_eq_ledger (mint : Nat) (rows : List (Nat × Nat)) :
    epochActualReward mint rows
      = sumNat (rewardLedger (treasuryReward mint) (rows.map (·.1))) := by
  unfold epochActualReward
  rw [sum_rewardLedger]

/-- **The rewards credited on one shard are at most 2.5 % of supply, with no assumption about the
validator shares.**

This is the end-to-end form. Every hypothesis is a fact about the epoch manager's own inputs rather
than a bound smuggled in:

* `hclip`/`hd` are discharged at the call site by `uptimeClipped_num_le_den` and
  `uptimeClipped_den_pos` — `calculate_reward` clips the uptime multiplier to 1 before using it;
* `hs` is `rowSum rows ≤ totalStake`, i.e. the validators' stakes are the ones the total is taken over
  (`validator_stake.values().sum()`);
* `hm`/`hNs` say the epoch mint is `epochMint supply epochNs` for an epoch of at most a year.

The chain is: each ledger row ≤ its stake-proportional share of the budget (clip); the shares sum to
at most the budget (`sumLedgerRows_le_budget`); the shard's credited rows are a filtered sublist
(`sumNat_filter_le`); and the budget is at most the mint, which is at most `supply/40`. -/
theorem creditedRewards_le_supply_div_40 {supply epochNs mint totalStake : Nat}
    (hm : mint = epochMint supply epochNs) (hNs : epochNs ≤ yearNs)
    (htot : 0 < totalStake) (rows : List VRow)
    (hclip : ∀ p ∈ rows, p.2.1 ≤ p.2.2)
    (hd : ∀ p ∈ rows, 0 < p.2.2)
    (hs : rowSum rows ≤ totalStake) (onShard : VRow → Bool) :
    sumNat ((rows.filter onShard).map fun p =>
        ledgerRow (validatorBudget mint) p.1 totalStake p.2.1 p.2.2)
      ≤ supply / 40 := by
  refine Nat.le_trans (sumNat_filter_le onShard _ rows) ?_
  refine Nat.le_trans (sumLedgerRows_le_budget htot rows hclip hd hs) ?_
  subst hm
  exact Nat.le_trans (Nat.sub_le (epochMint supply epochNs) _)
    (epochMint_le_supply_div_40 (supply := supply) hNs)

/-- **`minted_amount` is at most 2.5 % of supply, from the clip alone.** This is the header's own
quantity: `chain.rs:2520-2522` reads `EpochInfo.minted_amount`, which `calculate_reward` produces as
`epochActualReward`. Bounding it needs no assumption about the reward split — §2.2 derives
`Σ rows ≤ validatorBudget mint` from the uptime clip. -/
theorem mintedAmount_le_supply_div_40 {supply epochNs : Nat}
    (hNs : epochNs ≤ yearNs)
    {totalStake : Nat} (htot : 0 < totalStake) (rows : List VRow)
    (hclip : ∀ p ∈ rows, p.2.1 ≤ p.2.2)
    (hd : ∀ p ∈ rows, 0 < p.2.2)
    (hs : rowSum rows ≤ totalStake) :
    treasuryReward (epochMint supply epochNs)
      + sumNat (rows.map fun p => ledgerRow (validatorBudget (epochMint supply epochNs))
          p.1 totalStake p.2.1 p.2.2)
      ≤ supply / 40 := by
  have hrows := sumLedgerRows_le_budget (budget := validatorBudget (epochMint supply epochNs))
    htot rows hclip hd hs
  have hbudget : treasuryReward (epochMint supply epochNs)
      + validatorBudget (epochMint supply epochNs) = epochMint supply epochNs :=
    treasury_add_validatorBudget _
  have h1 : treasuryReward (epochMint supply epochNs)
      + sumNat (rows.map fun p => ledgerRow (validatorBudget (epochMint supply epochNs))
          p.1 totalStake p.2.1 p.2.2) ≤ epochMint supply epochNs := by
    omega
  exact Nat.le_trans h1 (epochMint_le_supply_div_40 (supply := supply) hNs)

/-! ## §3 The block header's supply identity

`verify_total_supply_checked` (`core/primitives/src/block.rs:315-343`): the endorsed header's
`total_supply` must equal `prev_total_supply + minted_amount − balance_burnt`, where `minted_amount`
is `Some` only when the block starts an epoch (`chain/chain/src/chain.rs:2520-2533`) and
`balance_burnt` is the sum of the chunks' `prev_balance_burnt`. Overflow is `none`; a burnt amount
larger than `prev + minted` is `some false`.
-/

/-- `prev.checked_add(minted)?.checked_sub(burnt)`, then `== new_total_supply`. -/
def verifyTotalSupply (prevSupply minted burnt newSupply : Nat) : Option Bool :=
  let s := prevSupply + minted
  if burnt ≤ s then some (newSupply == s - burnt) else some false

/-- The `minted_amount` the chain hands to the check: `Some` only at an epoch start. -/
def mintedOf (epochStart : Bool) (reward : Nat) : Nat := if epochStart then reward else 0

theorem mintedOf_not_epochStart (reward : Nat) : mintedOf false reward = 0 := rfl

theorem mintedOf_epochStart (reward : Nat) : mintedOf true reward = reward := rfl

/-! ### §3.0 Mainnet's epoch, instantiated

Mainnet's epoch is 43200 blocks (`epoch_configs/mainnet/85.json`) at a target of 600 ms per block
(`MIN_BLOCK_PRODUCTION_DELAY`, `core/chain-configs/src/lib.rs:75`), i.e. 25 920 000 ms ≈ 7.2 h. An
epoch's mint is therefore far under the 2.5 % ceiling: at most `supply/40` pro-rated to 7.2 h of an
8760 h year, i.e. about `supply/48666` ≈ 0.00206 %. At the ~1 s/block mainnet actually produced in this
era the same epoch spans ≈ 12 h and the figure is ≈ `supply/29200` ≈ 0.00342 % — still ≈ 1/730 of the
annual ceiling. Both are instantiations of `epochMint_le_supply_div_40`; the divisor below is the 600 ms
target one. -/

/-- Mainnet's epoch duration in nanoseconds: 43200 blocks × 600 ms. -/
def mainnetEpochNs : Nat := 43200 * 600 * 1000000

theorem mainnetEpochNs_eq : mainnetEpochNs = 25920000000000 := by decide

theorem mainnetEpochNs_pos : 0 < mainnetEpochNs := by decide

theorem mainnetEpochNs_le_year : mainnetEpochNs ≤ yearNs := by
  rw [mainnetEpochNs_eq, yearNs_eq]
  decide

/-- `43200 blocks × 600 ms × 48666 ≤ 40 · year`: the epoch's share of the year, as a fraction. -/
theorem mainnetEpochNs_ratio : mainnetEpochNs * 48666 ≤ maxInflationDen * yearNs := by decide

/-- **Mainnet's per-epoch mint is at most `supply/40`.** -/
theorem mainnetEpochMint_le (supply : Nat) :
    epochMint supply mainnetEpochNs ≤ supply / 40 :=
  epochMint_le_supply_div_40 mainnetEpochNs_le_year

/-- Mainnet's per-epoch mint, spelled out: a 7.2 h epoch out of an 8760 h year is `1/48666.7` of the
year, so the epoch mints at most `supply/48666` ≈ 0.00206 % of the supply. (The annual 2.5 % is spread
over ~1217 epochs, each ≈ 0.00206 %.) -/
theorem mainnetEpochMint_le_div_48666 (supply : Nat) :
    epochMint supply mainnetEpochNs ≤ supply / 48666 := by
  unfold epochMint
  refine Nat.le_trans
    (Nat.div_le_div_left mainnetEpochNs_ratio
      (Nat.mul_pos mainnetEpochNs_pos (by decide : 0 < 48666))) ?_
  rw [Nat.mul_comm supply mainnetEpochNs, Nat.mul_div_mul_left supply 48666 mainnetEpochNs_pos]
  exact Nat.le_refl _

/-- **Acceptance characterisation.** The header check accepts iff the supply identity holds exactly. -/
theorem verifyTotalSupply_accept {prevSupply minted burnt newSupply : Nat} :
    verifyTotalSupply prevSupply minted burnt newSupply = some true ↔
      burnt ≤ prevSupply + minted ∧ newSupply = prevSupply + minted - burnt := by
  unfold verifyTotalSupply
  dsimp only
  split
  · rename_i h
    constructor
    · intro he
      have h2 : newSupply = prevSupply + minted - burnt := by simpa using he
      exact ⟨h, h2⟩
    · rintro ⟨-, rfl⟩
      simp
  · rename_i h
    constructor
    · intro he; exact absurd he (by simp)
    · rintro ⟨h1, -⟩; exact absurd h1 h

/-- **The supply only grows by the minted amount.** Any accepted block satisfies
`total_supply(block) ≤ total_supply(prev) + minted`. -/
theorem verifyTotalSupply_le_add {prevSupply minted burnt newSupply : Nat}
    (h : verifyTotalSupply prevSupply minted burnt newSupply = some true) :
    newSupply ≤ prevSupply + minted := by
  rw [verifyTotalSupply_accept] at h
  omega

/-- **Outside an epoch start nothing is minted, so supply cannot grow.** On a block that does not
start an epoch, an accepted header's supply is at most the previous block's. -/
theorem verifyTotalSupply_nonEpoch_le {prevSupply reward burnt newSupply : Nat}
    (h : verifyTotalSupply prevSupply (mintedOf false reward) burnt newSupply = some true) :
    newSupply ≤ prevSupply := by
  have := verifyTotalSupply_le_add h
  simpa [mintedOf] using this

/-- **The supply only shrinks when nothing is minted and something is burnt.** -/
theorem verifyTotalSupply_nonEpoch_lt {prevSupply reward burnt newSupply : Nat}
    (h : verifyTotalSupply prevSupply (mintedOf false reward) burnt newSupply = some true)
    (hb : 0 < burnt) :
    newSupply < prevSupply := by
  rw [verifyTotalSupply_accept] at h
  have h1 : burnt ≤ prevSupply := by simpa [mintedOf] using h.1
  have h2 : newSupply = prevSupply - burnt := by simpa [mintedOf] using h.2
  omega

/-! ### §3.1 The epoch's growth is bounded by 2.5 % of supply

Composing §3 with §1: on an epoch-start block the minted amount is the epoch's budget, so the
supply's increase across that block is at most `supply/40`, and across a one-year window at most
`1/40` of the window's end supply (§1.2). -/

/-- **An epoch-start block raises the supply by at most 2.5 % of it.** -/
theorem verifyTotalSupply_epochStart_le {prevSupply epochNs burnt newSupply : Nat}
    (h : verifyTotalSupply prevSupply (mintedOf true (epochMint prevSupply epochNs)) burnt newSupply
          = some true)
    (hNs : epochNs ≤ yearNs) :
    newSupply ≤ prevSupply + prevSupply / 40 := by
  have := verifyTotalSupply_le_add h
  have hb := epochMint_le_supply_div_40 (supply := prevSupply) hNs
  simpa [mintedOf] using Nat.le_trans this (Nat.add_le_add_left hb _)

/-- The same, phrased as "the increase is at most 2.5 % of the previous supply". -/
theorem verifyTotalSupply_epochStart_increase_le {prevSupply epochNs burnt newSupply : Nat}
    (h : verifyTotalSupply prevSupply (mintedOf true (epochMint prevSupply epochNs)) burnt newSupply
          = some true)
    (hNs : epochNs ≤ yearNs) (hmono : prevSupply ≤ newSupply) :
    newSupply - prevSupply ≤ prevSupply / 40 := by
  have hle := verifyTotalSupply_epochStart_le h hNs
  omega

/-! ### §3.2 A run of accepted headers conserves supply up to mint and burn

Chain the per-block identity across a list of accepted headers: over the run, the final supply is the
initial supply plus everything minted minus everything burnt — with the minted term `0` on every block
that does not start an epoch. -/

/-- The facts a block contributes to the supply identity. `minted` is the epoch's mint on an
epoch-start block and `0` otherwise (`mintedOf`); `supply` and `dur` are the supply the mint was
computed on and the epoch's duration, present so that §1's bound can be applied to a run. -/
structure BlockSupply where
  epochStart : Bool
  minted : Nat
  burnt : Nat
  supply : Nat := 0
  dur : Nat := 0
  deriving DecidableEq, Repr

/-- One accepted block's supply step: `s + minted − burnt`, or `none` when burnt exceeds it. -/
def supplyStep (s : Nat) (b : BlockSupply) : Option Nat :=
  let m := mintedOf b.epochStart b.minted
  if b.burnt ≤ s + m then some (s + m - b.burnt) else none

theorem supplyStep_sound {s S : Nat} {b : BlockSupply} (h : supplyStep s b = some S) :
    S = s + mintedOf b.epochStart b.minted - b.burnt ∧
      b.burnt ≤ s + mintedOf b.epochStart b.minted := by
  unfold supplyStep at h
  dsimp only at h
  split at h
  · rename_i hle
    simp only [Option.some.injEq] at h
    exact ⟨h.symm, hle⟩
  · simp at h

/-- Run the supply identity over a list of accepted blocks. -/
def supplyRun : Nat → List BlockSupply → Option Nat
  | s, [] => some s
  | s, b :: rest => (supplyStep s b).bind (supplyRun · rest)

/-- **Over a run, the final supply is the initial supply plus mints minus burns.** -/
theorem supplyRun_conservation :
    ∀ (bs : List BlockSupply) (s S : Nat), supplyRun s bs = some S →
      S + sumNat (bs.map (·.burnt)) =
        s + sumNat (bs.map fun b => mintedOf b.epochStart b.minted) := by
  intro bs
  induction bs with
  | nil => intro s S h; simp only [supplyRun, Option.some.injEq] at h; subst h; simp [sumNat]
  | cons b rest ih =>
    intro s S h
    simp only [supplyRun, List.map_cons, sumNat] at h ⊢
    cases hs : supplyStep s b with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind] at h
      obtain ⟨h1, hle⟩ := supplyStep_sound hs
      have h2 := ih s' S h
      omega

/-- **On a run with no epoch start the supply never grows.** A run of blocks that do not start an
epoch only burns: its final supply is at most its initial supply. -/
theorem supplyRun_nonEpoch_mono :
    ∀ (bs : List BlockSupply) (s S : Nat), (∀ b ∈ bs, b.epochStart = false) →
      supplyRun s bs = some S → S ≤ s := by
  intro bs
  induction bs with
  | nil => intro s S _ h; simp only [supplyRun, Option.some.injEq] at h; omega
  | cons b rest ih =>
    intro s S hne h
    have hb : b.epochStart = false := hne b (by simp)
    simp only [supplyRun] at h
    cases hs : supplyStep s b with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind] at h
      have h1 : s' ≤ s := by
        have h0 : s' = s + mintedOf b.epochStart b.minted - b.burnt := (supplyStep_sound hs).1
        rw [hb] at h0
        simp only [mintedOf, Bool.false_eq_true, ite_false] at h0
        omega
      exact Nat.le_trans (ih s' S (fun x hx => hne x (by simp [hx])) h) h1

/-- **A run's supply increase is at most its total mint.** From §3.2's conservation: burns only
lower the supply, so `S ≤ Sstart + Σ minted`. -/
theorem supplyRun_increase_le {bs : List BlockSupply} {Sstart S cap : Nat}
    (h : supplyRun Sstart bs = some S)
    (hcap : sumNat (bs.map fun b => mintedOf b.epochStart b.minted) ≤ cap) :
    S ≤ Sstart + cap := by
  have hc := supplyRun_conservation bs Sstart S h
  omega

/-- **A one-year run mints at most 2.5 % of its end supply.** Composing §3.2's conservation with
§1.2's annual bound: each block's mint is either `0` (no epoch start) or the epoch formula on its own
supply; every such supply is at most `Send`, and the epoch durations in the window sum to at most one
year, so the run's total mint is at most `Send/40`. -/
theorem supplyRun_mint_cap {bs : List BlockSupply} {Send : Nat}
    (hform : ∀ b ∈ bs, b.epochStart = true → b.minted = epochMint b.supply b.dur)
    (hS : ∀ b ∈ bs, b.supply ≤ Send)
    (hT : sumNat (bs.map (·.dur)) ≤ yearNs) :
    sumNat (bs.map fun b => mintedOf b.epochStart b.minted) ≤ Send / 40 := by
  -- termwise: a block's mint is at most `Send · dur / (40 · year)`
  have hstep : sumNat (bs.map fun b => mintedOf b.epochStart b.minted)
      ≤ sumNat (bs.map fun b => Send * b.dur) / (maxInflationDen * yearNs) := by
    refine Nat.le_trans ?_ (sumNat_div_le _ _)
    rw [List.map_map]
    refine sumNat_map_le ?_
    intro b hb
    cases hbe : b.epochStart with
    | true =>
      simp only [mintedOf, ite_true]
      rw [hform b hb hbe]
      exact Nat.div_le_div_right (Nat.mul_le_mul_right b.dur (hS b hb))
    | false =>
      simp only [mintedOf]
      exact Nat.zero_le _
  refine Nat.le_trans hstep ?_
  rw [sumNat_map_mul bs (·.dur) Send]
  refine Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left Send hT)) ?_
  exact Nat.le_of_eq (Nat.mul_div_mul_right Send 40 yearNs_pos)

/-- **A one-year run raises the supply by at most 2.5 % of its end supply.** The headline composition:
§3.2's run-level conservation plus the §1.2 annual bound. -/
theorem supplyRun_year_increase_le {bs : List BlockSupply} {Sstart S Send : Nat}
    (h : supplyRun Sstart bs = some S)
    (hform : ∀ b ∈ bs, b.epochStart = true → b.minted = epochMint b.supply b.dur)
    (hS : ∀ b ∈ bs, b.supply ≤ Send)
    (hT : sumNat (bs.map (·.dur)) ≤ yearNs) :
    S ≤ Sstart + Send / 40 :=
  supplyRun_increase_le h (supplyRun_mint_cap hform hS hT)

end NearSpecV3.Supply
