# Supply and inflation in the Lean model — what is proved

Two economic properties of NEAR, as far as the Lean spec in `spec/lean/v3/NearSpecV3/` can carry them:

1. **No NEAR is created anywhere except validator rewards.**
2. **The amount created is within 2.5 % of total supply per annum.**

This document says what each statement means precisely, which theorem proves it, and what is *not*
proved. The Lean modules are `NearSpecV3/Supply.lean` (formula and header),
`NearSpecV3/SupplyRuntime.lean` (runtime balance writes) and `NearSpecV3/SupplyConfinement.lean`
(where in the runtime those writes can land); all three are in the default `lake build`.

Short version: **(2) is proved as a bound on the epoch-reward formula and on the block header's
supply identity, and the same cap is carried through to the amount actually credited on a shard —
`calculate_reward`'s uptime clip is modelled, so the share bound is derived rather than assumed;
(1) is proved as a per-site accounting of every balance write in the D2 runtime, plus a
machine-checked confinement result saying the mint site writes no account outside the shard's stake
info and the treasury. The inventory that the per-site list is exhaustive is still an argument over
the source rather than a symbolic-execution proof.**

One link is *not* closed and **cannot be closed from claim bytes**: that the reward amounts a chunk
credits *equal* the epoch manager's computed ledger. That value is a trusted claim input
(`spec/claim-v3.md` T10), and the claim carries none of the inputs the ledger is computed from. What
is proved is the stronger-than-before statement that *no matter which rewards the trusted answer
carries*, the amount minted and credited stays within 2.5 % — see the "reward *amounts*" bullet in §3.

---

## 1. The 2.5 % per annum bound

### The formula

`chain/epoch-manager/src/reward_calculator.rs:69-76` computes an epoch's mint as

```
epoch_total_reward = max_inflation_rate.numer · total_supply · epoch_duration
                     / (num_seconds_per_year · max_inflation_rate.denom · 10^9)
```

in `U256`, truncated to `u128`. Mainnet's `max_inflation_rate` is `1/40` from protocol version 48 on
(`core/primitives/res/epoch_configs/mainnet/85.json`, which PV 86 also uses); the genesis-config field
`[0, 1]` is overridden by the epoch config. `NearSpecV3.Supply.epochTotalReward` is that expression in
`Nat`; `epochMint` is its `1/40` instance in the `40 · year` form.

### The results

| statement | theorem |
|---|---|
| the `1/40` form equals the Rust expression | `epochMint_eq_epochTotalReward` |
| one full-year epoch mints exactly `supply/40` | `epochMint_full_year` |
| one epoch of at most a year mints at most `supply/40` | `epochMint_le_supply_div_40` |
| a `k`-year epoch mints `k·supply/40` (the cap is on the rate) | `epochMint_mul_yearNs` |
| a one-year window of epochs mints at most `Send/40` | `yearMinted_le_div_40` |
| … equivalently at most `Sstart/39` ≈ 2.56 % of the start supply | `yearMinted_le_start_div_39` |
| mainnet's 7.2 h epoch mints at most `supply/48666` ≈ 0.00206 % | `mainnetEpochMint_le_div_48666` |

The window bound is the honest reading of "per annum": each epoch's mint is computed on the supply at
that epoch, and `epoch_duration` is a *measured timestamp difference* (`epoch-manager/src/lib.rs:826-827`),
so what the parameter caps is the rate. Mainnet's epoch is 43200 blocks
(`epoch_configs/mainnet/85.json`): 7.2 h at the 600 ms target block time, ≈ 12 h at the ~1 s/block
mainnet produced in this era — either way a year holds ~730–1217 epochs, so the per-epoch figures below
are instantiations of the same bound rather than a single fixed number. A year's epochs therefore mint at most `1/40` of the supply at
the year's end, i.e. **at most 2.5 %**, and at most `1/39` of the supply at the year's start (≈ 2.56 %,
because the base grows). A single epoch spanning a full year mints exactly `supply/40`, which is the
figure the parameter denotes. A two-year epoch mints `supply/20` — the rate is still 2.5 %/year.

### The split

`epoch_actual_reward` starts at the treasury's 10 % cut (`reward_calculator.rs:90`) and each validator's
share is added to it (`:143`), so the minted total is `treasury + Σ shares`; both branches are funded
from the one `epoch_total_reward`.

| statement | theorem |
|---|---|
| the treasury takes at most a tenth | `treasury_mul_ten_le` |
| treasury + validator budget = the mint | `treasury_add_validatorBudget` |
| one validator's share ≤ the budget | `validatorReward_le_budget` |
| the shares sum to at most the budget | `sumValidatorRewards_le_budget` |
| treasury + shares ≤ the mint | `treasury_add_shares_le` |
| the Rust double floor equals the single-floor share | `validatorReward_eq_rust` |
| the epoch manager's reward ledger sums to ≤ the mint | `rewardLedger_sum_le_mint` |
| the epoch manager's reported mint ≤ 2.5 % of supply | `epochActualReward_le_supply_div_40` |

### The clip: why the shares fit the budget

`calculate_reward` does not take the uptime fraction on faith. It computes the multiplier
`(avg_p · min_den − min_num · avg_d) · max_den / ((max_num · min_den − min_num · max_den) · avg_d)`
and then clips the numerator to the denominator (`reward_calculator.rs:119-131`) before dividing.
§2.2 models that clip, which turns the share bound from an assumption into a theorem:

| statement | theorem |
|---|---|
| the clip makes the uptime multiplier ≤ 1 | `uptimeClipped_num_le_den` |
| the clipped denominator is the threshold gap × production denominator | `uptimeClipped_den` |
| one ledger row ≤ the budget | `ledgerRow_le_budget` |
| one row ≤ its stake-proportional share of the budget | `ledgerRow_le_share` |
| the rows sum to ≤ the budget, per-validator denominators | `sumLedgerRows_le_budget` |
| `minted_amount` = the total of the reward map | `epochActualReward_eq_ledger` |
| `minted_amount` ≤ 2.5 % of supply — clip only, no share assumption | `mintedAmount_le_supply_div_40` |
| the rewards credited on **one shard** ≤ 2.5 % of supply | `creditedRewards_le_supply_div_40` |
| any single `lookupAmt` reward ≤ the reward list's total | `lookupAmt_getD_le_sum` |

The last two are the ones that touch the runtime. `creditedRewards_le_supply_div_40` is the amount that
actually lands in accounts on the shard: the epoch ledger is filtered to the shard's accounts
(`D2/Validators.lean:40`), a filtered sublist sums no higher (`sumNat_filter_le`), and §5.5 shows
`validatorUpdate` writes no account outside that set. So *however the trusted rows were chosen*, the
credit is inside the cap.

### The block header

`Block::verify_total_supply_checked` (`core/primitives/src/block.rs:315-343`) accepts a block only if
`total_supply(block) = total_supply(prev) + minted − balance_burnt`, and `minted_amount` is supplied
only when the block starts an epoch (`chain/chain/src/chain.rs:2520-2533`).

| statement | theorem |
|---|---|
| acceptance ⟺ the identity holds | `verifyTotalSupply_accept` |
| any accepted block satisfies `supply ≤ prev + minted` | `verifyTotalSupply_le_add` |
| a non-epoch block cannot raise supply | `verifyTotalSupply_nonEpoch_le` |
| a non-epoch block with any burn lowers supply | `verifyTotalSupply_nonEpoch_lt` |
| an epoch-start block raises supply by ≤ 2.5 % | `verifyTotalSupply_epochStart_le` |

And over a *run* of accepted headers (§3.2): `supplyRun_conservation` gives
`final = start + Σ minted − Σ burnt`, `supplyRun_nonEpoch_mono` says a run without an epoch start only
burns, and `supplyRun_year_increase_le` composes the run's conservation with the annual bound:
**a one-year run raises the supply by at most `Send/40`.**

---

## 2. "Nowhere else"

### At block granularity

The two facts above give it directly: an accepted header's supply changes by exactly `minted − burnt`
(`verifyTotalSupply_accept`), and `minted` is `0` unless the block starts an epoch, where it is the
epoch's reward. So the *only* block that can raise the supply is an epoch's first, and it raises it by
at most a year's 2.5 % worth — less if it burns anything.

### At account granularity

`NearSpecV3/SupplyRuntime.lean` gives the measure `Σ_accounts (amount + locked) + Σ_gas_keys balance +
tokensBurnt` and the arithmetic of every write to it in the D2 runtime (`D2/Actions.lean`,
`D2/Receipts.lean`, `D2/RuntimeD2.lean`, `D2/Validators.lean`):

| site | effect | theorem |
|---|---|---|
| `validatorUpdate`, stake-info branch | **+ reward** | `validatorStep_total` |
| `validatorUpdate`, treasury branch | **+ reward** | `treasuryStep_total` |
| `actStake` | 0 | `stakeStep_total`, `actStake_ok_total` |
| `actFromGasKey` | 0 | `fromGasKeyStep_total` |
| `actToGasKey` | + deposit (charged before) | `toGasKeyStep_total` |
| `actDeleteKey` on a gas key | − balance, into `tokensBurnt` | `deleteGasKeyStep_total` |
| `actDeleteAccount` | − amount − gsum, refund receipt + amount | `deleteAccountStep_total` |
| `applyActionReceipt` receiver reward | 0 over `amount + tokensBurnt` | `receiverRewardStep_total` |
| transaction charge | − total cost | `chargeStep_total` |
| charge + deposit credit | 0 over the pair | `depositPair_total` |
| failed-receipt deposit refund | 0 over the pair | `refundStep_total` |

`actStake` is proved *through the runtime function* (`actStake_ok_total`), showing the style closes
end to end: unfold the function, find the write, apply the arithmetic lemma. `validatorUpdate`'s
per-entry step is the pure `Acct → Acct` map `validatorStep`, whose accounting is `validatorStep_total`;
the monadic overlay step wrapping it is `validatorEntryStep` (§5.5.1). The fold-level *sum* over the
shard's stake info — "the whole call raises the measure by exactly the sum of its rewards" — is not
proved; the header of `SupplyRuntime.lean` lists it as successor work. What §5.5 carries over the same
`foldlM` is the *confinement* statement (`validatorFold_keeps`), which is a different conclusion.

The read-after-write link is provided too: `lookup_setAcct` and `kvFind_put_same` say that a `setAcct`
is what a later `getAcct` of the same account reads. That is what a successor invariant needs to turn
the per-site arithmetic into a statement about the overlay the runtime actually commits.

Read this table as: *the supply rises by exactly the rewards the facts carry, and nothing else*. It does
not say those rewards are the correct epoch ledger — that is §1's job for the computed ledger, and the
equality between the two is the "reward *amounts*" gap in §3.

### Where the writes can land

The table above says what each write *does*; it does not say *which accounts* a site can reach. For the
mint site that second half is now proved in `NearSpecV3/SupplyConfinement.lean` (§5):

| statement | theorem |
|---|---|
| writing one account key leaves every other key's lookup alone | `lookup_set_other` |
| … and that survives the commit | `lookup_commit_of_avoids` |
| different accounts have different keys | `kAccount_inj`, `kAccount_ne` |
| an account key is never a code/access-key/contract-data/queue/bandwidth key | §5.3 key-disjointness lemmas |
| the bandwidth-scheduler step changes no account's lookup | `schedOvl_acct_lookup` |
| the named per-entry step is the code's lambda | `validatorEntryStep_eq_lambda` |
| the named step keeps an unnamed account's lookup | `validatorEntryStep_keeps` |
| the fold over stake info keeps an unnamed account's lookup | `validatorFold_keeps` |
| the treasury branch keeps an unnamed account's lookup | `treasuryStepRaw_keeps` |
| **`validatorUpdate` writes no key outside stake info ∪ treasury** | **`validatorUpdate_keeps`** |
| … with the input-overlay side condition discharged, as at the real call site | `validatorUpdate_keeps_ofTrie` |

The statement is *lookup preservation*, not "the write set is empty": `validatorUpdate` ends in
`o.commit`, which empties the prospective overlay, so `Avoids k o1` (the §5.1 invariant "`k` is absent
from `o.prosp`") holds vacuously for every key after the call and cannot express the write set. The
informative form is `Keeps k o o1 : o1.lookup k = o.lookup k` for an account `b` that no shard
stake-info entry names and that is not the treasury account.

`validatorUpdate_keeps` states that under two naming hypotheses (no shard stake-info entry names `b`,
and the treasury — when there is one — is not `b`) plus an `Avoids (kAccount b) o` side condition on
the *input* overlay. That side condition is not a real restriction at the call site: the runtime builds
the input overlay with `Ovl.ofTrie` (`D2/RuntimeD2.lean:178,235`), whose prospective overlay is empty,
so `Avoids` holds for every key by `rfl`. The corollary `validatorUpdate_keeps_ofTrie` states the result
with that hypothesis already discharged.

Read together: **§2's per-site arithmetic says each write moves the measure by the reward it carries;
§5 says the mint site cannot write any account it does not name.** The remaining per-site statement —
that no *other* site raises the measure — is still the table's argument over the source (§3).

---

## 3. What is not proved

These limits matter if the result is to be quoted.

* **The chunk statement does not carry `total_supply`.** `decodeBlockV6` (`Wire.lean:306`) decodes the
  header's field and discards it, and `checkD2CoreObs` (`ChunkValidationD2.lean:115-295`, the burnt comparison at `:260`) compares
  `H.prevBalanceBurnt` against the computed burnt amount but nothing about supply. So `Rel_D2`
  authenticates the *burnt* half of the supply identity and not the *minted* half. §3 of `Supply.lean`
  models the block-level check that supplies the missing half; wiring it into `Rel_D2` is successor
  work. Until then, "the Lean chunk statement enforces 2.5 %" would be an overstatement: the Lean
  chunk statement enforces `balanceBurnt`, and the block-level check — modelled but not yet related —
  enforces the mint side.
* **The enumeration in the site table is an argument over the source, not a proof.** Every balance
  write in the four D2 files goes through `Ovl.setAcct` or the gas-key balance field and is listed
  above; a machine-checked "these are all of them" needs symbolic execution of the whole runtime in
  the successor relation. The lemmas are the per-site half of that. §5.5 is the one place where the
  other half — "this site cannot reach any other key" — is machine-checked, and only for
  `validatorUpdate`'s write set. Note also that rows 5, 12 and 13 (deposit credits) are only
  conservative *in pairs* with the charge: `depositPair_total` is a two-account statement, so a
  per-write reading of those rows alone would wrongly show an increase.
* **Confinement constrains *where* the mint writes, not *how much*.** `validatorUpdate_keeps` proves
  that an unnamed account's trie lookup is unchanged, so the mint cannot credit an account outside the
  shard's stake info or the treasury. It says nothing about whether the reward each named account
  receives is the value `calculate_reward` computed; that is the next bullet's gap, and §5.5 does not
  narrow it. It also says nothing about the *other* sites in the table — their confinement is not
  proved in this module.
* **The per-site lemmas speak about the values written**, not about a sum over the trie. A global sum
  needs `PTrie.allKeys` completeness (`D2/TrieProps.lean:326,506` has the two halves) plus an injection
  from trie keys to accounts; not attempted here.
* **The reward *amounts* a chunk applies are not recomputed in Lean — and cannot be, from claim
  bytes.** This was the largest gap; its arithmetic half is now closed (§2.2), and what remains is a
  trust-boundary statement. In Rust the reward map comes from
  `epoch_manager.compute_stake_return_info` (`chain/chain/src/runtime/mod.rs:238-246`), which returns
  `EpochInfo.validator_reward` verbatim (`chain/epoch-manager/src/lib.rs:1274`) — the map
  `calculate_reward` produced. In Lean the rewards arrive inside the claim's facts
  (`applyFacts[k].validator_update`), and `checkD2CoreObs` checks only that a `validatorUpdate` is
  *present* exactly when the block starts an epoch (`ChunkValidationD2.lean:188-190`). The claim
  carries no production stats, `total_supply` or `epoch_duration`, so the ledger **cannot be
  recomputed from claim bytes**; `spec/claim-v3.md` classes `validator_update` as trusted (`T10`) and
  states that `Rel` "can only check the trusted values for internal consistency; it cannot check that
  they are true".

  What §2.2 closed is the arithmetic that used to be *assumed* on top of that trust. Previously the
  bound took `shares ≤ validatorBudget` as a hypothesis; now that is derived from the uptime clip
  `reward_calculator.rs:119-131` (`sumLedgerRows_le_budget`), and `minted_amount` is proved to be
  exactly the ledger total (`epochActualReward_eq_ledger`). The resulting bounds hold **whatever rows
  the trusted facts carry**: `mintedAmount_le_supply_div_40` for the header's quantity and
  `creditedRewards_le_supply_div_40` for the amount landing in accounts on one shard. So the statement
  a verifier can quote is *"no matter which rewards the trusted epoch-manager answer contains, the
  amount minted and credited is within 2.5 %"* — strictly stronger than the old *"…if the ledger is
  well-shaped"*, and still not *"…and the facts equal the computed ledger"*, which no claim-byte check
  can establish.
* **The Rust-to-Lean bridge for the formula is cited, not proved.** That the epoch manager's
  `minted_amount` is produced by `calculate_reward`, and that mainnet takes the hardcoded treasury
  branch, are facts about `reward_calculator.rs` established by reading it. What is proved is the
  bound on the formula and on the header check.
* **The minted amount in the header comes from the *next* epoch's info.** `chain.rs:2520-2522` reads
  `header.next_epoch_id()`'s `minted_amount`, i.e. the epoch *being entered*. That is the same value
  `calculate_reward` produced at the epoch boundary, but the Lean model treats the header's `minted`
  as an unconstrained input satisfying the identity — it does not prove the header's value equals any
  particular epoch's computed ledger.
* **`U256`/`u128` widths.** The Rust arithmetic is `U256` truncated to `u128`; the Lean model is `Nat`
  with explicit `≥ 2^128` guards, as `D2/Validators.lean` does. Truncation is a narrowing of the value
  bounded here, so the bound transfers.
* **`FunctionCall` actions' balance effects** live in D3's WASM host (`Wasm/Host.lean`); D2 hands the
  action to `hooks.functionCall` without modelling it. Their deposit accounting is the
  `actTransfer`-shaped surface above; the WASM side is out of scope for these two modules.
* **Staking and unstaking are balance-conserving here** (`stakeStep_total`), matching
  `action_stake` (`runtime/runtime/src/actions.rs:47-95`): the code moves `stake − locked` out of
  `amount` into `locked`, so the sum is unchanged. Note the locked amount is *not* a separate pot in the
  model: `locked` is part of the account's total, as in `Account::locked`.

---

## 4. Reproducing

```bash
cd spec/lean/v3
lake build NearSpecV3.Supply NearSpecV3.SupplyRuntime NearSpecV3.SupplyConfinement   # all three are in the default build too

# axiom audit (no `sorryAx`, no extra axioms)
cat > /tmp/Ax.lean <<'EOF'
import NearSpecV3.SupplyConfinement
open NearSpecV3.Supply NearSpecV3.SupplyRuntime NearSpecV3.D2
#print axioms supplyRun_year_increase_le
#print axioms validatorStep_total
-- §2.2 the clip and the amount bounds
#print axioms uptimeClipped_num_le_den
#print axioms sumLedgerRows_le_budget
#print axioms epochActualReward_eq_ledger
#print axioms mintedAmount_le_supply_div_40
#print axioms creditedRewards_le_supply_div_40
#print axioms lookupAmt_getD_le_sum
-- §5.5 confinement
#print axioms validatorUpdate_eq_entries
#print axioms validatorEntryStep_keeps
#print axioms validatorFold_keeps
#print axioms treasuryStepRaw_keeps
#print axioms validatorUpdate_keeps
#print axioms validatorUpdate_keeps_ofTrie
EOF
lake env lean /tmp/Ax.lean
```

Every theorem listed above reports only `propext`, `Quot.sound` and (where `simp`/`omega` reach it)
`Classical.choice`; there is no `sorry` in any of the three modules. The repo-wide `make lean` builds
all four Lean projects with these modules in `NearSpecV3`'s default target (the root module
`NearSpecV3.lean` imports all three; `make lean` on the v3 project reports 274 jobs).
