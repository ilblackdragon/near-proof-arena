import NearSpecV3.Supply

/-!
# §4 Supply accounting in the D2 runtime: the balance-write sites

`NearSpecV3/Supply.lean` proves the *formula* side: an epoch mints at most 2.5 % of supply and the
block header's check forces the supply identity. This file is the *runtime* side: which writes in
`D2/Actions.lean`, `D2/Receipts.lean`, `D2/RuntimeD2.lean` and `D2/Validators.lean` change the amount
of NEAR held in accounts, and by how much.

The accounting measure is

  `Σ_accounts (amount + locked) + Σ_gas_keys balance + tokensBurnt`

— NEAR in accounts, plus NEAR already destroyed. Each lemma below is the arithmetic of one write:
the change to that measure under the guards the surrounding code has already checked. Every write
either preserves it, lowers it (burn), or raises it by an amount charged to a deposit earlier in the
same receipt. Exactly one site raises it from nothing: `validatorUpdate`, whose raise is the shard's
validator rewards — the epoch's mint, bounded in §1.

## What this file does **not** prove

* **The reward amounts are taken from the claim's facts, not recomputed — and cannot be recomputed
  from claim bytes.** In Rust the reward map comes from `epoch_manager.compute_stake_return_info`
  (`chain/chain/src/runtime/mod.rs:238-246`), which returns `EpochInfo.validator_reward` verbatim
  (`chain/epoch-manager/src/lib.rs:1274`), i.e. the epoch manager's own `calculate_reward` ledger. In
  Lean the rewards arrive as `applyFacts[k].validator_update` in the claim, and `checkD2CoreObs` only
  checks that a `validatorUpdate` is *present* exactly when the block starts an epoch
  (`ChunkValidationD2.lean:188-190`). The claim carries no production stats, `total_supply` or
  `epoch_duration`, so there is nothing to recompute the ledger from; `spec/claim-v3.md` accordingly
  classes `validator_update` as *trusted* (`T10`).
  So the accounting below proves "the supply rises by exactly the rewards the facts claim", and §1/§2
  of `Supply.lean` prove "the epoch's ledger is at most 2.5 %" — with §2.2 deriving the shares' bound
  from the uptime clip rather than assuming it. **What is not in the relation is that the facts'
  rewards *equal* the computed ledger.** That residual is a trust-boundary statement, not an
  arithmetic one.
* The enumeration in §4.6 is an argument over the source, not a proof. A machine-checked "these are
  all the writes" needs symbolic execution of the whole runtime in the successor relation; the lemmas
  here are the per-site half of that.
* The lemmas speak about the *values written* by `Ovl.setAcct` / `Ovl.setAK`, not about a sum over
  the trie. A global sum needs `PTrie.allKeys` completeness (`D2/TrieProps.lean:326,506` has the two
  halves) plus an injection from trie keys to accounts; not attempted here. A successor invariant
  would consume the per-site statements.
* `validatorUpdate` (`Validators.lean:36-67`) is a `foldlM` over the shard's stake info; the per-entry
  step is `validatorStep`, whose accounting is `validatorStep_total`. The fold-level statement — the
  sum over all entries — is a straightforward induction on the list, but it needs the overlay's
  read-after-write discipline (`getAcct_setAcct`, provided) and is left to successor work.
  Note that `validatorStep` here is the *pure* `Acct → Acct` map of one entry; the *monadic* overlay
  step is `validatorEntryStep` in `SupplyConfinement.lean` (§5.5.1), which wraps this arithmetic in
  the code's guard checks and the `setAcct` write. §5.5 does carry its induction over the same
  `foldlM` to a conclusion — but for *write confinement* (`validatorFold_keeps`), not for the sum.
* A `FunctionCall` action's balance effects live in D3's WASM host (`Wasm/Host.lean`); D2 hands the
  action to `hooks.functionCall` without modelling it. Its deposit accounting is the
  `actTransfer`-shaped surface below; the WASM side is out of this file's scope.
-/

namespace NearSpecV3.D2

/-- The balance an access key holds (`AccessKeyPermission::gas_key` balance; 0 for other keys). This
NEAR is held against the key, not the account (`actions.rs:103-120`). -/
def AK.gasBal (k : AK) : Nat := match k.perm.gasInfo with | some (b, _) => b | none => 0

theorem AK.gasBal_setGasBalance {k : AK} {b : Nat} (h : k.perm.gasInfo.isSome = true) :
    { k with perm := k.perm.setGasBalance b }.gasBal = b := by
  obtain ⟨nonce, perm⟩ := k
  cases perm with
  | fc p => simp [Perm.gasInfo] at h
  | full => simp [Perm.gasInfo] at h
  | gasFc bal n p => simp [AK.gasBal, Perm.setGasBalance, Perm.gasInfo]
  | gasFull bal n => simp [AK.gasBal, Perm.setGasBalance, Perm.gasInfo]

end NearSpecV3.D2

namespace NearSpecV3.SupplyRuntime

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Supply

/-! ## §4.2 Read-after-write on the overlay

The per-site arithmetic is about the value written; connecting it to the runtime needs the fact that
a `setAcct` is what a later `getAcct` of the same account reads. -/

theorem kvFind_put_same (k : Bytes) (v : Option Bytes) (l : List (Bytes × Option Bytes)) :
    kvFind k (kvPut k v l) = some v := by
  induction l with
  | nil => simp [kvPut, kvFind]
  | cons p ps ih =>
    obtain ⟨k', v'⟩ := p
    by_cases h : k' = k
    · subst h; simp [kvPut, kvFind]
    · simp [kvPut, kvFind, h, ih]

theorem lookup_setAcct (o : Ovl) (a : Bytes) (x : Acct) :
    (o.setAcct a x).lookup (kAccount a) = some (some x.encode) := by
  simp [Ovl.setAcct, Ovl.set, Ovl.lookup, kvFind_put_same]

/-! ## §4.3 The minting site: `validatorUpdate`

`update_validator_accounts` (`runtime/runtime/src/lib.rs:1599-1716`), modelled at
`D2/Validators.lean:36-67`. For a stake-info entry on this shard the code computes

  `locked := locked + r`;  `ret := locked − max(maxStake, lastProposal)`;
  writes  `locked := locked − ret`,  `amount := amount + ret`

so `amount + locked` grows by exactly the reward `r`, whatever the stake invariant says. The treasury
branch adds `r` to `amount` directly. These are the only two raises in the D2 runtime not matched by
a debit.
-/

/-- The per-entry account update of `validatorUpdate` (`Validators.lean:45-52`). -/
def validatorStep (x : Acct) (maxStake lastP r : Nat) : Acct :=
  let locked := x.locked + r
  let ret := locked - max maxStake lastP
  { x with locked := locked - ret, amount := x.amount + ret }

/-- **The validator update raises the account's total by exactly its reward.** -/
theorem validatorStep_total (x : Acct) (maxStake lastP r : Nat) :
    (validatorStep x maxStake lastP r).total = x.total + r := by
  unfold validatorStep Acct.total
  simp only
  omega

/-- The treasury branch's update (`Validators.lean:64`): `amount := amount + r`. -/
theorem treasuryStep_total (x : Acct) (r : Nat) :
    ({ x with amount := x.amount + r } : Acct).total = x.total + r := by
  unfold Acct.total
  simp only
  omega

/-- A validator update never lowers the total: the reward is non-negative. -/
theorem validatorStep_total_ge (x : Acct) (maxStake lastP r : Nat) :
    x.total ≤ (validatorStep x maxStake lastP r).total := by
  rw [validatorStep_total]
  exact Nat.le_add_right _ _

/-- A validator update moves money only: storage usage and the contract are untouched. -/
theorem validatorStep_usage (x : Acct) (maxStake lastP r : Nat) :
    (validatorStep x maxStake lastP r).usage = x.usage := rfl

/-! ## §4.4 Conservation and burn sites

The arithmetic of each remaining balance write in `D2/Actions.lean` and `D2/Receipts.lean`, with the
guards the code checks before writing. -/

/-- `actStake` (`Actions.lean:296-305`): moving `stake − locked` from `amount` into `locked` leaves
the total unchanged. Guards: the account covers the increase (`inc ≤ amount`, else the action fails)
and the stake does not decrease (`locked ≤ stake`, the `stake > x.locked` branch). -/
theorem stakeStep_total {x : Acct} {stake : Nat} (hl : x.locked ≤ stake)
    (ha : stake - x.locked ≤ x.amount) :
    ({ x with amount := x.amount - (stake - x.locked), locked := stake } : Acct).total = x.total := by
  unfold Acct.total
  simp only
  omega

/-- `actFromGasKey` (`Actions.lean:376-387`): `amount += amt` funded by `gasBal −= amt`; the total of
account + key is unchanged. Guard: `b ≥ amt`, else the action fails. -/
theorem fromGasKeyStep_total {amount b amt : Nat} (h : amt ≤ b) :
    (amount + amt) + (b - amt) = amount + b := by omega

/-- `actToGasKey` (`Actions.lean:366-374`): `gasBal += dep`, account unchanged — the total rises by
`dep`, the action's attached deposit, charged to the sender before execution
(`TxCostD2.totalCost = gasCost + totalDeposit`, `Fees.lean:382-384`). -/
theorem toGasKeyStep_total {amount b dep : Nat} :
    amount + (b + dep) = (amount + b) + dep := by omega

/-- `actDeleteKey` on a gas key (`Actions.lean:280-291`): the key's balance `bal` leaves the key and
enters `tokensBurnt`; `gasBal + tokensBurnt` is conserved and the account's own balance is untouched. -/
theorem deleteGasKeyStep_total {b bal burnt : Nat} (h : bal ≤ b) :
    (b - bal) + (burnt + bal) = b + burnt := by omega

/-- The receiver's gas reward (`Receipts.lean:172-181`): `amount += rew` funded by `tb −= rew`, so
`amount + tokensBurnt` is conserved. Guard: `rew ≤ tb`, else the receipt panics. -/
theorem receiverRewardStep_total {amount rew tb : Nat} (h : rew ≤ tb) :
    (amount + rew) + (tb - rew) = amount + tb := by omega

/-- The transaction charge (`TxD2.lean:150-159`, `Fees.lean:366-384`): the signer's amount drops by
`totalCost = gasCost + depositCost`, so the charge only lowers supply. -/
theorem chargeStep_total {amount totalCost : Nat} (h : totalCost ≤ amount) :
    amount - totalCost + totalCost = amount := by omega

/-- A deposit-funded increase plus its charge conserves the measure: the sender's amount drops by
`dep` (`chargeStep_total`) and the receiver's rises by `dep` (`actTransfer`, both branches, and
`actToGasKey`). Guard: the sender covers the deposit, which the charge's
`available_balance >= total_cost` check (`verifier.rs:315`) enforces. -/
theorem depositPair_total {senderAmount receiverAmount dep : Nat} (h : dep ≤ senderAmount) :
    (senderAmount - dep) + (receiverAmount + dep) = senderAmount + receiverAmount := by omega

/-- A failed receipt's deposit refund (`Receipts.lean:70-100`: `depRefund = dep` when `!res.ok`)
returns exactly the deposit that was charged: net zero over the pair. Guard: the account covered the
deposit when it was charged. -/
theorem refundStep_total {amount dep : Nat} (h : dep ≤ amount) :
    (amount - dep) + dep = amount := by omega

/-- `actDeleteAccount` (`Actions.lean:221-248`): the account disappears (`account := none`), its
`amount` leaves as a refund transfer receipt to the beneficiary, and its gas-key balance `gsum` enters
`tokensBurnt`. The measure is conserved when the refund receipt executes; until then the amount sits
in the outgoing receipt. -/
theorem deleteAccountStep_total {amount gsum burnt : Nat} :
    ((0 : Nat) + (burnt + gsum)) + amount = (amount + burnt) + gsum := by omega

/-! ## §4.5 Through the runtime function

`actStake`'s write site, proved through the definition: a successful `actStake` leaves the receiver
account's total unchanged. This is the style the rest of the table needs — unfold the runtime
function, find the write, apply the arithmetic lemma. -/

theorem actStake_ok_total {c : ActCtx} {st : ActSt} {res : AR} {stake : Nat}
    {pk : NearSpec.PublicKey} {st' : ActSt} {res' : AR}
    (h : actStake c st res stake pk = .ok (st', res')) {x : Acct} (hx : st.account = some x) :
    ∃ x', st'.account = some x' ∧ x'.total = x.total := by
  unfold actStake at h
  simp only [needAcct, ok?, hx, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨x, h.1.symm ▸ hx, rfl⟩
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨x, h.1.symm ▸ hx, rfl⟩
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨x, h.1.symm ▸ hx, rfl⟩
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          refine ⟨⟨x.amount - (stake - x.locked), stake, x.usage, x.contract, x.v2⟩, ?_, ?_⟩
          · rw [← h.1]
          · simp only [Acct.total]; omega
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨x, h.1.symm ▸ hx, rfl⟩

/-! ## §4.6 The inventory of balance-writing sites

Every write to `Acct.amount`, `Acct.locked` or a gas-key balance in the D2 runtime, with its effect on
the measure `Σ(amount + locked) + Σ gasBal + tokensBurnt`. The two "mint" rows are the epoch's
rewards; every other row conserves or burns. Lines are `spec/lean/v3/NearSpecV3/...`.

| # | site | location | effect |
|---|------|----------|--------|
| 1 | `validatorUpdate`, stake-info branch | `D2/Validators.lean:42-55` | **+ reward** (`validatorStep_total`) |
| 2 | `validatorUpdate`, treasury branch | `D2/Validators.lean:56-66` | **+ reward** (`treasuryStep_total`) |
| 3 | `actStake` | `D2/Actions.lean:296-305` | 0 (`actStake_ok_total`) |
| 4 | `actFromGasKey` | `D2/Actions.lean:376-387` | 0 (`fromGasKeyStep_total`) |
| 5 | `actToGasKey` | `D2/Actions.lean:366-374` | + deposit, charged before (`toGasKeyStep_total`) |
| 6 | `actDeleteKey`, gas key | `D2/Actions.lean:280-291` | − bal, to `tokensBurnt` (`deleteGasKeyStep_total`) |
| 7 | `actDeleteKey`, plain key | `D2/Actions.lean:292-294` | 0 |
| 8 | `actDeleteAccount` | `D2/Actions.lean:221-248` | − amount − gsum, refund receipt + amount, burnt + gsum (`deleteAccountStep_total`) |
| 9 | `actAddKey` | `D2/Actions.lean:250-267` | 0 |
| 10 | `actCreateAccount` | `D2/Actions.lean:389-395` | 0 (`Acct.new 0 0`) |
| 11 | `actDeploy` | `D2/Actions.lean:357-364` | 0 |
| 12 | `actTransfer`, existing account | `D2/Actions.lean:307-341` | + deposit, charged before |
| 13 | `actTransfer`, implicit creation | `D2/Actions.lean:342-355` | + deposit, charged before |
| 14 | `applyActionReceipt`, receiver reward | `D2/Receipts.lean:172-181` | 0 (`receiverRewardStep_total`) |
| 15 | `processTxD2`, success / depositFailed | `D2/RuntimeD2.lean:24-72` | − totalCost, or 0 (`chargeStep_total`) |
| 16 | `verifyRegular` / `verifyGasKey` | `D2/TxD2.lean:117-159` | − totalCost / − burnt |
| 17 | `refunds` | `D2/Receipts.lean:70-100` | refund receipt of the charged deposit (`refundStep_total`) |

Rows 1–2 are reached only from `applyNewChunkD2` step 1 and `applyMissingChunkD2`
(`D2/RuntimeD2.lean:179-182, 236-238`), and only when the chunk's facts carry a `validatorUpdate`
(`D2/Validators.lean:36`, fed from the claim's `applyFacts[k].validator_update`,
`ChunkValidationD2.lean:227`). With `vu = none` no row raises the measure at all — the chunk's
transition conserves or burns.

Rows 5, 12 and 13 raise the measure by a deposit that row 15 or 16 already took from the sender's
`amount`, so the pair (charge, credit) conserves it (`depositPair_total`); row 15's failed-transaction
path returns the deposit by row 17. Row 14 moves burnt tokens back into an account, so it conserves
`amount + tokensBurnt`. Row 6 and row 8's `gsum` convert account/key balance into burnt tokens.
-/

/-- **Nothing is minted without a validator update.** A chunk whose facts carry no `validatorUpdate`
(`vu = none`) has no balance-raising write: rows 1–2 are its only raisers, and both are behind the
`match vu with | some f => ...` guard. This is a statement about the inventory above, made checkable
as a predicate on the facts. -/
def hasMintSite (vu : Option ValidatorUpdateFacts) : Bool := vu.isSome

theorem noMintSite_of_none {vu : Option ValidatorUpdateFacts} (h : vu = none) :
    hasMintSite vu = false := by
  simp [hasMintSite, h]

theorem mintSite_of_some {vu : Option ValidatorUpdateFacts} (h : vu ≠ none) :
    hasMintSite vu = true := by
  cases vu with
  | none => exact absurd rfl h
  | some f => rfl

/-! ## §4.7 What the mint site can read

§4.6 says `validatorUpdate` is the only site that raises the measure. This subsection records the one
data-flow fact the amount bound needs: the reward a single stake-info entry receives,
`lookupAmt rewards a`, is one entry of the list the fold reads, so it is at most that list's total.

`NearSpecV3/Supply.lean` §2.2 then bounds a ledger of that shape by the epoch's mint. What is **not**
proved — and cannot be, from claim bytes — is that the claim's `validatorRewards` list *is* the epoch
manager's ledger: `validator_update` is a trusted claim value (`spec/claim-v3.md` T10), and the claim
carries no production stats, `total_supply`, or epoch duration from which to recompute it. -/

/-- A list element's value is at most the list's sum of values (non-negative). -/
theorem mem_le_sumNat {α : Type} {l : List α} {f : α → Nat} {x : α} (h : x ∈ l) :
    f x ≤ sumNat (l.map f) := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.map_cons, sumNat]
    rcases List.mem_cons.mp h with rfl | htail
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih htail) (Nat.le_add_left _ _)

/-- **Every reward the `validatorUpdate` fold can pay is at most the sum of the reward list it reads.**
`lookupAmt` finds one entry of the list, so the amount written to that account is one summand of the
list's total. -/
theorem lookupAmt_getD_le_sum (l : List (Bytes × Nat)) (a : Bytes) :
    (lookupAmt l a).getD 0 ≤ sumNat (l.map (·.2)) := by
  unfold lookupAmt
  cases hf : List.find? (fun p => p.1 == a) l with
  | none => simp
  | some p =>
    have hmem : p ∈ l := List.mem_of_find?_eq_some hf
    simp only [Option.map_some, Option.getD_some]
    exact mem_le_sumNat hmem

end NearSpecV3.SupplyRuntime
