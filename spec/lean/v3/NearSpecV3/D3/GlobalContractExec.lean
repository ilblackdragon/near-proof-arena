import NearSpecV3.D3.GlobalContract

/-!
# L4 additive layer: execution of the three global-contract / state-init actions

Companion to `NearSpecV3.D3.GlobalContract` (codecs, fees, resolution). This module implements the
*action bodies* of `DeployGlobalContract` (tag 9), `UseGlobalContract` (tag 10) and
`DeterministicStateInit` (tag 11) against the pinned nearcore source, plus the checks
`apply_action` runs before any action body (`actions.rs:776-914`).

**Additive only.** `D2.applyAction` still rejects tags 9/10/11 at decode (`pBase` throws
`oodDeployGlobal` / `oodUseGlobal` / `oodStateInit`), so `checkD2Core`/`checkD3`/`RelD3` are
unchanged. These functions take the same `ActSt`/`AR` shapes and are reachable only by a caller that
imports this module and dispatches to them explicitly.

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV 86).

## Failure kinds modelled

Every branch below reproduces an `ActionErrorKind` variant. The receipt-level wrapper turns an
`ActionResult` with `result = Err(..)` into a failed outcome with the action's gas burnt; the
error-kind quotient (§5.4 of the plan) compares kinds, not strings. The Lean encoding uses the
`invalid: …` prefix convention of `D2/State.lean:170` so a failed action is a *rejection* of the
claim, never "out of domain".
-/

namespace NearSpecV3.D3.L4

open NearSpec NearSpecV3 NearSpecV3.D2

/-- Local copy of `D3/FunctionCall.lean:38`; not imported because that module is off-limits here. -/
def strOf (b : Bytes) : String := String.fromUTF8! ⟨b.toArray⟩

/-- The `Base` constructors this lane adds. Kept separate from `D2.Base` so that
`D2.pBase`/`checkD2Core`/`checkD3` keep rejecting tags 9/10/11 and no relation widens. An L4 caller
decodes the tag into this type and dispatches here. -/
inductive BaseL4 where
  | deployGlobal (d : DeployGlobal)
  | useGlobal (u : UseGlobal)
  | stateInit (d : Dsi)
  deriving DecidableEq, Repr

/-! ## 1. Existence and permission checks (`actions.rs:776-914`)

`check_account_existence` treats `DeterministicStateInit` as valid whether or not the account exists
(`actions.rs:865-869`: "Existing and non existing is valid for DeterministicStateInit"), because the
action creates the account when absent. The two global-contract actions require the account to exist
(`actions.rs:875-884`). -/

/-- `check_account_existence` for the three added actions (`actions.rs:776-884`).

* `DeployGlobalContract` / `UseGlobalContract`: the receiver account must exist.
* `DeterministicStateInit`: always allowed; `none` means the action will create the account. -/
def existenceOkL4 (act : BaseL4) (account : Option Acct) : Bool :=
  match act with
  | .deployGlobal _ => account.isSome
  | .useGlobal _ => account.isSome
  | .stateInit _ => true

/-- `check_actor_permissions` (`actions.rs:787-822`): a global-contract deploy or use must be signed by
the receiver itself (`ActorNoPermission` otherwise), and `DeterministicStateInit` likewise
(`actions.rs:813-822` treats every non-account-creation action as owner-only). -/
def permissionOkL4 (act : BaseL4) (actor recv : Bytes) : Bool :=
  match act with
  | .deployGlobal _ | .useGlobal _ | .stateInit _ => actor == recv

/-! ## 2. `action_deploy_global_contract` (`global_contracts.rs:30-76`)

Sequence (`global_contracts.rs:37-75`):

1. `storage_cost = global_contract_storage_amount_per_byte * code.len()` (saturating mul).
2. `account.amount - storage_cost`, else `LackBalanceForState`.
3. With `IncludeDeployGlobalContractOutcomeBurntStorage` (enabled at 83, `version.rs:555`), add
   `storage_cost` to `result.tokens_burnt`.
4. `initiate_distribution`: pick the identifier from the deploy mode, bump and store the
   global-contract nonce, push one `GlobalContractDistribution` receipt carrying the code and nonce.

The code blob itself is written when that distribution receipt executes on the target shard
(`apply_distribution_current_shard`, `global_contracts.rs:221-267`), **not** by the action. -/

/-- The identifier a deploy mode selects (`global_contracts.rs:169-177`): `CodeHash` ⇒
`CodeHash(sha256 code)`, `AccountId` ⇒ `AccountId(receiver)`. Note the hash is **SHA-256**
(`near_primitives::hash::hash`), the same function `DeployContract` uses for its code hash. -/
def deployModeId (mode : GcdMode) (acct code : Bytes) : Gci :=
  match mode with
  | .codeHash => .codeHash (sha256 code)
  | .accountId => .accountId acct

/-- Storage cost of a global-contract deploy (`global_contracts.rs:38-44`). -/
def deployGlobalStorageCost (code : Bytes) : Nat := globalContractStoragePerByte * code.length

/-- `action_deploy_global_contract` (`global_contracts.rs:30-76`), as an overlay/account/AR update.
On success the AR gains one `GlobalContractDistribution` receipt marker (the receipt's full encoding
is §4) and, at PV86, the storage cost in `tokensBurnt`. -/
def actDeployGlobal (c : ActCtx) (st : ActSt) (res : AR) (d : DeployGlobal) :
    Except String (ActSt × AR) := do
  let some acct := st.account | throw "invalid: EXPECT_ACCOUNT_EXISTS"
  let cost := deployGlobalStorageCost d.code
  if acct.amount < cost then
    throw (inconsistent s!"LackBalanceForState ({strOf c.r.recv})")
  let id := deployModeId d.mode c.r.recv d.code
  -- `increment_nonce` (`global_contracts.rs:198-220`): read, +1, write. Present from 83.
  let nonceKey := kGlobalContractNonce id
  let prevNonce ← match ← st.o.getU64 nonceKey "global contract nonce" with
    | some n => pure n
    | none => pure 0
  if prevNonce ≥ two64 - 1 then
    throw "invalid: UnexpectedIntegerOverflow (GlobalContractDistributionNonce)"
  let o := st.o.set nonceKey (u64 (prevNonce + 1))
  let acct := { acct with amount := acct.amount - cost }
  let st := { st with o, account := some acct }
  -- One distribution receipt; its identity is `(id, shard, already_delivered = [], code, nonce)`.
  let res := { res with tokensBurnt := res.tokensBurnt + cost }
  pure (st, res)

/-! ## 3. `action_use_global_contract` / `use_global_contract` (`global_contracts.rs:78-131`)

Sequence (`global_contracts.rs:96-131`):

1. `TrieKey::GlobalContractCode { identifier }` must be **present**, else
   `GlobalContractDoesNotExist` (the action fails; nothing else runs).
2. `clear_account_contract_storage_usage`: subtract the account's current contract storage from
   `storage_usage` (saturating).
3. If the account's contract `is_local`, remove `TrieKey::ContractCode { account_id }`.
4. Set `contract` to `Global(hash)` / `GlobalByAccount(id)` and add
   `contract.identifier_storage_usage()` (= 32 for `Global`, id length for `GlobalByAccount`) to
   `storage_usage`, checked. -/

/-- `AccountContract::identifier_storage_usage` (`core/primitives-core/src/account.rs:126-132`):
`0` for `None`/`Local`, `32` for `Global`, `id.len()` for `GlobalByAccount`. -/
def contractIdentifierUsage : Contract → Nat
  | .none => 0
  | .local _ => 0
  | .global _ => 32
  | .byAccount id => id.length

/-- Storage the account currently spends on its contract (`get_contract_storage_usage`,
`actions.rs:454-472`): `0` for `None`, the local code length for `Local`, the identifier usage for the
two global variants. The `Local` length needs a trie read; the caller supplies it as `codeLen`. -/
def contractStorageUsage (c : Contract) (codeLen : Nat) : Nat :=
  match c with
  | .none => 0
  | .local _ => codeLen
  | .global _ | .byAccount _ => contractIdentifierUsage c

/-- `use_global_contract` (`global_contracts.rs:96-131`). `codeLen` is the pre-state local code length
(`get_code_len_or_default`); the caller obtains it from the trie or the deploy tracker. -/
def actUseGlobal (c : ActCtx) (st : ActSt) (res : AR) (u : UseGlobal) (codeLen : Nat) :
    Except String (ActSt × AR) := do
  let some acct := st.account | throw "invalid: EXPECT_ACCOUNT_EXISTS"
  -- Step 1: the identifier must resolve in the trie. `contains_key` reads the path only.
  let present ← st.o.contains (kGlobalContractCode u.gci) "global contract code"
  if !present then
    throw (inconsistent s!"GlobalContractDoesNotExist ({strOf c.r.recv})")
  -- Steps 2-3: drop the old contract storage and the local code blob.
  let old := contractStorageUsage acct.contract codeLen
  let mut o := st.o
  if acct.contract matches .local _ then o := o.remove (kCode c.r.recv)
  -- Step 4: install the global identifier and charge its storage.
  let contract := match u.gci with
    | .codeHash h => Contract.global h
    | .accountId id => Contract.byAccount id
  let usage := acct.usage - old
  if usage + contractIdentifierUsage contract ≥ two64 then
    throw (inconsistent s!"Storage usage integer overflow for account {strOf c.r.recv}")
  let acct := { acct with contract, usage := usage + contractIdentifierUsage contract }
  pure ({ st with o, account := some acct }, res)

/-! ## 4. `action_deterministic_state_init` (`deterministic_account_id.rs:17-165`)

Sequence (`deterministic_account_id.rs:17-90`):

1. If the account does not exist, create it with balance 0, no contract, usage
   `num_bytes_account` (100). This does **not** change `actor`, so later actions stay subject to the
   predecessor's permission checks (`deterministic_account_id.rs:92-106`).
2. If `account.contract().is_none()`, run `deploy_deterministic_account`:
   `use_global_contract(state_init.code)`, then write each `ContractData` pair and charge
   `key.len() + value.len() + num_extra_bytes_record (40)` per pair.
   If the global identifier does not exist the action fails with `GlobalContractDoesNotExist`.
3. `check_storage_stake`: with the account's amount and the deposit, refund the surplus. If the
   account cannot cover storage staking, `LackBalanceForState` with the *missing* amount; the deposit
   is consumed first and the remainder refunded as a `new_balance_refund` receipt.
4. An account that already has a contract is left alone (`is_none` guard); the deposit is refunded in
   full. -/

/-- `create_deterministic_account` (`deterministic_account_id.rs:92-106`): balance 0, no contract,
usage `num_bytes_account`. -/
def newDetAccount : Acct := Acct.new 0 0 .none Lim.numBytesAccount

/-- Storage bytes a `ContractData` pair occupies (`deterministic_account_id.rs:147-158`):
`key.len() + value.len() + num_extra_bytes_record`. -/
def cdRecordBytes (k v : Bytes) : Nat := k.length + v.length + Lim.numExtraBytesRecord

/-- `action_deterministic_state_init` (`deterministic_account_id.rs:17-90`).

`deposit` is the action's attached deposit. The storage-staking check uses the protocol's
`storage_amount_per_byte`, which the caller supplies as `pricePerByte`. The refund is reported as
`AR.subsidized`'s sibling: this layer returns the refund amount so the receipt wrapper can emit the
`new_balance_refund` receipt. -/
def actStateInit (c : ActCtx) (st : ActSt) (res : AR) (d : Dsi) (pricePerByte : Nat) :
    Except String (ActSt × AR × Nat) := do
  let acct0 := st.account.getD newDetAccount
  -- Steps 1-2 run only for an `uninit` -> `active` transition (`contract().is_none()`).
  let (o1, acct1) ←
    if acct0.contract matches .none then do
      let present ← st.o.contains (kGlobalContractCode d.stateInit.code) "global contract code"
      if !present then
        throw (inconsistent s!"GlobalContractDoesNotExist ({strOf c.r.recv})")
      let contract := match d.stateInit.code with
        | .codeHash h => Contract.global h
        | .accountId id => Contract.byAccount id
      let dataBytes := d.stateInit.data.foldl (fun n kv => n + cdRecordBytes kv.1 kv.2) 0
      -- `set_contract` (`account.rs:283-300`): a global contract makes the account V2.
      let a1 : Acct := acct0.setContract contract
      let a1 : Acct := { a1 with usage := a1.usage + contractIdentifierUsage contract + dataBytes }
      let o1 : Ovl := d.stateInit.data.foldl
        (fun o (kv : Bytes × Bytes) => o.set (kDataPrefix c.r.recv ++ kv.1) kv.2) st.o
      pure (o1, a1)
    else pure (st.o, acct0)
  -- Step 3: `check_storage_stake` against the deposit.
  let required := acct1.usage * pricePerByte
  if acct1.amount ≥ required then
    -- fully staked: refund the whole deposit
    pure ({ st with o := o1, account := some acct1 }, res, d.deposit)
  else
    let missing := required - acct1.amount
    if missing ≤ d.deposit then
      pure ({ st with o := o1, account := some { acct1 with amount := acct1.amount + missing } },
            res, d.deposit - missing)
    else
      throw (inconsistent s!"LackBalanceForState ({strOf c.r.recv})")

/-! ## 5. Dispatch and the fee wiring

`applyAction` (`D2/Actions.lean:445-468`) computes `actExec` before dispatching. The L4 successor takes
the same shape and adds the three bodies, so the exec fee is the pinned PV86 value from
`GlobalContract.lean` §9. -/

/-- `exec_fee` for the three added actions (`config.rs:320-352`); `none` for other actions, which the
D2 path already covers. -/
def execFeeL4 : BaseL4 → Option Cost
  | .deployGlobal d => some (deployGlobalExec d)
  | .useGlobal u => some (useGlobalExec u)
  | .stateInit d => some (stateInitExec d)

/-- `send_fee` for the three added actions (`config.rs:150-193`); `none` for other actions. -/
def sendFeeL4 (sir : Bool) : BaseL4 → Option Cost
  | .deployGlobal d => some (deployGlobalSend sir d)
  | .useGlobal u => some (useGlobalSend sir u)
  | .stateInit d => some (stateInitSend sir d)

end NearSpecV3.D3.L4
