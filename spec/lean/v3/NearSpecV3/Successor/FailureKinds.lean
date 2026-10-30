import NearSpecV3.D2.TxD2
import NearSpecV3.D2.GlobalTypes
import NearSpecV3.D3.GlobalContract

/-!
# Failure kinds of failed outcomes (W01, observation only)

nearcore's outcome status `Failure(TxExecutionError)` names *why* a transaction or receipt failed
(`InvalidTxError::…`, `ActionError { index, kind }`). The outcome hash commits only to the
`Failure` tag (`PartialExecutionStatus`), so the checker's verdict never depends on the kind, and
the action/transaction code in `D2/Actions`, `Logged/D2Actions` and `Logged/D2Runtime` returns only
`ok = false`.

This module recovers the kind for the differential comparison: given the state *before* the failed
action (or transaction) and the action itself, it re-evaluates the same conditions the action code
evaluated, **in nearcore's order**, and returns the name of the first one that fails. It is called
only after the real code reported a failure, and its answer is emitted (`--emit-full`), never read
by a check. Every pinned source line the order follows is cited at the condition.

Kinds are dotted variant paths: `AccountDoesNotExist`,
`DelegateActionAccessKeyError.AccessKeyNotFound`, `ActionsValidation.DeleteActionMustBeFinal`. Payloads
(account ids, amounts, nonces) are not part of the kind. The driver adds the `ActionError[i].` /
`InvalidTxError.` prefix. A condition the classifier cannot evaluate (a missing read) yields
`Unclassified`, which the comparator reports as a mismatch.
-/

namespace NearSpecV3.Successor.FailureKinds

open NearSpec NearSpecV3 NearSpecV3.D2

def unclassified : String := "Unclassified"

private def orU {α : Type} (x : Except String α) (k : α → String) : String :=
  match x with
  | .ok v => k v
  | .error _ => unclassified

/-- `check_account_existence` (`actions.rs:824-892`) on a failed `existenceOk`. -/
def existenceKind (act : Act) (account : Option Acct) : String :=
  match act with
  | .base ⟨_, .createAccount⟩ =>
    if account.isSome then "AccountAlreadyExists" else "OnlyImplicitAccountCreationAllowed"
  | _ => "AccountDoesNotExist"

/-- `check_actor_permissions` (`actions.rs:776-822`) on a failed `permissionOk`: `ActorNoPermission`
first, then (DeleteAccount) `DeleteAccountStaking`. -/
def permissionKind (act : Act) (actor recv : Bytes) : String :=
  match act with
  | .base ⟨_, .deleteAccount _⟩ => if actor != recv then "ActorNoPermission" else "DeleteAccountStaking"
  | _ => "ActorNoPermission"

/-- `apply_delegate_action` (`actions.rs:487-520`) and `validate_delegate_action_key`
(`actions.rs:600-745`), on the conditions `actDelegate(L)` evaluates. -/
def delegateKind (c : ActCtx) (st : ActSt) (d : Delegate) : String :=
  let sigOk := match d.sigTag, d.pk.tag with
    | 0, 0 => Ed25519.verify d.pk.data d.sig d.signedHash
    | 1, 1 => Secp256k1.verify d.pk.data d.sig d.signedHash
    | 2, 2 => MlDsa65.verify d.pk.data d.sig d.signedHash
    | _, _ => false
  let h := c.env.ctx.height
  if !sigOk then "DelegateActionInvalidSignature"
  else if h > d.maxHeight then "DelegateActionExpired"
  else if d.sender != c.r.recv then "DelegateActionSenderDoesNotMatchTxReceiver"
  else orU (st.o.getAK d.sender d.pk) fun
    | none => "DelegateActionAccessKeyError.AccessKeyNotFound"
    | some k =>
      let cur : Except String (Except String Nat) := match d.nonceIdx with
        | none => if k.perm.gasInfo.isSome
            then .ok (.error "DelegateActionAccessKeyError.DelegateActionRequiresNonGasKey")
            else .ok (.ok k.nonce)
        | some i => match k.perm.gasInfo with
          | none => .ok (.error "DelegateActionAccessKeyError.DelegateActionRequiresGasKey")
          | some (_, n) =>
            if i ≥ n then .ok (.error "DelegateActionInvalidNonceIndex")
            else match st.o.getU64 (kNonce d.sender d.pk i) "gas key nonce" with
              | .ok (some v) => .ok (.ok v)
              | _ => .error "missing"
      orU cur fun
        | .error kind => kind
        | .ok cur =>
          if d.nonce ≤ cur then "DelegateActionInvalidNonce"
          else if d.nonce ≥ h * Lim.nonceMult then "DelegateActionNonceTooLarge"
          else match k.perm.fcPerm with
            | none => unclassified
            | some fc => match d.actions with
              | [⟨_, .fcall m _ _ dep⟩] =>
                if dep > 0 then "DelegateActionAccessKeyError.DepositWithFunctionCall"
                else if d.receiver != fc.receiver then "DelegateActionAccessKeyError.ReceiverMismatch"
                else if !fc.methods.isEmpty && !fc.methods.contains m then
                  "DelegateActionAccessKeyError.MethodNameMismatch"
                else unclassified
              | _ => "DelegateActionAccessKeyError.RequiresFullAccess"

/-- The kind of a failed non-VM action, from the state before it. Existence, then permission
(`apply_action`, `lib.rs:567-600`), then the action body. Function calls that reached the VM are
classified by the driver from the VM's own error; a call that did not reach it is
`CodeDoesNotExist` (`function_call.rs`, `Contract.none`). -/
def actionKind (c : ActCtx) (st : ActSt) (act : Act) : String :=
  let recv := c.r.recv
  let elig := c.nActs == 1 && c.r.pred != AccountId.system
  if !existenceOk act st.account recv elig then existenceKind act st.account
  else if !permissionOk act st.account st.actor recv then permissionKind act st.actor recv
  else match act with
  | .delegate _ d => delegateKind c st d
  | .base ⟨_, b⟩ => match b, st.account with
    | .createAccount, _ =>
      -- `action_create_account` (`actions.rs:150-190`)
      if isTopLevel recv then "CreateAccountOnlyByRegistrar" else "CreateAccountNotAllowed"
    | .fcall _ _ _ _, _ => "FunctionCallError.CompilationError.CodeDoesNotExist"
    | .stake stake _, some x =>
      -- `action_stake` (`actions.rs:50-95`)
      if x.amount < stake - x.locked then "TriesToStake"
      else if x.locked == 0 && stake == 0 then "TriesToUnstake"
      else "InsufficientStake"
    | .addKey _ _, _ => "AddKeyAlreadyExists"
    | .deleteKey pk, _ =>
      -- `action_delete_key` (`access_keys.rs:70-110`)
      orU (st.o.getAK recv pk) fun
        | none => "DeleteKeyDoesNotExist"
        | some _ => "GasKeyBalanceTooHigh"
    | .deleteAccount _, some x =>
      -- `action_delete_account` (`actions.rs:370-400`)
      orU (contractUsage st.o recv x) fun cs =>
        if x.usage - cs > Lim.maxAccountDeletionUsage then "DeleteAccountWithLargeState"
        else "GasKeyBalanceTooHigh"
    | .toGasKey _ _, _ => "GasKeyDoesNotExist"
    | .fromGasKey pk _, _ =>
      -- `action_withdraw_from_gas_key` (`access_keys.rs:285-320`)
      orU (st.o.getAK recv pk) fun
        | some k => if k.perm.gasInfo.isSome then "InsufficientGasKeyBalance" else "GasKeyDoesNotExist"
        | none => "GasKeyDoesNotExist"
    | .deployGlobal _, _ => "LackBalanceForState"
    | .useGlobal _, _ => "GlobalContractDoesNotExist"
    | .stateInit d, some x =>
      -- `action_deterministic_state_init` (`deterministic_account_id.rs:30-90`): a fresh account
      -- first uses the global code (`GlobalContractDoesNotExist`), then pays storage
      if x.contract == .none then
        orU (st.o.contains (D3.L4.kGlobalContractCode d.stateInit.code) "global contract code") fun
          | false => "GlobalContractDoesNotExist"
          | true => "LackBalanceForState"
      else "LackBalanceForState"
    | .stateInit d, none =>
      orU (st.o.contains (D3.L4.kGlobalContractCode d.stateInit.code) "global contract code") fun
        | false => "GlobalContractDoesNotExist"
        | true => "LackBalanceForState"
    | _, _ => unclassified

/-! ## Transactions -/

/-- `validate_action_with_mode` (`action_validation.rs:127-470`) of one non-delegate action:
`none` = valid. -/
def baseValidKind (recv : Bytes) : Base → Option String
  | .deploy code | .deployGlobal ⟨code, _⟩ =>
    if code.length > Lim.maxContractSize then some "ContractSizeExceeded" else none
  | .useGlobal u => if !D3.L4.gciValid u.gci then some "InvalidAccountId" else none
  | .stateInit d =>
    if !D3.L4.gciValid d.stateInit.code then some "InvalidAccountId"
    else if D3.L4.deriveDetAccountId d.stateInit != recv then some "InvalidDeterministicStateInitReceiver"
    else d.stateInit.data.findSome? fun (k, v) =>
      if k.length > D3.L4.maxStorageKey then some "DeterministicStateInitKeyLengthExceeded"
      else if v.length > D3.L4.maxStorageValue then some "DeterministicStateInitValueLengthExceeded"
      else none
  | .fcall m a g _ =>
    if g == 0 then some "FunctionCallZeroAttachedGas"
    else if m.length > Lim.maxMethodName then some "FunctionCallMethodNameLengthExceeded"
    else if a.length > Lim.maxArgs then some "FunctionCallArgumentsLengthExceeded"
    else none
  | .stake _ pk => if !validStakingKey pk then some "UnsuitableStakingKey" else none
  | .addKey _ ak =>
    -- `validate_add_key_action` / `validate_access_key_permission` (`action_validation.rs:300-380`)
    let permKind : Option String := match ak.perm.fcPerm with
      | none => none
      | some fc =>
        if !AccountId.valid fc.receiver then some "InvalidAccountId"
        else if fc.methods.any (fun m => m.length > Lim.maxMethodName) then
          some "AddKeyMethodNameLengthExceeded"
        else if methodBytes fc.methods > Lim.maxMethodNamesBytes then
          some "AddKeyMethodNamesNumberOfBytesExceeded"
        else none
    match permKind with
    | some k => some k
    | none => match ak.perm.gasInfo with
      | none => none
      | some (bal, n) =>
        if (match ak.perm.fcPerm with | some fc => fc.allowance.isSome | none => false) then
          some "GasKeyFunctionCallAllowanceNotAllowed"
        else if n == 0 || n > Lim.maxNoncesForGasKey then some "GasKeyInvalidNumNonces"
        else if bal != 0 then some "AddGasKeyWithNonZeroBalance"
        else none
  | .deleteAccount b => if !AccountId.valid b then some "InvalidAccountId" else none
  | _ => none

/-- `validate_actions_with_mode` (`action_validation.rs:62-122`) over a non-delegate list (the
inner actions of a delegate, with its receiver). -/
def baseListValidKind (newMode : Bool) (recv : Bytes) (bs : List Base) : Option String :=
  if bs.length > Lim.maxActions then some "TotalNumberOfActionsExceeded"
  else if newMode && (bs.filter isDeploy).length > Lim.maxDeployActions then
    some "TotalNumberOfDeployActionsExceeded"
  else
    let rec loop : List Base → Option String
      | [] => none
      | b :: rest =>
        if isDeleteAccount b && !rest.isEmpty then some "DeleteActionMustBeFinal"
        else match baseValidKind recv b with
          | some k => some k
          | none => loop rest
    match loop bs with
    | some k => some k
    | none => match sumNat64 (bs.map Base.prepaidGas) with
      | none => some "IntegerOverflow"
      | some g => if g > Lim.maxTotalPrepaidGas then some "TotalPrepaidGasExceeded" else none

/-- `validate_actions_with_mode` over a transaction's actions (`NewReceipt` mode). -/
def actsValidKind (recv : Bytes) (acts : List Act) : Option String :=
  if acts.length > Lim.maxActions then some "TotalNumberOfActionsExceeded"
  else if (acts.filter fun a => match a with | .base b => isDeploy b.b | _ => false).length
      > Lim.maxDeployActions then some "TotalNumberOfDeployActionsExceeded"
  else
    let rec loop (seenDelegate : Bool) : List Act → Option String
      | [] => none
      | a :: rest =>
        match a with
        | .base b =>
          if isDeleteAccount b.b && !rest.isEmpty then some "DeleteActionMustBeFinal"
          else match baseValidKind recv b.b with
            | some k => some k
            | none => loop seenDelegate rest
        | .delegate _ d =>
          if seenDelegate then some "DelegateActionMustBeOnlyOne"
          -- `validate_delegate_action`: inner receiver from PV86 on (FixDelegatedDeterministicStateInit)
          else match baseListValidKind true d.receiver (d.actions.map (·.b)) with
            | some k => some k
            | none => loop true rest
    match loop false acts with
    | some k => some k
    | none => match totalPrepaidGas acts with
      | none => some "IntegerOverflow"
      | some g => if g > Lim.maxTotalPrepaidGas then some "TotalPrepaidGasExceeded" else none

/-- `validate_transaction` (`verifier.rs:109-117`): actions, then `check_valid_for_config` (size,
`transaction.rs:302-340`), then the signature (`transaction.rs:281-298`). -/
def txValidKind (t : TxD2) : String :=
  match actsValidKind t.receiver t.actions with
  | some k => "ActionsValidation." ++ k
  | none => if !t.sizeOk then "TransactionSizeExceeded" else "InvalidSignature"

/-- `verify_function_call_permission` (`verifier.rs:162-210`). -/
def fcPermKind (fc : FcPerm) (t : TxD2) : String :=
  match t.actions with
  | [.base ⟨_, .fcall m _ _ dep⟩] =>
    if dep > 0 then "InvalidAccessKeyError.DepositWithFunctionCall"
    else if t.receiver != fc.receiver then "InvalidAccessKeyError.ReceiverMismatch"
    else if !fc.methods.isEmpty && !fc.methods.contains m then "InvalidAccessKeyError.MethodNameMismatch"
    else unclassified
  | _ => "InvalidAccessKeyError.RequiresFullAccess"

/-- `verify_nonce` (`verifier.rs:212-238`). -/
def nonceKind (strict : Bool) (txNonce cur height : Nat) : Option String :=
  if !(if strict then cur + 1 < two64 && txNonce == cur + 1 else txNonce > cur) then some "InvalidNonce"
  else if txNonce ≥ min (height * Lim.nonceMult) (two64 - 1) then some "NonceTooLarge"
  else none

/-- `verify_and_charge_tx_ephemeral` (`verifier.rs:272-378`) on a `.failed` `verifyRegular`. -/
def regularKind (a : Acct) (k : AK) (t : TxD2) (c : TxCostD2) (height : Nat) : String :=
  if k.perm.gasInfo.isSome then "InvalidNonceIndex"
  else match nonceKind t.strict t.nonce k.nonce height with
  | some x => x
  | none =>
    if a.amount < c.totalCost then "NotEnoughBalance"
    else
      let allowanceShort := match k.perm.fcPerm with
        | some fc => match fc.allowance with | some al => decide (al < c.totalCost) | none => false
        | none => false
      if allowanceShort then "InvalidAccessKeyError.NotEnoughAllowance"
      else match storageStakeOk a (a.amount - c.totalCost) with
        | some true => match k.perm with
          | .fc fc => fcPermKind fc t
          | _ => unclassified
        | _ => "LackBalanceForState"

/-- `verify_and_charge_gas_key_tx_ephemeral` (`verifier.rs:383-538`) on a `.failed` `verifyGasKey`. -/
def gasKeyKind (k : AK) (row idx : Nat) (t : TxD2) (c : TxCostD2) (height : Nat) : String :=
  match k.perm.gasInfo with
  | none => "InvalidAccessKeyError.AccessKeyNotFound"
  | some (bal, n) =>
    if idx ≥ n then "InvalidNonceIndex"
    else match nonceKind t.strict t.nonce row height with
    | some x => x
    | none =>
      if bal < c.gasCost || bal < c.burntAmount then "NotEnoughGasKeyBalance"
      else match k.perm.fcPerm with
        | some fc => fcPermKind fc t
        | none => unclassified

/-- The kind of a transaction outcome `processTxD2L` reported as failed, from the state before it
(`process_transactions`, `lib.rs:1882-2140`). -/
def txKind (gasPrice height : Nat) (o : Ovl) (t : TxD2) (flag : Bool) : String :=
  if !flag then "Expired"
  else if !t.valid then txValidKind t
  else match txCostD2 t.pk t.signer t.receiver t.actions gasPrice with
  | none => "CostOverflow"
  | some c =>
    orU (o.getAcct t.signer) fun
      | none => "InvalidSignerId"
      | some a => orU (o.getAK t.signer t.pk) fun
        | none => "InvalidAccessKeyError.AccessKeyNotFound"
        | some k => match t.nonceIdx with
          | none => regularKind a k t c height
          | some idx => orU (o.getU64 (kNonce t.signer t.pk idx) "gas key nonce") fun
            | none => "InvalidNonceIndex"
            | some row =>
              -- `DepositFailed` (`verifier.rs:505-535`): the deposit is not covered
              match verifyGasKey a k row idx t c height with
              | .depositFailed _ _ => "NotEnoughBalanceForDeposit"
              | _ => gasKeyKind k row idx t c height

end NearSpecV3.Successor.FailureKinds
