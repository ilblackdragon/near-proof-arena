import NearSpecV3.D2.Receipts

/-!
# D2 transactions (spec/near-chunk-validation-d2.md §5)

`SignedTransaction` of any action list (`transaction.rs:233-268, 440-450`), V0 or V1, plain or
gas-key nonce (`TransactionNonce`), monotonic or strict `NonceMode`; ED25519 key and signature
only (other key / signature types: `out of domain (w.shape)`, as in D1).

`validate_transaction` (`verifier.rs:109-121`) = `validate_actions(NewReceipt)` ∧
`check_valid_for_config` (size) ∧ `Ed25519.verify`; `tx_cost` (`D2/Fees`); the two charging
paths `verify_and_charge_tx_ephemeral` (`verifier.rs:272-378`) and
`verify_and_charge_gas_key_tx_ephemeral` (`verifier.rs:383-538`, with `DepositFailed`).
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

structure TxD2 where
  raw : Bytes
  body : Bytes
  signer : Bytes
  pk : PublicKey
  nonce : Nat
  nonceIdx : Option Nat
  receiver : Bytes
  blockHash : Bytes
  actions : List Act
  strict : Bool
  sig : Bytes
  deriving Repr

def TxD2.hash (t : TxD2) : Bytes := sha256 t.body

def pTxD2 : P TxD2 := fun bs => do
  let start := bs
  let (u1, r1) ← pU8 "transaction version" bs
  let (u2, _) ← pU8 "transaction version" r1
  let (v1, bs) ←
    if u2 == 0 then pure (false, bs)
    else if u1 == 1 then pure (true, r1)
    else throw "decode: invalid transaction version tag"
  let (signer, bs) ← pAccountId "signer_id" bs
  let (pk, bs) ← pPublicKey "tx public_key" bs
  if pk.tag != 0 then throw "out of domain (w.shape): non-ED25519 transaction key"
  let ((nonce, ni), bs) ← if v1 then pTxNonce bs else (do let (n, bs) ← pU64 "nonce" bs; pure ((n, none), bs))
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (bh, bs) ← pHash "block_hash" bs
  let (acts, bs) ← pVec "actions" pAct bs
  let (strict, bs) ← if v1 then (do
      let (m, bs) ← pU8 "NonceMode" bs
      if m == 0 then pure (false, bs) else if m == 1 then pure (true, bs)
      else throw "decode: NonceMode tag")
    else pure (false, bs)
  let body := consumed start bs
  let (st, bs) ← pU8 "signature type" bs
  if st != 0 then
    if st == 1 || st == 2 then throw "out of domain (w.shape): non-ED25519 transaction signature"
    else throw "decode: unknown signature tag"
  let (sig, bs) ← pTake 64 "ed25519 signature" bs
  if (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨consumed start bs, body, signer, pk, nonce, ni, recv, bh, acts, strict, sig⟩, bs)

def TxD2.sizeOk (t : TxD2) : Bool := t.body.length + 65 ≤ TxParams.maxTransactionSize

/-- `validate_transaction`. -/
def TxD2.valid (t : TxD2) : Bool :=
  validActs true t.actions && t.sizeOk && Ed25519.verify t.pk.data t.sig t.hash

/-- `verify_nonce` (`verifier.rs:212-238`). -/
def nonceOk (strict : Bool) (txNonce cur height : Nat) : Bool :=
  (if strict then cur + 1 < two64 && txNonce == cur + 1 else txNonce > cur) &&
  txNonce < min (height * Lim.nonceMult) (two64 - 1)

/-- `verify_function_call_permission` (`verifier.rs:167-210`). -/
def fcPermissionOk (fc : FcPerm) (t : TxD2) : Bool :=
  match t.actions with
  | [.base ⟨_, .fcall m _ _ dep⟩] =>
    dep == 0 && t.receiver == fc.receiver && (fc.methods.isEmpty || fc.methods.contains m)
  | _ => false

inductive Verdict where
  /-- success: new account amount, new access key, gas-key nonce row update -/
  | success (amount : Nat) (k : AK) (row : Option (Nat × Nat))
  /-- gas key, deposit not covered: key charged `burnt_amount`, row advanced -/
  | depositFailed (k : AK) (row : Nat × Nat)
  | failed

/-- `verify_and_charge_tx_ephemeral` (plain nonce). -/
def verifyRegular (a : Acct) (k : AK) (t : TxD2) (c : TxCostD2) (height : Nat) : Verdict :=
  if k.perm.gasInfo.isSome then .failed
  else if !nonceOk t.strict t.nonce k.nonce height then .failed
  else if a.amount < c.totalCost then .failed
  else
    let newAmount := a.amount - c.totalCost
    let allowance : Option (Option Nat) := match k.perm.fcPerm with
      | some fc => match fc.allowance with
        | some al => if al < c.totalCost then none else some (some (al - c.totalCost))
        | none => some none
      | none => some none
    match allowance with
    | none => .failed
    | some newAl =>
      match storageStakeOk a newAmount with
      | some true =>
        match k.perm with
        | .fc fc =>
          if !fcPermissionOk fc t then .failed
          else .success newAmount ⟨t.nonce, .fc (match newAl with | some x => { fc with allowance := some x } | none => fc)⟩ none
        | .full => .success newAmount ⟨t.nonce, .full⟩ none
        | _ => .failed
      | _ => .failed

/-- `verify_and_charge_gas_key_tx_ephemeral` given the nonce row value. -/
def verifyGasKey (a : Acct) (k : AK) (row : Nat) (idx : Nat) (t : TxD2) (c : TxCostD2) (height : Nat) : Verdict :=
  match k.perm.gasInfo with
  | none => .failed
  | some (bal, n) =>
    if idx ≥ n then .failed
    else if !nonceOk t.strict t.nonce row height then .failed
    else if bal < c.gasCost then .failed
    else if bal < c.burntAmount then .failed
    else if (match k.perm.fcPerm with | some fc => !fcPermissionOk fc t | none => false) then .failed
    else
      let failedK : AK := { k with perm := k.perm.setGasBalance (bal - c.burntAmount) }
      if a.amount < c.depositCost then .depositFailed failedK (idx, t.nonce)
      else
        let na := a.amount - c.depositCost
        match storageStakeOk a na with
        | some true => .success na { k with perm := k.perm.setGasBalance (bal - c.gasCost) } (some (idx, t.nonce))
        | some false => .depositFailed failedK (idx, t.nonce)
        | none => .failed

end NearSpecV3.D2
