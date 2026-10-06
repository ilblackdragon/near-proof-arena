import NearSpecV3.Wire
import NearSpecV3.Ed25519

/-!
# Transfer transactions (domain D1): decoding, costs, access keys, verification

Transcription of the parts of nearcore 2.13.4 (`44f7ae6c…`, PV 86) that a chunk validator
runs on the transactions of the last new chunk (spec/near-chunk-validation-d1.md §3):

* borsh `SignedTransaction = Transaction ‖ Signature` (`core/primitives/src/transaction.rs:440-450`),
  `Transaction` with the two-byte look-ahead (`transaction.rs:233-268`): second byte 0 ⇒ `V0`
  (untagged), else first byte 1 ⇒ `V1`, else error; `TransactionV1` adds `TransactionNonce`
  (`Nonce{u64}` = 0 | `GasKeyNonce{u64, u16}` = 1, `transaction.rs:61-68`) and a trailing
  `NonceMode` (0 Monotonic | 1 Strict, `transaction.rs:99-112`);
* the D1 shape (`w.tx_shape`): V0 or V1 with a plain nonce; exactly one action, `Transfer`
  (`Action` tag 3, `u128 deposit`); ED25519 public key (tag 0) and ED25519 signature (tag 0,
  64 bytes, `sig[63] & 0xE0 = 0` else a decode error, `signature.rs:1174-1183`). Any other
  well-formed shape is `out of domain`;
* the transaction hash `sha256(borsh(Transaction))` (`transaction.rs:139-145`, `init` 465-469),
  which is both the signed message and the outcome id;
* `validate_transaction` (`runtime/runtime/src/verifier.rs:109-121`) for a single Transfer:
  `validate_actions` always passes (`action_validation.rs:62-125, 142`); `check_valid_for_config`
  (`transaction.rs:315-354`): version gates are open at PV 86 (GasKeys, StrictNonce,
  PostQuantumSignatures = 85, `core/primitives-core/src/version.rs:559-575`), size
  `wire_size = |borsh(Transaction)| + |borsh(Signature)| ≤ max_transaction_size = 1 572 864`;
  then `Signature::verify(tx_hash, public_key)` (`transaction.rs:302-308`,
  `core/crypto/src/signature.rs:1086-1093`) = `Ed25519.verify`;
* `tx_cost` (`runtime/runtime/src/config.rs:400-479`) for one Transfer;
* `AccessKey` decoding (`core/primitives-core/src/account.rs:453-620`) and
  `verify_and_charge_tx_ephemeral` (`verifier.rs:272-378`).

PV 86 fee constants (gas = compute for every one of them; `send_sir = send_not_sir`), as
printed by `near-arena-oracle-v3 params` from `RuntimeConfigStore::new(None).get_config(86)`:
new_action_receipt 108 059 500 000 (send and exec), transfer 115 123 062 500 (send and exec),
create_account send 500 000 000 000 / exec 7 200 000 000 000, add_full_access_key
101 765 125 000 (send and exec), ED25519 signature verification 0
(`core/parameters/src/parameter_table.rs:434-441`), `min_gas_purchase_price` 10⁹
(`runtime_configs/85.yaml:41`), `eth_implicit_accounts` = true.
-/

namespace NearSpecV3

open NearSpec

/-! ## Constants -/

namespace TxParams
def narSend : Nat := 108059500000
def narExec : Nat := 108059500000
def transferSend : Nat := 115123062500
def transferExec : Nat := 115123062500
def createAccountSend : Nat := 500000000000
def createAccountExec : Nat := 7200000000000
def addFullAccessKeySend : Nat := 101765125000
def addFullAccessKeyExec : Nat := 101765125000
def sigVerifEd25519 : Nat := 0
def minGasPurchasePrice : Nat := 1000000000
def maxTransactionSize : Nat := 1572864
def nonceRangeMultiplier : Nat := 1000000
end TxParams

/-! ## Decoded D1 transaction -/

structure Tx where
  raw : Bytes            -- borsh(SignedTransaction): merklize leaf preimage, RS body
  body : Bytes           -- borsh(Transaction): hash preimage
  signerId : Bytes
  pk : Bytes             -- 32-byte ED25519 key
  nonce : Nat
  receiverId : Bytes
  blockHash : Bytes
  deposit : Nat
  strict : Bool          -- V1 with NonceMode::Strict
  sig : Bytes            -- 64 bytes
  deriving Repr

def Tx.hash (t : Tx) : Bytes := sha256 t.body
def Tx.pkKey (t : Tx) : PublicKey := ⟨0, t.pk⟩

/-- `Transaction` V0/V1 field tail common to both (signer … actions) in the D1 shape. -/
def pTxFields (v1 : Bool) : P (Bytes × Bytes × Nat × Bytes × Bytes × Nat) := fun bs => do
  let (signer, bs) ← pAccountId "signer_id" bs
  let (pk, bs) ← pPublicKey "tx public_key" bs
  if pk.tag != 0 then throw "out of domain (w.tx_shape): non-ED25519 transaction key"
  let (nonce, bs) ← if v1 then (do
      let (nt, bs) ← pU8 "TransactionNonce tag" bs
      match nt with
      | 0 => pU64 "nonce" bs
      | 1 => throw "out of domain (w.tx_shape): gas-key nonce (TransactionNonce::GasKeyNonce)"
      | _ => throw "decode: TransactionNonce tag")
    else pU64 "nonce" bs
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (bh, bs) ← pHash "block_hash" bs
  let (na, bs) ← pU32 "actions" bs
  if na != 1 then throw "out of domain (w.tx_shape): not exactly one action"
  let (atag, bs) ← pU8 "action tag" bs
  if atag != 3 then throw "out of domain (w.tx_shape): action is not Transfer(3)"
  let (dep, bs) ← pU128 "deposit" bs
  pure ((signer, pk.data, nonce, recv, bh, dep), bs)

/-- borsh `SignedTransaction` in the D1 shape (decode errors are `decode: …`, other shapes
`out of domain (w.tx_shape)`). -/
def pTxD1 : P Tx := fun bs => do
  let start := bs
  let (u1, r1) ← pU8 "transaction version" bs
  let (u2, _) ← pU8 "transaction version" r1
  let (v1, bodyStart) ←
    if u2 == 0 then pure (false, bs)
    else if u1 == 1 then pure (true, r1)
    else throw "decode: invalid transaction version tag"
  let ((signer, pk, nonce, recv, bh, dep), bs) ← pTxFields v1 bodyStart
  let (strict, bs) ← if v1 then (do
      let (m, bs) ← pU8 "NonceMode" bs
      if m == 0 then pure (false, bs) else if m == 1 then pure (true, bs)
      else throw "decode: NonceMode tag")
    else pure (false, bs)
  let body := consumed start bs
  let (st, bs) ← pU8 "signature type" bs
  if st != 0 then
    if st == 1 || st == 2 then throw "out of domain (w.tx_shape): non-ED25519 signature"
    else throw "decode: unknown signature tag"
  let (sig, bs) ← pTake 64 "ed25519 signature" bs
  if (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨consumed start bs, body, signer, pk, nonce, recv, bh, dep, strict, sig⟩, bs)

/-! ## `validate_transaction` -/

/-- `check_valid_for_config` (size gate; the version gates are open at PV 86). -/
def Tx.sizeOk (t : Tx) : Bool := t.body.length + 65 ≤ TxParams.maxTransactionSize

/-- `ValidatedTransaction::new`: config checks, then the signature. -/
def Tx.valid (t : Tx) : Bool := t.sizeOk && Ed25519.verify t.pk t.sig t.hash

/-! ## `tx_cost` for one Transfer (`config.rs:417-479`, `cost.rs:722-777`) -/

/-- Transfer send fee by receiver account type (`transfer_send_fee`, eth-implicit enabled). -/
def transferSendFee (recv : Bytes) : Nat :=
  if AccountId.isNearImplicit recv then
    TxParams.transferSend + TxParams.createAccountSend + TxParams.addFullAccessKeySend
  else if AccountId.isEthImplicit recv || AccountId.isNearDeterministic recv then
    TxParams.transferSend + TxParams.createAccountSend
  else TxParams.transferSend

def transferExecFee (recv : Bytes) : Nat :=
  if AccountId.isNearImplicit recv then
    TxParams.transferExec + TxParams.createAccountExec + TxParams.addFullAccessKeyExec
  else if AccountId.isEthImplicit recv || AccountId.isNearDeterministic recv then
    TxParams.transferExec + TxParams.createAccountExec
  else TxParams.transferExec

structure TxCost where
  gasBurnt : Nat         -- = compute_burnt (gas = compute for every fee at PV 86)
  receiptGasPrice : Nat
  burntAmount : Nat
  totalCost : Nat

/-- `None` ⇔ `IntegerOverflowError` (u64 gas sums, u128 balances: `CostOverflow`). -/
def txCost (t : Tx) (gasPrice : Nat) : Option TxCost :=
  let burnt := TxParams.narSend + transferSendFee t.receiverId + TxParams.sigVerifEd25519
  let remaining := TxParams.narExec + transferExecFee t.receiverId
  let burntAmount := gasPrice * burnt
  let rgp := max gasPrice TxParams.minGasPurchasePrice
  let remAmount := rgp * remaining
  let gasCost := burntAmount + remAmount
  let total := gasCost + t.deposit
  if burnt ≥ Params.two64 || remaining ≥ Params.two64 then none
  else if burntAmount ≥ Params.two128 || remAmount ≥ Params.two128 || gasCost ≥ Params.two128
    || total ≥ Params.two128 then none
  else some ⟨burnt, rgp, burntAmount, total⟩

/-! ## Access keys (`account.rs:453-620`) -/

inductive Perm where
  | fullAccess
  | functionCall (allowance : Option Nat)
  | gasKey
  deriving Repr, DecidableEq

structure AccessKeyV where
  nonce : Nat
  perm : Perm
  deriving Repr

/-- `String::from_utf8` (borsh `String`): well-formed UTF-8 (no overlong forms, no surrogates,
≤ U+10FFFF). -/
def utf8Ok : List UInt8 → Bool
  | [] => true
  | a :: rest =>
    let x := a.toNat
    let cont (b : UInt8) := 0x80 ≤ b.toNat && b.toNat ≤ 0xBF
    if x < 0x80 then utf8Ok rest
    else if 0xC2 ≤ x && x ≤ 0xDF then
      match rest with
      | b :: r => cont b && utf8Ok r
      | _ => false
    else if 0xE0 ≤ x && x ≤ 0xEF then
      match rest with
      | b :: c :: r =>
        let lo := if x == 0xE0 then 0xA0 else 0x80
        let hi := if x == 0xED then 0x9F else 0xBF
        lo ≤ b.toNat && b.toNat ≤ hi && cont c && utf8Ok r
      | _ => false
    else if 0xF0 ≤ x && x ≤ 0xF4 then
      match rest with
      | b :: c :: d :: r =>
        let lo := if x == 0xF0 then 0x90 else 0x80
        let hi := if x == 0xF4 then 0x8F else 0xBF
        lo ≤ b.toNat && b.toNat ≤ hi && cont c && cont d && utf8Ok r
      | _ => false
    else false

def pString (w : String) : P Bytes := fun bs => do
  let (s, bs) ← pBytes w bs
  if utf8Ok s then pure (s, bs) else throw s!"decode: invalid UTF-8 ({w})"

/-- `FunctionCallPermission { allowance: Option<u128>, receiver_id: String, method_names: Vec<String> }`. -/
def pFcPerm : P (Option Nat) := fun bs => do
  let (al, bs) ← pOption "allowance" (pU128 "allowance") bs
  let (_, bs) ← pString "receiver_id" bs
  let (_, bs) ← pVec "method_names" (pString "method_name") bs
  pure (al, bs)

/-- `GasKeyInfo { balance: u128, num_nonces: u16 }`. -/
def pGasKeyInfo : P Unit := fun bs => do
  let (_, bs) ← pU128 "gas key balance" bs
  let (_, bs) ← pU16 "num_nonces" bs
  pure ((), bs)

/-- `AccessKey::try_from_slice` (trailing bytes rejected). `none` ⇔ nearcore's
`StorageInconsistentState` (`core/store/src/utils/mod.rs:26-38`). -/
def decodeAccessKey (b : Bytes) : Option AccessKeyV :=
  let r : Except String (AccessKeyV × Bytes) := do
    let (n, bs) ← pU64 "ak nonce" b
    let (t, bs) ← pU8 "permission" bs
    match t with
    | 0 => do let (al, bs) ← pFcPerm bs; pure (⟨n, .functionCall al⟩, bs)
    | 1 => pure (⟨n, .fullAccess⟩, bs)
    | 2 => do let (_, bs) ← pGasKeyInfo bs; let (_, bs) ← pFcPerm bs; pure (⟨n, .gasKey⟩, bs)
    | 3 => do let (_, bs) ← pGasKeyInfo bs; pure (⟨n, .gasKey⟩, bs)
    | _ => throw "decode: AccessKeyPermission tag"
  match r with
  | .ok (k, []) => some k
  | _ => none

/-- `AccessKey { nonce, FullAccess }` encoding (9 bytes). -/
def encodeFullAccessKey (nonce : Nat) : Bytes := u64 nonce ++ [1]

/-! ## `verify_and_charge_tx_ephemeral` (`verifier.rs:272-378`) for a Transfer

Returns the new account amount on success (`TxVerdict::Success`), `none` on any
`TxVerdict::Failed`. All failure reasons are equivalent for the chunk: the failed outcome
(`Failure`, no receipts, gas 0) hashes without the error (`PartialExecutionStatus::Failure`,
`transaction.rs:597-612`) and nothing is written (`FixAccessKeyAllowanceCharging`, PV 83). -/
def verifyAndCharge (a : Account) (k : AccessKeyV) (t : Tx) (c : TxCost) (height : Nat) :
    Option Nat :=
  match k.perm with
  | .gasKey => none                                         -- InvalidNonceIndex (:283-291)
  | perm =>
    -- verify_nonce (:212-238): monotonic `>`, strict `= ak + 1` (checked); `< height·10⁶`
    let nonceOk :=
      (if t.strict then k.nonce + 1 < Params.two64 && t.nonce == k.nonce + 1
       else t.nonce > k.nonce) &&
      t.nonce < min (height * TxParams.nonceRangeMultiplier) (Params.two64 - 1)
    if !nonceOk then none
    else if a.amount < c.totalCost then none                -- NotEnoughBalance
    else
      let newAmount := a.amount - c.totalCost
      -- allowance (:327-345): a function-call key with an allowance below the cost fails
      let allowanceOk := match perm with
        | .functionCall (some al) => c.totalCost ≤ al
        | _ => true
      if !allowanceOk then none
      else
        -- check_storage_stake (:48-86) with the new amount
        let required := Params.storageAmountPerByte * a.storageUsage
        if required ≥ Params.two128 || newAmount + a.locked ≥ Params.two128 then none
        else if !(newAmount + a.locked ≥ required || a.storageUsage ≤ Params.zeroBalanceStorageLimit)
        then none                                           -- LackBalanceForState
        else match perm with
          | .functionCall _ => none                         -- RequiresFullAccess (:357-363)
          | _ => some newAmount

end NearSpecV3
