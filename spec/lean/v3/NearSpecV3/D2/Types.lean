import NearSpecV3.TxD1

/-!
# D2 state and message types: decoders and encoders

nearcore 2.13.4 (`44f7ae6c…`, PV 86) borsh layouts used by domain D2
(spec/near-chunk-validation-d2.md §2):

* `Account` V1 / V2 (`core/primitives-core/src/account.rs:40-456`);
* `AccessKey` with all four permissions (`account.rs:466-620`);
* every action of the `Action` enum except the global-contract / state-init ones (tags 9,
  10, 11: `out of domain (w.shape)`), Delegate / DelegateV2 with their signed payloads
  (`core/primitives/src/action/mod.rs:349-370`, `action/delegate.rs`);
* `Receipt` (`ReceiptV0`, untagged) with `ReceiptEnum` tags 0, 1, 2, 3, 5, 6 (tag 4
  `GlobalContractDistribution`: `out of domain (w.shape)`) (`receipt.rs:57-80, 565-660`);
* `ReceiptOrStateStoredReceipt` (`receipt.rs:150-330`).

ML-DSA-65 public keys anywhere in an action or a receipt are `out of domain (w.shape)`: their
trie handle is a SHA3-256 hash, which is not formalized. Every decoder is strict (truncation,
unknown tags, invalid account ids, non-UTF-8 strings fail like nearcore's
`BorshDeserialize`). Encoders are the exact nearcore borsh; actions are kept with their raw
bytes (`raw`) so that re-encoding a receipt never needs an action encoder.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-! ## Public keys -/

/-- `PublicKey` excluding ML-DSA (tag 2): `out of domain (w.shape)`. -/
def pPk (w : String) : P PublicKey := fun bs => do
  let (pk, bs) ← pPublicKey w bs
  if pk.tag == 2 then throw s!"out of domain (w.shape): ML-DSA-65 public key ({w})"
  pure (pk, bs)

/-- `PublicKeyHandle` borsh = trie id of the key (`trie_key.rs:324-335`) for ED25519 /
SECP256K1: the `PublicKey` borsh itself. -/
def _root_.NearSpec.PublicKey.handle (k : PublicKey) : Bytes := k.encode

/-- `trie_id_len` (33 / 65). -/
def _root_.NearSpec.PublicKey.trieIdLen (k : PublicKey) : Nat := 1 + k.data.length

/-! ## Account -/

inductive Contract where
  | none
  | local (h : Bytes)
  | global (h : Bytes)
  | byAccount (id : Bytes)
  deriving DecidableEq, Repr

structure Acct where
  amount : Nat
  locked : Nat
  usage : Nat
  contract : Contract
  v2 : Bool
  deriving DecidableEq, Repr

def zero32 : Bytes := zeros 32

/-- `Account::new` (`account.rs:166-184`): V1 for `None`/`Local`, V2 otherwise. -/
def Acct.new (amount locked : Nat) (c : Contract) (usage : Nat) : Acct :=
  match c with
  | .none | .local _ => ⟨amount, locked, usage, c, false⟩
  | _ => ⟨amount, locked, usage, c, true⟩

/-- `set_contract` (`account.rs:283-300`): V1 stays V1 for `None`/`Local`, else becomes V2. -/
def Acct.setContract (a : Acct) (c : Contract) : Acct :=
  match c with
  | .none | .local _ => { a with contract := c }
  | _ => { a with contract := c, v2 := true }

def Contract.encode : Contract → Bytes
  | .none => [0]
  | .local h => [1] ++ h
  | .global h => [2] ++ h
  | .byAccount id => [3] ++ borshBytes id

/-- `identifier_storage_usage` (`account.rs:124-130`). -/
def Contract.idUsage : Contract → Nat
  | .global _ => 32
  | .byAccount id => id.length
  | _ => 0

def Acct.encode (a : Acct) : Bytes :=
  if a.v2 then
    u128 Params.u128Max ++ [0] ++ u128 a.amount ++ u128 a.locked ++ u64 a.usage ++ a.contract.encode
  else
    let ch := match a.contract with
      | .local h => h
      | _ => zero32
    u128 a.amount ++ u128 a.locked ++ ch ++ u64 a.usage

def pContract : P Contract := fun bs => do
  let (t, bs) ← pU8 "AccountContract tag" bs
  match t with
  | 0 => pure (.none, bs)
  | 1 => do let (h, bs) ← pHash "local code hash" bs; pure (.local h, bs)
  | 2 => do let (h, bs) ← pHash "global code hash" bs; pure (.global h, bs)
  | 3 => do let (a, bs) ← pAccountId "global contract account" bs; pure (.byAccount a, bs)
  | _ => throw "decode: AccountContract tag"

/-- `Account::try_from_slice` (`account.rs:410-456`); `none` ⇔ `StorageInconsistentState`. -/
def decodeAcct (b : Bytes) : Option Acct :=
  let r : Except String (Acct × Bytes) := do
    let (a0, bs) ← pU128 "amount" b
    if a0 == Params.u128Max then
      let (t, bs) ← pU8 "BorshVersionedAccount tag" bs
      if t != 0 then throw "decode: account version"
      let (amount, bs) ← pU128 "amount" bs
      let (locked, bs) ← pU128 "locked" bs
      let (usage, bs) ← pU64 "storage_usage" bs
      let (c, bs) ← pContract bs
      pure (⟨amount, locked, usage, c, true⟩, bs)
    else
      let (locked, bs) ← pU128 "locked" bs
      let (ch, bs) ← pHash "code_hash" bs
      let (usage, bs) ← pU64 "storage_usage" bs
      pure (⟨a0, locked, usage, (if ch == zero32 then .none else .local ch), false⟩, bs)
  match r with
  | .ok (a, []) => some a
  | _ => none

/-! ## Access keys -/

structure FcPerm where
  allowance : Option Nat
  receiver : Bytes
  methods : List Bytes
  deriving DecidableEq, Repr

inductive Perm where
  | fc (p : FcPerm)
  | full
  | gasFc (balance numNonces : Nat) (p : FcPerm)
  | gasFull (balance numNonces : Nat)
  deriving DecidableEq, Repr

structure AK where
  nonce : Nat
  perm : Perm
  deriving DecidableEq, Repr

def FcPerm.encode (p : FcPerm) : Bytes :=
  (match p.allowance with | none => [0] | some a => [1] ++ u128 a) ++ borshBytes p.receiver ++
  u32 p.methods.length ++ concatAll (p.methods.map borshBytes)

def Perm.encode : Perm → Bytes
  | .fc p => [0] ++ p.encode
  | .full => [1]
  | .gasFc b n p => [2] ++ u128 b ++ u16 n ++ p.encode
  | .gasFull b n => [3] ++ u128 b ++ u16 n

def AK.encode (k : AK) : Bytes := u64 k.nonce ++ k.perm.encode

def Perm.gasInfo : Perm → Option (Nat × Nat)
  | .gasFc b n _ => some (b, n)
  | .gasFull b n => some (b, n)
  | _ => none

def Perm.fcPerm : Perm → Option FcPerm
  | .fc p => some p
  | .gasFc _ _ p => some p
  | _ => none

def Perm.setGasBalance : Perm → Nat → Perm
  | .gasFc _ n p, b => .gasFc b n p
  | .gasFull _ n, b => .gasFull b n
  | p, _ => p

def pFcPermFull : P FcPerm := fun bs => do
  let (al, bs) ← pOption "allowance" (pU128 "allowance") bs
  let (r, bs) ← pString "receiver_id" bs
  let (ms, bs) ← pVec "method_names" (pString "method_name") bs
  pure (⟨al, r, ms⟩, bs)

def pPerm : P Perm := fun bs => do
  let (t, bs) ← pU8 "permission" bs
  match t with
  | 0 => do let (p, bs) ← pFcPermFull bs; pure (.fc p, bs)
  | 1 => pure (.full, bs)
  | 2 => do
    let (b, bs) ← pU128 "gas key balance" bs
    let (n, bs) ← pU16 "num_nonces" bs
    let (p, bs) ← pFcPermFull bs
    pure (.gasFc b n p, bs)
  | 3 => do
    let (b, bs) ← pU128 "gas key balance" bs
    let (n, bs) ← pU16 "num_nonces" bs
    pure (.gasFull b n, bs)
  | _ => throw "decode: AccessKeyPermission tag"

def pAK : P AK := fun bs => do
  let (n, bs) ← pU64 "ak nonce" bs
  let (p, bs) ← pPerm bs
  pure (⟨n, p⟩, bs)

def decodeAK (b : Bytes) : Option AK :=
  match pAK b with
  | .ok (k, []) => some k
  | _ => none

/-! ## Actions -/

/-- Non-delegate actions (the `NonDelegateAction` universe minus tags 9–11). -/
inductive Base where
  | createAccount
  | deploy (code : Bytes)
  | fcall (method args : Bytes) (gas deposit : Nat)
  | transfer (deposit : Nat)
  | stake (amount : Nat) (pk : PublicKey)
  | addKey (pk : PublicKey) (ak : AK)
  | deleteKey (pk : PublicKey)
  | deleteAccount (beneficiary : Bytes)
  | toGasKey (pk : PublicKey) (deposit : Nat)
  | fromGasKey (pk : PublicKey) (amount : Nat)
  deriving DecidableEq, Repr

structure BaseAct where
  raw : Bytes
  b : Base
  deriving DecidableEq, Repr

/-- `DelegateAction` (V1) or `DelegateActionV2` (with `TransactionNonce`). `payload` is the
borsh of the signed message body: `DelegateAction` for V1, `VersionedDelegateActionPayload`
(`0 ‖ DelegateActionV2`) for V2 (`action/delegate.rs:46-200`). -/
structure Delegate where
  v2 : Bool
  sender : Bytes
  receiver : Bytes
  actions : List BaseAct
  nonce : Nat
  nonceIdx : Option Nat
  maxHeight : Nat
  pk : PublicKey
  payload : Bytes
  sigTag : Nat
  sig : Bytes
  deriving DecidableEq, Repr

inductive Act where
  | base (a : BaseAct)
  | delegate (raw : Bytes) (d : Delegate)
  deriving DecidableEq, Repr

def Act.raw : Act → Bytes
  | .base a => a.raw
  | .delegate r _ => r

/-- `Action::get_deposit_balance` (non-delegate). -/
def Base.deposit : Base → Nat
  | .fcall _ _ _ d => d
  | .transfer d => d
  | .toGasKey _ d => d
  | _ => 0

def Base.prepaidGas : Base → Nat
  | .fcall _ _ g _ => g
  | _ => 0

/-- borsh `String`: `Vec<u8>` that is valid UTF-8 (`pString` of TxD1). -/
def pBase (tag : Nat) : P Base := fun bs =>
  match tag with
  | 0 => pure (.createAccount, bs)
  | 1 => do let (c, bs) ← pBytes "code" bs; pure (.deploy c, bs)
  | 2 => do
    let (m, bs) ← pString "method_name" bs
    let (a, bs) ← pBytes "args" bs
    let (g, bs) ← pU64 "gas" bs
    let (d, bs) ← pU128 "deposit" bs
    pure (.fcall m a g d, bs)
  | 3 => do let (d, bs) ← pU128 "deposit" bs; pure (.transfer d, bs)
  | 4 => do
    let (s, bs) ← pU128 "stake" bs
    let (pk, bs) ← pPk "stake key" bs
    pure (.stake s pk, bs)
  | 5 => do
    let (pk, bs) ← pPk "add key" bs
    let (ak, bs) ← pAK bs
    pure (.addKey pk ak, bs)
  | 6 => do let (pk, bs) ← pPk "delete key" bs; pure (.deleteKey pk, bs)
  | 7 => do let (b, bs) ← pAccountId "beneficiary_id" bs; pure (.deleteAccount b, bs)
  | 9 => throw "out of domain (w.shape): DeployGlobalContract action"
  | 10 => throw "out of domain (w.shape): UseGlobalContract action"
  | 11 => throw "out of domain (w.shape): DeterministicStateInit action"
  | 12 => do
    let (pk, bs) ← pPk "gas key" bs
    let (d, bs) ← pU128 "deposit" bs
    pure (.toGasKey pk d, bs)
  | 13 => do
    let (pk, bs) ← pPk "gas key" bs
    let (a, bs) ← pU128 "amount" bs
    pure (.fromGasKey pk a, bs)
  | _ => throw "decode: Action tag"

/-- `NonDelegateAction` (`action/delegate.rs:431-441`): tags 8 and 14 fail to decode. -/
def pBaseAct : P BaseAct := fun bs => do
  let start := bs
  let (t, bs) ← pU8 "action tag" bs
  if t == 8 || t == 14 then throw "decode: DelegateAction mustn't contain a nested one"
  let (b, bs) ← pBase t bs
  pure (⟨consumed start bs, b⟩, bs)

/-- `Signature` borsh: returns (tag, 64/65/3309 data bytes); ED25519 high bits rejected. -/
def pSig (w : String) : P (Nat × Bytes) := fun bs => do
  let (t, bs) ← pU8 (w ++ " signature type") bs
  match t with
  | 0 => do
    let (d, bs) ← pTake 64 w bs
    if (d.getD 63 0).toNat / 32 != 0 then throw s!"decode: ed25519 signature high bits ({w})"
    pure ((0, d), bs)
  | 1 => do let (d, bs) ← pTake 65 w bs; pure ((1, d), bs)
  | 2 => do let (_, bs) ← pTake 3309 w bs; throw s!"out of domain (w.shape): ML-DSA-65 signature ({w})"
  | _ => throw s!"decode: unknown signature tag ({w})"

/-- `TransactionNonce` (`transaction.rs:61-68`). -/
def pTxNonce : P (Nat × Option Nat) := fun bs => do
  let (t, bs) ← pU8 "TransactionNonce tag" bs
  match t with
  | 0 => do let (n, bs) ← pU64 "nonce" bs; pure ((n, none), bs)
  | 1 => do
    let (n, bs) ← pU64 "nonce" bs
    let (i, bs) ← pU16 "nonce_index" bs
    pure ((n, some i), bs)
  | _ => throw "decode: TransactionNonce tag"

/-- `DelegateAction` / `DelegateActionV2` fields after the payload tag. -/
def pDelegateBody (v2 : Bool) : P (Bytes × Bytes × List BaseAct × (Nat × Option Nat) × Nat × PublicKey) :=
  fun bs => do
    let (s, bs) ← pAccountId "sender_id" bs
    let (r, bs) ← pAccountId "receiver_id" bs
    let (acts, bs) ← pVec "delegate actions" pBaseAct bs
    let (n, bs) ← if v2 then pTxNonce bs else (do let (n, bs) ← pU64 "nonce" bs; pure ((n, none), bs))
    let (mh, bs) ← pU64 "max_block_height" bs
    let (pk, bs) ← pPk "delegate public key" bs
    pure ((s, r, acts, n, mh, pk), bs)

def pAct : P Act := fun bs => do
  let start := bs
  let (t, bs) ← pU8 "action tag" bs
  if t == 8 || t == 14 then
    let pstart := bs
    let bs ← if t == 14 then (do
        let (pt, bs) ← pU8 "VersionedDelegateActionPayload tag" bs
        if pt != 0 then throw "decode: VersionedDelegateActionPayload tag"
        pure bs) else pure bs
    let ((s, r, acts, (n, ni), mh, pk), bs) ← pDelegateBody (t == 14) bs
    let payload := consumed pstart bs
    let ((st, sig), bs) ← pSig "delegate" bs
    pure (.delegate (consumed start bs)
      ⟨t == 14, s, r, acts, n, ni, mh, pk, payload, st, sig⟩, bs)
  else
    let (b, bs) ← pBase t bs
    pure (.base ⟨consumed start bs, b⟩, bs)

/-- The NEP-461 signed hash of a delegate action (`signable_message.rs:18-25, 216-228`):
`sha256(u32le(2³⁰ + nep) ‖ payload)`, nep 366 (V1) / 611 (V2). -/
def Delegate.signedHash (d : Delegate) : Bytes :=
  sha256 (u32 (1073741824 + (if d.v2 then 611 else 366)) ++ d.payload)

def Delegate.innerActs (d : Delegate) : List Act := d.actions.map Act.base

/-! ## Receipts -/

structure ActionR where
  v2 : Bool
  signer : Bytes
  refundTo : Option Bytes
  signerPk : PublicKey
  gasPrice : Nat
  outputs : List (Bytes × Bytes)       -- (data_id, receiver_id)
  inputs : List Bytes
  actions : List Act
  deriving DecidableEq, Repr

inductive RBody where
  | action (yield : Bool) (a : ActionR)
  | data (resume : Bool) (dataId : Bytes) (data : Option Bytes)
  deriving DecidableEq, Repr

structure Rcpt where
  pred : Bytes
  recv : Bytes
  rid : Bytes
  body : RBody
  deriving DecidableEq, Repr

def encOptBytes : Option Bytes → Bytes
  | none => [0]
  | some b => [1] ++ borshBytes b

def ActionR.encode (a : ActionR) : Bytes :=
  borshBytes a.signer ++ (if a.v2 then encOptBytes a.refundTo else []) ++ a.signerPk.encode ++
  u128 a.gasPrice ++ u32 a.outputs.length ++
  concatAll (a.outputs.map fun (d, r) => d ++ borshBytes r) ++
  u32 a.inputs.length ++ concatAll a.inputs ++
  u32 a.actions.length ++ concatAll (a.actions.map Act.raw)

def RBody.encode : RBody → Bytes
  | .action y a => [if a.v2 then (if y then 6 else 5) else (if y then 2 else 0)] ++ a.encode
  | .data r d x => [if r then 3 else 1] ++ d ++ encOptBytes x

def Rcpt.encode (r : Rcpt) : Bytes :=
  borshBytes r.pred ++ borshBytes r.recv ++ r.rid ++ r.body.encode

def encodeRcpts (rs : List Rcpt) : Bytes := u32 rs.length ++ concatAll (rs.map Rcpt.encode)

def pActionR (v2 : Bool) : P ActionR := fun bs => do
  let (s, bs) ← pAccountId "signer_id" bs
  let (rt, bs) ← if v2 then pOption "refund_to" (pAccountId "refund_to") bs else pure (none, bs)
  let (pk, bs) ← pPk "signer_public_key" bs
  let (gp, bs) ← pU128 "gas_price" bs
  let (outs, bs) ← pVec "output_data_receivers" (fun bs => do
      let (d, bs) ← pHash "data_id" bs
      let (r, bs) ← pAccountId "data receiver" bs
      pure ((d, r), bs)) bs
  let (ins, bs) ← pVec "input_data_ids" (pHash "input data id") bs
  let (acts, bs) ← pVec "actions" pAct bs
  pure (⟨v2, s, rt, pk, gp, outs, ins, acts⟩, bs)

def pRcpt : P Rcpt := fun bs => do
  let (pred, bs) ← pAccountId "predecessor_id" bs
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (rid, bs) ← pHash "receipt_id" bs
  let (tag, bs) ← pU8 "ReceiptEnum tag" bs
  match tag with
  | 0 => do let (a, bs) ← pActionR false bs; pure (⟨pred, recv, rid, .action false a⟩, bs)
  | 2 => do let (a, bs) ← pActionR false bs; pure (⟨pred, recv, rid, .action true a⟩, bs)
  | 5 => do let (a, bs) ← pActionR true bs; pure (⟨pred, recv, rid, .action false a⟩, bs)
  | 6 => do let (a, bs) ← pActionR true bs; pure (⟨pred, recv, rid, .action true a⟩, bs)
  | 1 | 3 => do
    let (d, bs) ← pHash "data_id" bs
    let (x, bs) ← pOption "data" (pBytes "data") bs
    pure (⟨pred, recv, rid, .data (tag == 3) d x⟩, bs)
  | 4 => throw "out of domain (w.shape): GlobalContractDistribution receipt"
  | _ => throw "decode: ReceiptEnum tag"

/-- `Receipt::try_from_slice`; `none`-like errors are `StorageInconsistentState` when the bytes
come from the trie. -/
def decodeRcpt (b : Bytes) : Except String Rcpt := do
  let (r, rest) ← pRcpt b
  if !rest.isEmpty then throw "decode: trailing bytes in receipt"
  pure r

/-- `balance_refund_receiver` (`receipt.rs:417-432`). -/
def Rcpt.refundReceiver (r : Rcpt) : Bytes :=
  match r.body with
  | .action _ a => a.refundTo.getD r.pred
  | _ => r.pred

/-- `is_instant_receipt` (`receipt.rs:474-495`). -/
def Rcpt.isInstant (r : Rcpt) : Bool :=
  match r.body with
  | .action true _ => true
  | .action false a =>
    a.inputs.isEmpty && (match a.actions with
      | [.base ⟨_, .deleteAccount _⟩] => true
      | _ => false)
  | _ => false

def Rcpt.isAction (r : Rcpt) : Bool :=
  match r.body with
  | .action _ _ => true
  | _ => false

/-! ## `ReceiptOrStateStoredReceipt` (`receipt.rs:150-330`) -/

structure Stored where
  r : Rcpt
  /-- `some (gas, size, version)` for a `StateStoredReceipt`, `none` for a plain `Receipt`. -/
  md : Option (Nat × Nat × Nat)
  deriving Repr

def encodeStoredV1 (r : Rcpt) (gas size : Nat) : Bytes :=
  [255, 255, 1] ++ r.encode ++ u64 gas ++ u64 size

def decodeStored (b : Bytes) : Except String Stored := do
  match b with
  | 255 :: 255 :: v :: rest =>
    if v != 0 && v != 1 then throw "decode: StateStoredReceipt version"
    let (r, rest) ← pRcpt rest
    let (g, rest) ← pU64 "congestion_gas" rest
    let (s, rest) ← pU64 "congestion_size" rest
    if !rest.isEmpty then throw "decode: trailing bytes in StateStoredReceipt"
    pure ⟨r, some (g, s, v.toNat)⟩
  | _ => do
    let r ← decodeRcpt b
    pure ⟨r, none⟩

end NearSpecV3.D2
