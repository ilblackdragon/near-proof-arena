import NearSpec.SHA256
import NearSpec.AccountId

/-!
# NEAR primitives used by the transfer slice (nearcore 2.13.4, PV 86)

Byte layouts (all borsh):
* `AccountV1` — `core/primitives-core/src/account.rs:54-63, 406-447`: bare struct
  `{amount u128, locked u128, code_hash [u8;32], storage_usage u64}` = 72 bytes;
  first u128 equal to `u128::MAX` is the V2 sentinel (excluded).
* `PublicKey` — `core/crypto/src/signature.rs:371-389`: tag `0` ED25519 (32 B),
  tag `1` SECP256K1 (64 B). (tag 2 ML-DSA-65 excluded from the slice domain.)
* `Receipt` — `core/primitives/src/receipt.rs:221-233` (`Receipt::V0` serialized
  untagged), `ReceiptEnum::Action = 0`, `ActionReceipt` fields in order,
  `Action::Transfer = 3` (`core/primitives/src/action/mod.rs:349-370`).
-/

namespace NearSpec

/-! ## Pinned constants (PV 86, mainnet `RuntimeConfigStore::new(None)`) -/
namespace Params
/-- `new_action_receipt` exec gas, `parameters.yaml:43-47`. -/
def newActionReceiptExec : Nat := 108059500000
/-- `transfer` exec gas for a NamedAccount receiver, `parameters.yaml:88-92`,
`core/parameters/src/cost.rs:722-748`. -/
def transferExec : Nat := 115123062500
/-- Gas burnt (= compute) per Transfer receipt. -/
def G : Nat := newActionReceiptExec + transferExec
/-- `storage_amount_per_byte`, `parameters.yaml:35`. -/
def storageAmountPerByte : Nat := 10000000000000000000
/-- `ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT`, `runtime/runtime/src/verifier.rs:25`. -/
def zeroBalanceStorageLimit : Nat := 770
def protocolVersion : Nat := 86
/-- `"mainnet"` -/
def chainId : Bytes := [109, 97, 105, 110, 110, 101, 116]
def maxBatch : Nat := 256
/-- Slice-witness size bound (bytes) keeping the chunk well below
`main_storage_proof_size_soft_limit = 4_000_000` (PV 72+). -/
def maxWitnessBytes : Nat := 3000000
def u128Max : Nat := 340282366920938463463374607431768211455
def two64 : Nat := 18446744073709551616
def two128 : Nat := 340282366920938463463374607431768211456
end Params

/-! ## Account (V1 only) -/

structure Account where
  amount : Nat
  locked : Nat
  codeHash : Bytes
  storageUsage : Nat
  deriving DecidableEq, Repr

def Account.encode (a : Account) : Bytes :=
  u128 a.amount ++ u128 a.locked ++ a.codeHash ++ u64 a.storageUsage

/-- nearcore `Account::deserialize` restricted to V1: exactly 72 bytes and the
first u128 is not the V2 sentinel `u128::MAX`. -/
def Account.decode (b : Bytes) : Option Account :=
  if b.length = 72 then
    let amount := leNat (b.take 16)
    if amount = Params.u128Max then none
    else some ⟨amount, leNat ((b.drop 16).take 16), (b.drop 32).take 32, leNat (b.drop 64)⟩
  else none

/-! ## Public keys -/

structure PublicKey where
  tag : Nat
  data : Bytes
  deriving DecidableEq, Repr

def PublicKey.encode (k : PublicKey) : Bytes := u8 k.tag ++ k.data

def PublicKey.wf (k : PublicKey) : Bool :=
  (k.tag == 0 && k.data.length == 32) || (k.tag == 1 && k.data.length == 64)

/-! ## Single-Transfer action receipts

The Lean type only represents receipts of the slice shape:
`Receipt::V0 { receipt: ReceiptEnum::Action(ActionReceipt { output_data_receivers: [],
input_data_ids: [], actions: [Transfer { deposit }] }) }`. -/

structure Receipt where
  predecessorId : Bytes
  receiverId : Bytes
  receiptId : Bytes
  signerId : Bytes
  signerPk : PublicKey
  gasPrice : Nat
  deposit : Nat
  deriving DecidableEq, Repr

/-- Exact nearcore borsh of the receipt. -/
def Receipt.encode (r : Receipt) : Bytes :=
  borshBytes r.predecessorId ++ borshBytes r.receiverId ++ r.receiptId ++
  [0] ++                                   -- ReceiptEnum::Action
  borshBytes r.signerId ++ r.signerPk.encode ++ u128 r.gasPrice ++
  u32 0 ++                                 -- output_data_receivers = []
  u32 0 ++                                 -- input_data_ids = []
  u32 1 ++ [3] ++ u128 r.deposit           -- actions = [Transfer { deposit }]

/-- Field-width / validity conditions every in-domain receipt satisfies
(nearcore cannot even decode receipts violating the first four). -/
def Receipt.wf (r : Receipt) : Bool :=
  AccountId.valid r.predecessorId && AccountId.valid r.receiverId &&
  AccountId.valid r.signerId && r.signerPk.wf &&
  r.receiptId.length == 32 && r.gasPrice < Params.two128 && r.deposit < Params.two128

/-- Slice shape restrictions beyond well-formedness:
predecessor is not `system` (refund receipts take a different path,
`runtime/runtime/src/lib.rs:924-932`), receiver is a NamedAccount
(transfer exec fee differs for implicit/deterministic receivers,
`core/parameters/src/cost.rs:722-748`). -/
def Receipt.inSlice (r : Receipt) : Bool :=
  r.wf && r.predecessorId != AccountId.system && AccountId.isNamed r.receiverId

/-- `create_receipt_id_from_receipt_id(parent, height, idx)`
= `sha256(parent ‖ height_le64 ‖ idx_le64)` (`core/primitives/src/utils.rs:278-335`). -/
def receiptIdFrom (parent : Bytes) (height idx : Nat) : Bytes :=
  sha256 (parent ++ u64 height ++ u64 idx)

/-- `Receipt::new_gas_refund(signer_id, refund, signer_public_key)`
(`core/primitives/src/receipt.rs:519-537`) with its id set to
`create_receipt_id(parent, 0)` (`runtime/runtime/src/lib.rs:1059-1062`). -/
def gasRefundReceipt (parent : Receipt) (height refund : Nat) : Receipt :=
  { predecessorId := AccountId.system
    receiverId := parent.signerId
    receiptId := receiptIdFrom parent.receiptId height 0
    signerId := parent.signerId
    signerPk := parent.signerPk
    gasPrice := 0
    deposit := refund }

/-- borsh `Vec<Receipt>` -/
def encodeReceipts (rs : List Receipt) : Bytes :=
  u32 rs.length ++ concatAll (rs.map Receipt.encode)

/-- `sha256(borsh((ShardId, Vec<Receipt>)))` — same shape as nearcore's per-shard
outgoing-receipts bucket hash (`chain/chain/src/chain.rs:4102-4130`). -/
def receiptsCommitment (shardId : Nat) (rs : List Receipt) : Bytes :=
  sha256 (u64 shardId ++ encodeReceipts rs)

/-- `sha256(borsh(Vec<Receipt>))` of the generated gas-refund receipts. -/
def refundsCommitment (rs : List Receipt) : Bytes := sha256 (encodeReceipts rs)

end NearSpec
