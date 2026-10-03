import NearSpec.Primitives

/-!
# Execution outcomes and the outcome root

* `ExecutionOutcomeWithId::to_hashes()` = `[id, hash(borsh(PartialExecutionOutcome)), hash(log_i)…]`
  (`core/primitives/src/transaction.rs:746-752`).
* `PartialExecutionOutcome = {receipt_ids: Vec<CryptoHash>, gas_burnt: u64,
  tokens_burnt: u128, executor_id: AccountId, status: PartialExecutionStatus}`
  (`transaction.rs:573-602`); `compute_usage` and `metadata` are NOT hashed.
  A successful Transfer has status `SuccessValue(vec![])` = `0x02 ‖ u32 0` and no logs.
* `outcome_root = merklize([o.to_hashes() for o in outcomes]).0`
  (`chain/chain/src/types.rs:151-163`, `core/primitives/src/merkle.rs:42-110`):
  leaf = `hash(borsh(Vec<CryptoHash>))`, inner = `sha256(left ‖ right)`, an odd last
  node is promoted unchanged, one leaf ⇒ root = leaf, empty ⇒ 32 zero bytes.
-/

namespace NearSpec

structure Outcome where
  id : Bytes
  receiptIds : List Bytes
  gasBurnt : Nat
  tokensBurnt : Nat
  executorId : Bytes
  deriving DecidableEq, Repr

def Outcome.partialEncode (o : Outcome) : Bytes :=
  u32 o.receiptIds.length ++ concatAll o.receiptIds ++ u64 o.gasBurnt ++ u128 o.tokensBurnt ++
  borshBytes o.executorId ++ [2] ++ u32 0

/-- `CryptoHash::hash_borsh(o.to_hashes())` — the merklize leaf for this outcome. -/
def Outcome.leaf (o : Outcome) : Bytes :=
  sha256 (u32 2 ++ o.id ++ sha256 o.partialEncode)

def merkleLevel : List Bytes → List Bytes
  | a :: b :: rest => sha256 (a ++ b) :: merkleLevel rest
  | l => l

def merkleFold : Nat → List Bytes → Bytes
  | _, [] => zeroHash
  | _, [x] => x
  | 0, x :: _ => x
  | n + 1, l => merkleFold n (merkleLevel l)

/-- nearcore `merklize` root over already-hashed leaves. -/
def merkleRoot (leaves : List Bytes) : Bytes := merkleFold leaves.length leaves

def outcomeRoot (os : List Outcome) : Bytes := merkleRoot (os.map Outcome.leaf)

end NearSpec
