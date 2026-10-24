import NearSpecV3.TxD1
import NearSpecV3.Wasm.Crypto

/-! Shared typed PV86 global actions. Signed D2 decoders still reject these variants. -/
namespace NearSpecV3.D3.L4
open NearSpec NearSpecV3

/-! ## 1. `GlobalContractIdentifier` (`core/primitives-core/src/global_contract.rs:16-44`) -/

/-- `GlobalContractIdentifier`: a borsh enum with `use_discriminant`, so a one-byte tag. `CodeHash`
carries a 32-byte hash, `AccountId` a borsh string (`global_contract.rs:16-35`). -/
inductive Gci where
  | codeHash (h : Bytes)
  | accountId (id : Bytes)
  deriving DecidableEq, Repr

/-- `GlobalContractIdentifier::len()` (`global_contract.rs:37-44`): 32 for a hash, the account id's
length otherwise. This is the *identifier* length used by the byte fee and by
`AccountContract::identifier_storage_usage`, **not** the borsh encoding length. -/
def Gci.len : Gci → Nat
  | .codeHash _ => 32
  | .accountId id => id.length

/-- borsh of `GlobalContractIdentifier`: tag `0`/`1` then the payload; the `AccountId` payload is a
borsh string (`u32` length prefix), matching `#[borsh(use_discriminant = true)]`. -/
def Gci.encode : Gci → Bytes
  | .codeHash h => [0] ++ h
  | .accountId id => [1] ++ borshBytes id

/-- `GlobalContractIdentifier` decoder. Strict: unknown tag, wrong hash length, invalid account id,
truncation all fail like nearcore's `BorshDeserialize`. -/
def pGci : P Gci := fun bs => do
  let (t, bs) ← pU8 "GlobalContractIdentifier tag" bs
  match t with
  | 0 => do let (h, bs) ← pHash "global contract code hash" bs; pure (.codeHash h, bs)
  | 1 => do let (id, bs) ← pAccountId "global contract account id" bs; pure (.accountId id, bs)
  | _ => throw "decode: GlobalContractIdentifier tag"

/-- The `CodeHash` encoding starts with the tag byte `0` and carries the 32-byte hash verbatim
(`global_contract.rs:16-24`). -/
theorem gci_encode_codeHash_eq (h : Bytes) :
    (Gci.codeHash h).encode = 0 :: h := rfl

/-- The `AccountId` encoding is tag `1` then a borsh string: a `u32` length prefix and the bytes
(`global_contract.rs:16-35`; the `AccountId` payload is `Vec<u8>`-shaped). -/
theorem gci_encode_accountId_eq (id : Bytes) :
    (Gci.accountId id).encode = 1 :: (u32 id.length ++ id) := rfl

/-! ## 2. Deploy mode (`core/primitives/src/action/mod.rs:133-146`) -/

/-- `GlobalContractDeployMode`: `CodeHash = 0`, `AccountId = 1`. -/
inductive GcdMode where
  | codeHash
  | accountId
  deriving DecidableEq, Repr

def pGcdMode : P GcdMode := fun bs => do
  let (t, bs) ← pU8 "GlobalContractDeployMode" bs
  match t with
  | 0 => pure (.codeHash, bs)
  | 1 => pure (.accountId, bs)
  | _ => throw "decode: GlobalContractDeployMode tag"

def GcdMode.encode : GcdMode → Bytes
  | .codeHash => [0]
  | .accountId => [1]

/-! ## 3. `DeterministicAccountStateInit` (`deterministic_account_id.rs:22-94`)

`data` is a `BTreeMap<Vec<u8>, Vec<u8>>`: borsh serializes it as `u32` count followed by
`(Vec<u8>, Vec<u8>)` pairs in **ascending key order** (`BTreeMap` iteration order), and duplicate
keys cannot be represented. The decoder below therefore rejects out-of-order keys and duplicates,
which is exactly the set of byte strings no `BTreeMap` round-trip produces. -/

/-- Keys strictly ascending (`BTreeMap` iteration order). -/
def ascKeys : List Bytes → Bool
  | [] => true
  | [_] => true
  | k1 :: k2 :: rest => decide (k1 < k2) && ascKeys (k2 :: rest)

/-- A `Vec<(Vec<u8>, Vec<u8>)>` in the canonical `BTreeMap` order: strictly ascending keys. -/
def sortedKeys (l : List (Bytes × Bytes)) : Bool := ascKeys (l.map Prod.fst)

/-- `DeterministicAccountStateInit::V1`: the code identifier and the `ContractData` pairs, in
`BTreeMap` order (`deterministic_account_id.rs:22-42`). -/
structure StateInit where
  code : Gci
  data : List (Bytes × Bytes)
  deriving DecidableEq, Repr

/-- `DeterministicAccountStateInitV1::len_bytes()` (`deterministic_account_id.rs:78-94`): the sum of
key and value lengths only — *not* the borsh overhead. -/
def StateInit.lenBytes (s : StateInit) : Nat :=
  s.data.foldl (fun acc (k, v) => acc + k.length + v.length) 0

/-- borsh of `DeterministicAccountStateInit::V1`: `0 ‖ identifier ‖ Vec<(Vec<u8>, Vec<u8>)>`. -/
def StateInit.encode (s : StateInit) : Bytes :=
  [0] ++ s.code.encode ++ u32 s.data.length ++
  s.data.foldl (fun acc (k, v) => acc ++ borshBytes k ++ borshBytes v) []

/-- `DeterministicAccountStateInit` decoder. Only the V1 tag exists at PV86; the key order check is
the `BTreeMap` invariant, so a non-canonical encoding is a decode error like nearcore's
`BorshDeserialize` (which would produce a map that re-serializes differently). -/
def pStateInit : P StateInit := fun bs => do
  let (t, bs) ← pU8 "DeterministicAccountStateInit tag" bs
  if t != 0 then throw "decode: DeterministicAccountStateInit tag"
  let (code, bs) ← pGci bs
  let (data, bs) ← pVec "state_init data" (fun bs => do
    let (k, bs) ← pBytes "state_init key" bs
    let (v, bs) ← pBytes "state_init value" bs
    pure ((k, v), bs)) bs
  if !sortedKeys data then throw "decode: state_init data not in BTreeMap order"
  pure (⟨code, data⟩, bs)

/-! ## 4. The three action bodies (`core/primitives/src/action/mod.rs:157-221`) -/

/-- `DeployGlobalContractAction` (tag 9): `code ‖ deploy_mode`. -/
structure DeployGlobal where
  code : Bytes
  mode : GcdMode
  deriving DecidableEq, Repr

def pDeployGlobal : P DeployGlobal := fun bs => do
  let (code, bs) ← pBytes "global contract code" bs
  let (m, bs) ← pGcdMode bs
  pure (⟨code, m⟩, bs)

def DeployGlobal.encode (d : DeployGlobal) : Bytes := borshBytes d.code ++ d.mode.encode

/-- `UseGlobalContractAction` (tag 10): `identifier`. -/
structure UseGlobal where
  gci : Gci
  deriving DecidableEq, Repr

def pUseGlobal : P UseGlobal := fun bs => do
  let (g, bs) ← pGci bs
  pure (⟨g⟩, bs)

def UseGlobal.encode (u : UseGlobal) : Bytes := u.gci.encode

/-- `DeterministicStateInitAction` (tag 11): `state_init ‖ deposit`. -/
structure Dsi where
  stateInit : StateInit
  deposit : Nat
  deriving DecidableEq, Repr

def pDsi : P Dsi := fun bs => do
  let (s, bs) ← pStateInit bs
  let (d, bs) ← pU128 "deposit" bs
  pure (⟨s, d⟩, bs)

def Dsi.encode (d : Dsi) : Bytes := d.stateInit.encode ++ u128 d.deposit


/-- `validate_global_contract_identifier` (`action_validation.rs:128-131, 452-462`): `CodeHash` is
always valid; `AccountId` must pass `AccountId::validate`. Note this is *only* account-id validity —
implicit ids are not rejected here. -/
def gciValid : Gci → Bool
  | .codeHash _ => true
  | .accountId id => AccountId.valid id

/-- `max_length_storage_key` (`parameters.snap:207`, `wasm_config.limit_config`). -/
def maxStorageKey : Nat := 2048
/-- `max_length_storage_value` (`parameters.snap:208`). -/
def maxStorageValue : Nat := 4194304

/-! ### Deterministic account id (`core/primitives/src/utils.rs:467-478`)

`"0s" ‖ hex(keccak256(borsh(state_init))[12..32])`. The hash is **Keccak-256**, not SHA-256 and not
SHA3-256; `NearSpecV3.Wasm.Crypto.keccak256` is the original-Keccak sponge nearcore's
`sha3::Keccak256` produces. -/

/-- Lowercase hex of a byte list. -/
def hexOf (b : Bytes) : Bytes :=
  b.foldl (fun acc x =>
    let d := fun (n : Nat) => if n < 10 then UInt8.ofNat (48 + n) else UInt8.ofNat (87 + n)
    acc ++ [d (x.toNat / 16), d (x.toNat % 16)]) []

/-- Local copy of the `Bytes → ByteArray` coercion used by the WASM layer
(`D3/FunctionCall.lean:36`); not imported because that module is off-limits for this lane. -/
def toBA (b : Bytes) : ByteArray := ⟨b.toArray⟩

/-- `derive_near_deterministic_account_id` (`utils.rs:470-478`): `"0s" ‖ hex(keccak256(..)[12:32])`. -/
def deriveDetAccountId (s : StateInit) : Bytes :=
  let h := (NearSpecV3.Wasm.Crypto.keccak256 (toBA s.encode)).toList
  [48, 115] ++ hexOf ((h.drop 12).take 20)


/-- `validate_deterministic_state_init` (`action_validation.rs:422-450`): the identifier is valid, the
receiver equals `derive_near_deterministic_account_id(state_init)`, and every key/value is within
`max_length_storage_key`/`max_length_storage_value`. -/
def dsiValid (acct : Bytes) (d : Dsi) : Bool :=
  gciValid d.stateInit.code &&
  deriveDetAccountId d.stateInit == acct &&
  d.stateInit.data.all fun (k, v) =>
    k.length ≤ maxStorageKey && v.length ≤ maxStorageValue

end NearSpecV3.D3.L4
