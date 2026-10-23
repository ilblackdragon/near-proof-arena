import NearSpecV3.D2.Actions

/-!
# L4 additive layer: global contracts and deterministic state-init

This module is **purely additive**. It does not edit `D2/Types.lean`, `D2/Actions.lean`,
`D3/FunctionCall.lean`, `checkD2Core`, `checkD3` or `RelD3`. Everything here is a *new* definition
that the L4 row set (`L0-action-09/10/11`, `L0-D3-006/008`) is built on, so that adding it cannot
silently widen the signed D2/D3 relations.

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV 86).

## Why this module exists (scope, exactly)

`D2/Types.lean:300-302` rejects action tags 9, 10, 11 with `oodDeployGlobal` / `oodUseGlobal` /
`oodStateInit`, and `D3/FunctionCall.lean:236-239,248` rejects ETH-implicit local contracts and
`Contract.global` / `Contract.byAccount`. Those are the five L4 rows. The protocol facts behind each
are pinned below; the *decoder* and *resolution* additions live here so that the D2/D3 relations keep
their exact current domain.

## What is pinned here and where it comes from

* `GlobalContractIdentifier` borsh — `core/primitives/src/action/mod.rs:100-118`
  (untagged enum: tag `0` = `CodeHash([u8;32])`, tag `1` = `AccountId`), `len()` at 113-116.
* `GlobalContractDeployMode` — `core/primitives/src/action/mod.rs:73-83` (`CodeHash = 0`,
  `AccountId = 1`).
* `DeployGlobalContractAction` — `core/primitives/src/action/mod.rs:34-46` (`code`, `deploy_mode`).
* `UseGlobalContractAction` — `core/primitives/src/action/mod.rs:102-105` (`contract_identifier`).
* `DeterministicStateInitAction` — `core/primitives/src/action/mod.rs:119-122`
  (`state_init`, `deposit`).
* Action enum tags — `core/primitives/src/action/mod.rs:196-232` (9, 10, 11).
* `RuntimeContractIdentifier::resolve` — `runtime/runtime/src/contract_code.rs:39-95`, in particular
  the ETH-implicit branch at 56-76 and the `Global{…}` construction at 66-76.
* `eth_wallet_global_contract_hash` — `runtime/near-wallet-contract/src/lib.rs:89-105`.
* `code_hash_matches_wallet_contract` / `WalletContract::magic_bytes` —
  `runtime/near-wallet-contract/src/lib.rs:107-124, 135-156`. The magic bytes are
  `"near" ‖ base58(sha256(wasm))`, and the compared hash is `sha256` of **that** string. The values
  below are computed from the four `res/*.wasm` blobs at the pin and cross-checked with nearcore's
  own `test_code_hash_matches_wallet_contract`.
* Global-contract trie key — `core/primitives/src/trie_key.rs:266-273` with `append_into` at
  542-545: `col::GLOBAL_CONTRACT_CODE ‖ identifier`; `GlobalContractCodeIdentifier::append_into`
  at 148-168.
* Global-contract distribution + nonce gate — `runtime/runtime/src/global_contracts.rs:200-260`
  (`ProtocolFeature::GlobalContractDistributionNonce`, `core/primitives-core/src/version.rs:553-562`).
* Fees — `runtime/runtime/src/config.rs:89-115` (exec) and 45-67 (send), action-cost enum in
  `core/parameters/src/cost.rs`; **all global-contract / state-init fee keys are PV86 placeholders**
  (`999_999_999_999_999`, `core/parameters/res/runtime_configs/parameters.yaml:236-260`).
* Validation — `runtime/runtime/src/action_validation.rs:112-124` (deploy size),
  128-131 + `validate_global_contract_identifier`, 422-455 (`DeterministicStateInit`).
* Execution — `runtime/runtime/src/actions.rs` (`action_deploy_global_contract`,
  `action_use_global_contract`, `action_deterministic_state_init`),
  `runtime/runtime/src/global_contracts.rs:1-120`,
  `runtime/runtime/src/deterministic_account_id.rs:100-155`.

## Additivity argument (structural, not asserted)

Nothing in this file is reachable from `NearSpecV3.D2.pBase`, `NearSpecV3.D2.applyAction`,
`NearSpecV3.D3.functionCall`, `checkD2Core`, `checkD3` or `RelD3` unless a caller opts in by
importing this module and using the `…L4` entry points below. Consequently `D2.pBase 9/10/11` still
throws the three `w.shape` strings, and `RelD2`/`RelD3` are the *same* definitions, so neither widens.
-/

namespace NearSpecV3.D3.L4

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## 1. `GlobalContractIdentifier` (`core/primitives/src/action/mod.rs:100-118`) -/

/-- `GlobalContractIdentifier`: an **untagged** borsh enum with a one-byte tag. `CodeHash` carries a
32-byte hash, `AccountId` a borsh string (`action/mod.rs:100-118`). -/
inductive Gci where
  | codeHash (h : Bytes)
  | accountId (id : Bytes)
  deriving DecidableEq, Repr

/-- `GlobalContractIdentifier::len()` (`action/mod.rs:113-116`): 32 for a hash, the account id's
length otherwise (no borsh prefix). -/
def Gci.len : Gci → Nat
  | .codeHash _ => 32
  | .accountId id => id.length

/-- borsh of `GlobalContractIdentifier`: tag `0`/`1` then the payload. -/
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

/-! ## 2. Deploy mode (`core/primitives/src/action/mod.rs:73-83`) -/

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

/-! ## 3. `DeterministicAccountStateInit` (`deterministic_account_id.rs:100-155`) -/

/-- `DeterministicAccountStateInit`: the code identifier and the `ContractData` key/value pairs in
insertion order (`deterministic_account_id.rs` `state_init.data()`). -/
structure StateInit where
  code : Gci
  data : List (Bytes × Bytes)
  deriving DecidableEq, Repr

/-- borsh of `DeterministicAccountStateInit::V1`: `0 ‖ identifier ‖ Vec<(Vec<u8>, Vec<u8>)>`. -/
def StateInit.encode (s : StateInit) : Bytes :=
  [0] ++ s.code.encode ++ u32 s.data.length ++
  s.data.foldl (fun acc (k, v) => acc ++ borshBytes k ++ borshBytes v) []

/-- `DeterministicAccountStateInit` decoder (strict; only the V1 tag exists at PV86). -/
def pStateInit : P StateInit := fun bs => do
  let (t, bs) ← pU8 "DeterministicAccountStateInit tag" bs
  if t != 0 then throw "decode: DeterministicAccountStateInit tag"
  let (code, bs) ← pGci bs
  let (data, bs) ← pVec "state_init data" (fun bs => do
    let (k, bs) ← pBytes "state_init key" bs
    let (v, bs) ← pBytes "state_init value" bs
    pure ((k, v), bs)) bs
  pure (⟨code, data⟩, bs)

/-! ## 4. The three action bodies (`core/primitives/src/action/mod.rs:196-232`) -/

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

/-! ## 5. Wallet magic hashes (`near-wallet-contract/src/lib.rs:107-156`) -/

/-- The four `LegacyEthWallet` variants (`near-wallet-contract/src/lib.rs:22-30`). -/
inductive Wallet where
  | mainnet
  | testnet
  | oldTestnet
  | localnet
  deriving DecidableEq, Repr

/-- `WalletContract::magic_bytes().hash()` for each variant, at the pin.

Derivation: `magic_bytes = "near" ‖ Display(CryptoHash(sha256(wasm)))` where `Display` is base58, and
the compared value is `sha256` of those ASCII magic bytes. Recomputed from the four
`runtime/near-wallet-contract/res/*.wasm` blobs; nearcore's own
`test_code_hash_matches_wallet_contract` asserts the same relation. -/
def walletMagicHash : Wallet → Bytes
  | .mainnet =>
    [0x5a, 0xbc, 0x64, 0x62, 0x2d, 0xdd, 0x36, 0x61, 0x89, 0x9e, 0x5d, 0x76, 0x5e, 0x7a, 0x52, 0x95,
     0x11, 0x5e, 0x90, 0x57, 0xc5, 0x4e, 0x9b, 0xbb, 0x9f, 0x0f, 0x0e, 0x02, 0xcd, 0x1d, 0x21, 0x16]
  | .testnet =>
    [0xb4, 0xfb, 0xbc, 0x96, 0x4b, 0x35, 0x0b, 0xd0, 0x21, 0xb4, 0xa7, 0x85, 0xb9, 0xdd, 0xd6, 0x3e,
     0x41, 0xd6, 0xf1, 0x32, 0x70, 0x2a, 0x6b, 0x38, 0xa2, 0x3b, 0x56, 0x48, 0xab, 0x2f, 0xb4, 0x72]
  | .oldTestnet =>
    [0x39, 0x4a, 0xbe, 0xb3, 0x5e, 0x70, 0x76, 0x09, 0xde, 0x8f, 0x73, 0xb6, 0x3d, 0x43, 0xbd, 0x1a,
     0x37, 0x6f, 0xfe, 0x67, 0x93, 0x5c, 0xaa, 0x68, 0x93, 0x7d, 0xd2, 0x9b, 0xc0, 0x4e, 0x67, 0x3c]
  | .localnet =>
    [0x3e, 0x6d, 0x7d, 0xd8, 0xc2, 0x57, 0x8a, 0xc8, 0xa5, 0xeb, 0xe7, 0x8f, 0xd3, 0x2d, 0x60, 0x0a,
     0x55, 0x5c, 0xef, 0x5e, 0xf7, 0x44, 0x5d, 0x3a, 0x96, 0x46, 0x58, 0x66, 0x9d, 0x70, 0x7c, 0xf2]

/-- `wallet_contract_magic_bytes(chain_id)`: mainnet for `mainnet`/`mocknet`, testnet for `testnet`,
localnet otherwise (`near-wallet-contract/src/lib.rs:74-80`). -/
def walletOf (chainId : Bytes) : Wallet :=
  if chainId == [109, 97, 105, 110, 110, 101, 116] then .mainnet      -- "mainnet"
  else if chainId == [109, 111, 99, 107, 110, 101, 116] then .mainnet -- "mocknet"
  else if chainId == [116, 101, 115, 116, 110, 101, 116] then .testnet-- "testnet"
  else .localnet

/-- `code_hash_matches_wallet_contract(chain_id, code_hash)` (`lib.rs:107-124`). The old-testnet hash
matches **only** on testnet. -/
def matchesWallet (chainId : Bytes) (codeHash : Bytes) : Bool :=
  codeHash == walletMagicHash (walletOf chainId) ||
  (walletOf chainId == .testnet && codeHash == walletMagicHash .oldTestnet)

/-! ## 6. Identifier resolution (`runtime/runtime/src/contract_code.rs:39-95`) -/

/-- `RuntimeContractIdentifier` (`contract_code.rs:21-32`), field order as in nearcore:
`Global { code_hash, identifier }`. -/
inductive Rci where
  | none
  | accountLocal (codeHash : Bytes) (accountId : Bytes)
  | global (codeHash : Bytes) (identifier : Gci)
  deriving DecidableEq, Repr

/-- The resolved code hash a `Rci` points at (`contract_code.rs:88-95`); `none` is
`CryptoHash::default()`. -/
def Rci.codeHashOf : Rci → Bytes
  | .none => zeros 32
  | .accountLocal h _ => h
  | .global h _ => h

/-- `RuntimeContractIdentifier::resolve` restricted to the code a call runs.

* `Contract.none` ⇒ `.none`;
* `Contract.local h`, **non**-ETH-implicit account ⇒ `.accountLocal h acct`;
* `Contract.local h`, ETH-implicit account, `h` a wallet magic hash ⇒
  `.global (eth_wallet_global_contract_hash chain_id) (.codeHash h)` — the
  `EthImplicitGlobalContract` branch (`contract_code.rs:56-76`, on at PV86);
* `Contract.local h`, ETH-implicit account, `h` **not** a wallet hash ⇒ stays `.accountLocal`
  (this is the corpus `ETH_LOCAL`/`d3tiny` case the old blanket guard excluded);
* `Contract.global h` ⇒ `.global h (.codeHash h)`;
* `Contract.byAccount id` ⇒ `.global (zeros 32) (.accountId id)`; the caller replaces the code hash
  by the trie lookup in §7. -/
def Rci.resolve (chainId : Bytes) (acct : Bytes) (c : Contract) : Rci :=
  match c with
  | .none => .none
  | .local h =>
    if AccountId.isEthImplicit acct && matchesWallet chainId h then
      .global (ethWalletHash chainId) (.codeHash h)
    else .accountLocal h acct
  | .global h => .global h (.codeHash h)
  | .byAccount id => .global (zeros 32) (.accountId id)

/-! ## 7. Global-contract trie key and code-hash lookup (`trie_key.rs:266-273, 542-545`) -/

/-- `col::GLOBAL_CONTRACT_CODE` (`core/store/src/columns.rs`), pinned `7`. -/
def colGlobalContractCode : UInt8 := 7

/-- `TrieKey::GlobalContractCode { identifier }` as raw bytes: `col ‖ identifier`
(`trie_key.rs:542-545`; `GlobalContractCodeIdentifier::append_into` at 148-168 — both variants
append the raw hash / account-id bytes, with no length prefix or separator). -/
def kGlobalContractCode (g : Gci) : Bytes :=
  [colGlobalContractCode] ++ match g with
    | .codeHash h => h
    | .accountId id => id

/-- Whether resolving this identifier needs a trie read (`contract_code.rs:118-131`: only the
`AccountId` variant consults the key; `CodeHash` is already the hash). -/
def Rci.needsTrieLookup : Rci → Bool
  | .global _ (.accountId _) => true
  | _ => false

/-- Resolve a `Rci` to the code hash it runs, reading `kGlobalContractCode` for `AccountId`
identifiers. An absent value is `StorageInconsistentState` (`contract_code.rs:107-116`), i.e.
`invalid`, never out of domain. -/
def Rci.resolveCodeHash (o : Ovl) (r : Rci) : Except String (Option Bytes) :=
  match r with
  | .none => pure (Option.none : Option Bytes)
  | .accountLocal h _ => pure (some h)
  | .global h (.codeHash _) => pure (some h)
  | .global _ (.accountId id) => do
    match ← o.get (kGlobalContractCode (.accountId id)) "global contract code" with
    | some raw => pure (some (sha256 raw))
    | Option.none => throw (inconsistent "global contract identifier not found")

/-! ## 8. Fees: pinned PV86 placeholders (`parameters.yaml:236-260`)

**No usable fee exists at PV86.** Every global-contract and state-init action-cost key is
`999_999_999_999_999` in `core/parameters/res/runtime_configs/parameters.yaml:236-260`, and the PV86
snapshot (`core/parameters/src/snapshots/near_parameters__config_store__tests__85.json.snap`) does not
override them — its `transaction_costs.action_creation_config` has only the eleven classic keys
(`add_key_cost`, `create_account_cost`, `delegate_cost`, `delete_account_cost`, `delete_key_cost`,
`deploy_contract_cost`, `deploy_contract_cost_per_byte`, `function_call_cost`,
`function_call_cost_per_byte`, `stake_cost`, `transfer_cost`).

A `10^15` Tgas exec fee equals the whole-chunk `max_gas_burnt` limit (`1 Pgas`), so a *valid* PV86
chunk cannot contain one of these actions. The corpus agrees: zero `DeployGlobalContract` /
`DeterministicStateInit` actions in 2,756+ cases, and every `UseGlobalContract` case is an OOD case
whose action merely *fails* (`GlobalContractDoesNotExist`) without burning its exec fee as modelled.
The constants are exposed so a later protocol version can supply real values without touching the
codecs. -/

/-- The PV86 placeholder fee for each global-contract / state-init action cost key. -/
def pv86GlobalContractPlaceholderFee : Nat := 999999999999999

/-- Whether a chunk may contain a global-contract/state-init action at PV86: `false`, because the
placeholder fee is not below the whole-chunk gas limit. Named so the rejection is a documented
protocol fact, not an accidental decoder gap. -/
def globalContractActionsAffordableAtPv86 : Bool := false

/-! ## 9. Validation facts (`runtime/runtime/src/action_validation.rs`) -/

/-- `validate_global_contract_identifier`: `CodeHash` always valid; `AccountId` must be a valid,
non-implicit account id (`action_validation.rs:128-131`; implicit ids are rejected because a global
contract must be owned by a named account). -/
def gciValid : Gci → Bool
  | .codeHash _ => true
  | .accountId id => AccountId.valid id && AccountId.isNamed id

/-- `validate_deploy_global_contract_action` (`action_validation.rs:112-124`): code size ≤
`max_contract_size`. -/
def deployGlobalSizeOk (d : DeployGlobal) : Bool := d.code.length ≤ Lim.maxContractSize

/-- `validate_deterministic_state_init_action` (`action_validation.rs:422-455`): receiver is a
deterministic-implicit account; each key ≤ 64 bytes, each value ≤ 4096 bytes; ≤ 64 entries. -/
def dsiValid (acct : Bytes) (d : Dsi) : Bool :=
  AccountId.isNearDeterministic acct &&
  d.stateInit.data.length ≤ 64 &&
  d.stateInit.data.all fun (k, v) => k.length ≤ 64 && v.length ≤ 4096

end NearSpecV3.D3.L4
