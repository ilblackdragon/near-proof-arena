import NearSpecV3.D2.Actions
import NearSpecV3.Wasm.Crypto

/-!
# L4 additive layer: global contracts and deterministic state-init

This module is **purely additive**. It does not edit `D2/Types.lean`, `D2/Actions.lean`,
`D3/FunctionCall.lean`, `checkD2Core`, `checkD3` or `RelD3`. Everything here is a *new* definition
that the L4 row set (`L0-action-09/10/11`, `L0-D3-006/008`) is built on, so that adding it cannot
silently widen the signed D2/D3 relations.

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV 86).

## Why this module exists (scope, exactly)

`D2/Types.lean:299-302` rejects action tags 9, 10, 11 with `oodDeployGlobal` / `oodUseGlobal` /
`oodStateInit`, and `D3/FunctionCall.lean:236-239,248` rejects ETH-implicit local contracts and
`Contract.global` / `Contract.byAccount`. Those are the five L4 rows. The protocol facts behind each
are pinned below; the *decoder* and *resolution* additions live here so that the D2/D3 relations keep
their exact current domain.

## Protocol facts pinned here (with the correction history)

An earlier revision of this module claimed "all global-contract / state-init fee keys are PV86
placeholders". **That is false and is corrected below.** The `999_999_999_999_999` values are the
*pre-activation* defaults in `parameters.yaml`; protocol 77 replaced every one of them
(`core/parameters/res/runtime_configs/77.yaml:2-55`), so at PV86 they are ordinary small fees. The
consequence reverses: a PV86 chunk **can** contain these actions, and 34 recorded corpus cases do
(`corpora/d3c9/ood/*` with `d3_violations` containing `w.shape`, all `nearcore: "ok"`).

* `GlobalContractIdentifier` borsh — `core/primitives-core/src/global_contract.rs:16-35`
  (`#[borsh(use_discriminant = true)] #[repr(u8)]`: tag `0` = `CodeHash(CryptoHash)`,
  tag `1` = `AccountId`), `len()` at 37-44 (32 / account length, **no** borsh prefix).
* `GlobalContractDeployMode` — `core/primitives/src/action/mod.rs:133-146` (`CodeHash = 0`,
  `AccountId = 1`).
* `DeployGlobalContractAction` — `core/primitives/src/action/mod.rs:157-168` (`code`, `deploy_mode`).
* `UseGlobalContractAction` — `core/primitives/src/action/mod.rs:201-203` (`contract_identifier`).
* `DeterministicStateInitAction` — `core/primitives/src/action/mod.rs:218-221` (`state_init`, `deposit`).
* Action enum tags — `core/primitives/src/action/mod.rs:363-365` (9, 10, 11).
* `DeterministicAccountStateInit::V1` — `core/primitives-core/src/deterministic_account_id.rs:22-42`
  (`V1 = 0`, then `code: GlobalContractIdentifier`, then `data: BTreeMap<Vec<u8>, Vec<u8>>`).
  **`data` is a `BTreeMap`, so its borsh encoding is key-sorted**, not insertion-ordered.
* `RuntimeContractIdentifier::resolve` — `runtime/runtime/src/contract_code.rs:39-95`, in particular
  the ETH-implicit branch at 56-76 and the `Global{…}` construction at 66-76. The `LegacyEthWallet`
  variant (21-31) is **unreachable at PV86**: `config.eth_implicit_global_contract` is set from
  `ProtocolFeature::EthImplicitGlobalContract`, which is enabled at protocol 83
  (`core/primitives-core/src/version.rs:556`), and `parameters.snap:281` records
  `eth_implicit_global_contract true`.
* `eth_wallet_global_contract_hash` — `runtime/near-wallet-contract/src/lib.rs:89-105`.
* `code_hash_matches_wallet_contract` / `WalletContract::magic_bytes` —
  `runtime/near-wallet-contract/src/lib.rs:107-124, 135-156`. The magic bytes are
  `"near" ‖ base58(sha256(wasm))`, and the compared hash is `sha256` of **that** string. The four
  values below are recomputed from the four `runtime/near-wallet-contract/res/*.wasm` blobs at the pin.
* Global-contract trie key — `core/primitives/src/trie_key.rs:266-273` with `append_into` at
  542-545: `col::GLOBAL_CONTRACT_CODE (18) ‖ borsh(GlobalContractCodeIdentifier)`;
  `GlobalContractCodeIdentifier::append_into` at 155-157 uses `borsh::to_writer`, i.e. **tag byte
  plus (for `AccountId`) a `u32` length prefix** — not the raw bytes.
* Global-contract distribution + nonce gate — `runtime/runtime/src/global_contracts.rs:143-260`
  (`ProtocolFeature::GlobalContractDistributionNonce`, `version.rs:553-562`, enabled at 83).
* Fees — `core/parameters/src/config.rs` accessors; effective PV86 values in
  `core/parameters/res/runtime_configs/77.yaml:2-55` and `parameters.snap:263-281`; the send/exec
  formulas are `runtime/runtime/src/config.rs:150-199` and 320-356.
* Validation — `runtime/runtime/src/action_validation.rs:112-124` (deploy size),
  128-131 + `validate_global_contract_identifier`, 422-455 (`DeterministicStateInit`).
* Execution — `runtime/runtime/src/global_contracts.rs:30-131`
  (`action_deploy_global_contract`, `action_use_global_contract`, `use_global_contract`),
  `runtime/runtime/src/deterministic_account_id.rs:17-165`.
* Deterministic account id — `core/primitives/src/utils.rs:467-478`:
  `"0s" ‖ hex(keccak256(borsh(state_init))[12..32])`.

## Additivity argument (structural, not asserted)

Nothing in this file is reachable from `NearSpecV3.D2.pBase`, `NearSpecV3.D2.applyAction`,
`NearSpecV3.D3.functionCall`, `checkD2Core`, `checkD3` or `RelD3` unless a caller opts in by
importing this module and using the `…L4` entry points below. Consequently `D2.pBase 9/10/11` still
throws the three `w.shape` strings, and `RelD2`/`RelD3` are the *same* definitions, so neither widens.
-/

namespace NearSpecV3.D3.L4

open NearSpec NearSpecV3 NearSpecV3.D2

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

/-! ## 5. Wallet magic hashes (`near-wallet-contract/src/lib.rs:107-156`)

`walletMagicHash w` is `sha256("near" ‖ base58(sha256(wasm)))`, the value `check_magic_bytes`
compares against. These are **not** the contract code hashes; those are the values in
`ethWalletHash` (§6), and the two differ for every variant. -/

/-- The four `LegacyEthWallet` variants (`near-wallet-contract/src/lib.rs:22-32`). -/
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
`test_code_hash_matches_wallet_contract` asserts the same relation. The `global_contract_mainnet.wasm`
blob is the *global* contract, not a legacy wallet, and is not a `Wallet` variant. -/
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

/-- `LegacyEthWallet::resolve` (`near-wallet-contract/src/lib.rs:37-52`): the first variant whose
magic hash matches. Order matters only if two blobs collide, which they do not. -/
def resolveWallet (codeHash : Bytes) : Option Wallet :=
  if codeHash == walletMagicHash .mainnet then some .mainnet
  else if codeHash == walletMagicHash .testnet then some .testnet
  else if codeHash == walletMagicHash .oldTestnet then some .oldTestnet
  else if codeHash == walletMagicHash .localnet then some .localnet
  else none

/-- `wallet_contract_magic_bytes(chain_id)` (`lib.rs:64-70`): mainnet for `mainnet`/`mocknet`,
testnet for `testnet`, localnet otherwise. (`chains::MAINNET`/`MOCKNET`/`TESTNET`.) -/
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

/-- `RuntimeContractIdentifier` (`contract_code.rs:21-31`), field order as in nearcore:
`Global { code_hash, identifier }`. `LegacyEthWallet` is modelled because nearcore has the variant,
but it is unreachable when `eth_implicit_global_contract` is on, which it is at PV86 (§7). -/
inductive Rci where
  | none
  | accountLocal (codeHash : Bytes) (accountId : Bytes)
  | global (codeHash : Bytes) (identifier : Gci)
  | legacyEthWallet (w : Wallet)
  deriving DecidableEq, Repr

/-- The resolved code hash a `Rci` points at (`contract_code.rs:88-95`); `.none` is
`CryptoHash::default()`. For `.legacyEthWallet` nearcore returns the built-in wallet's own contract
hash (`contract_code.rs:91`); that value is not modelled here, so the field is `zeros 32` and the
constructor is documented as unreachable at PV86 (§7). -/
def Rci.codeHashOf : Rci → Bytes
  | .none => zeros 32
  | .accountLocal h _ => h
  | .global h _ => h
  | .legacyEthWallet _ => zeros 32

/-- `RuntimeContractIdentifier::resolve` restricted to the code a call runs, with
`eth_implicit_global_contract = true` (PV86).

* `Contract.none` ⇒ `.none`;
* `Contract.local h`, **non**-ETH-implicit account ⇒ `.accountLocal h acct`;
* `Contract.local h`, ETH-implicit account, `h` a wallet magic hash ⇒
  `.global (eth_wallet_global_contract_hash chain_id) (.codeHash _)` — the
  `EthImplicitGlobalContract` branch (`contract_code.rs:56-76`, on at PV86);
* `Contract.local h`, ETH-implicit account, `h` **not** a wallet hash ⇒ stays `.accountLocal`
  (this is the corpus `e.eth_implicit_local` case the old blanket guard excluded);
* `Contract.global h` ⇒ `.global h (.codeHash h)`;
* `Contract.byAccount id` ⇒ `.global (zeros 32) (.accountId id)`; the caller replaces the code hash
  by the trie lookup in §7. -/
def Rci.resolve (chainId : Bytes) (acct : Bytes) (c : Contract) : Rci :=
  match c with
  | .none => .none
  | .local h =>
    if AccountId.isEthImplicit acct && (resolveWallet h).isSome then
      .global (ethWalletHash chainId) (.codeHash (ethWalletHash chainId))
    else .accountLocal h acct
  | .global h => .global h (.codeHash h)
  | .byAccount id => .global (zeros 32) (.accountId id)

/-- The same resolution with `eth_implicit_global_contract = false`, i.e. protocol < 83. Kept so the
`LegacyEthWallet` branch is modelled and can be shown unreachable at PV86 rather than ignored. -/
def Rci.resolvePre83 (chainId : Bytes) (acct : Bytes) (c : Contract) : Rci :=
  match c with
  | .none => .none
  | .local h =>
    if AccountId.isEthImplicit acct then
      match resolveWallet h with
      | Option.some w => .legacyEthWallet w
      | Option.none => .accountLocal h acct
    else .accountLocal h acct
  | .global h => .global h (.codeHash h)
  | .byAccount id => .global (zeros 32) (.accountId id)

/-! ## 7. The PV86 configuration flag

`RuntimeContractIdentifier::resolve` branches on `config.eth_implicit_global_contract`
(`contract_code.rs:61`), which comes from `ProtocolFeature::EthImplicitGlobalContract`
(`core/primitives-core/src/version.rs:556`, enabled at **83**) via the parameter table
(`core/parameters/src/parameter_table.rs:465`) and `parameters.snap:281` (`true`). So at PV86 the
`LegacyEthWallet` branch is dead: an ETH-implicit account whose local hash is a wallet magic hash
resolves to the *global* wallet contract. This answers UQ-007. -/

/-- `eth_implicit_global_contract` at PV86 (`version.rs:556`, `parameters.snap:281`). -/
def ethImplicitGlobalContractPv86 : Bool := true

/-- `Rci.resolve` is the PV86 branch, so it never constructs `LegacyEthWallet`. This is the UQ-007
answer as a checked statement: the arm exists in nearcore's enum but is dead here. -/
theorem legacyWallet_unreachable_pv86 (chainId : Bytes) (acct : Bytes) (c : Contract) :
    ∀ w, Rci.resolve chainId acct c ≠ .legacyEthWallet w := by
  intro w h
  cases c with
  | «none» => simp [Rci.resolve] at h
  | «local» hh =>
    by_cases hc : AccountId.isEthImplicit acct && (resolveWallet hh).isSome
    · simp [Rci.resolve, hc] at h
    · simp [Rci.resolve, hc] at h
  | «global» hh => simp [Rci.resolve] at h
  | byAccount id => simp [Rci.resolve] at h

/-- At PV86 an ETH-implicit account with a wallet-hash local contract resolves to the global wallet
contract's code hash, not to its own local hash. -/
theorem ethImplicit_resolves_global (chainId acct h : Bytes)
    (hEth : AccountId.isEthImplicit acct = true) (hW : (resolveWallet h).isSome = true) :
    Rci.resolve chainId acct (.local h) = .global (ethWalletHash chainId) (.codeHash (ethWalletHash chainId)) := by
  simp [Rci.resolve, hEth, hW]

/-! ## 8. Global-contract trie key and code-hash lookup

`TrieKey::GlobalContractCode { identifier }` (`trie_key.rs:266-273`) appends the column byte and
then `GlobalContractCodeIdentifier::append_into` (`trie_key.rs:155-157`), which is
`borsh::to_writer` — a tag byte plus, for `AccountId`, a `u32` length prefix. The earlier revision of
this module used `[7] ++ raw`, which was wrong twice: the column is **18**
(`trie_key.rs:73`) and the identifier is **borsh-encoded**, so an `AccountId` key carries its length
prefix (`trie_key.rs:133-143`). -/

/-- `col::GLOBAL_CONTRACT_CODE` (`core/primitives/src/trie_key.rs:73`). -/
def colGlobalContractCode : UInt8 := 18

/-- `col::GLOBAL_CONTRACT_NONCE` (`core/primitives/src/trie_key.rs:75`). -/
def colGlobalContractNonce : UInt8 := 19

/-- `GlobalContractCodeIdentifier` borsh = the same encoding as `GlobalContractIdentifier`
(`trie_key.rs:133-143` vs `global_contract.rs:16-35`; the `From` impl at `trie_key.rs:158-168` is
field-preserving). -/
def kGlobalContractCode (g : Gci) : Bytes := [colGlobalContractCode] ++ g.encode

/-- `TrieKey::GlobalContractNonce { identifier }` (`trie_key.rs:273-276`, `552-556`). -/
def kGlobalContractNonce (g : Gci) : Bytes := [colGlobalContractNonce] ++ g.encode

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
    let key := kGlobalContractCode (.accountId id)
    -- nearcore get_ref().value_hash(): code bytes need not be in the witness.
    match o.lookup key with
    | some (some raw) => pure (some (sha256 raw))
    | some Option.none => throw (inconsistent "global contract identifier not found")
    | Option.none =>
      match o.trie.findRef (nibbles key) with
      | some (some slot) => pure (some (slot.valueRef.drop 4))
      | some Option.none => throw (inconsistent "global contract identifier not found")
      | Option.none => throw (missing "global contract identifier")
  | .legacyEthWallet _ => pure (Option.none : Option Bytes)

/-! ## 9. Fees: the effective PV86 values

Global-contract and state-init action costs were placeholders (`999_999_999_999_999`) **before**
protocol 77 and were all replaced there (`runtime_configs/77.yaml:2-55`), with the deterministic
state-init execution fee replaced again at 85 (`runtime_configs/85.yaml:28-39`). The effective PV86
values (`parameters.snap:86-97, 263-281`) are reproduced here. `Fee` is `(send_sir, send_not_sir,
execution)`; `execCompute` is the separate compute component where it differs. -/

/-- `action_deploy_global_contract` (`parameters.snap:263-267`, `77.yaml:3-14`). -/
def feeDeployGlobalBase : Fee := .mk3 184765750000 184765750000 184765750000
/-- `action_deploy_global_contract_per_byte` (`parameters.snap:267-271`, `77.yaml:15-26`); the compute
component is `70_000_000` (`core/parameters/src/cost.rs:631`). -/
def feeDeployGlobalByte : Fee := .mk3 6812999 47683715 70000000
/-- `action_use_global_contract` (`parameters.snap:275-279`, `77.yaml:27-38`). -/
def feeUseGlobalBase : Fee := .mk3 184765750000 184765750000 184765750000
/-- `action_use_global_contract_per_identifier_byte` (`parameters.snap:279-283`, `77.yaml:39-54`). -/
def feeUseGlobalByte : Fee := .mk3 6812999 47683715 64572944
/-- `action_deterministic_state_init` (`parameters.snap:86-90`, `85.yaml:28-39`). -/
def feeStateInitBase : Fee := .mk3 500000000000 500000000000 7430000000000
/-- `action_deterministic_state_init_per_entry` (`parameters.snap:90-94`). -/
def feeStateInitEntry : Fee := .mk3 0 0 200000000000
/-- `action_deterministic_state_init_per_byte` (`parameters.snap:94-98`). -/
def feeStateInitByte : Fee := .mk3 72000000 72000000 70000000
/-- `global_contract_storage_amount_per_byte = 0.0001 N` (`parameters.snap:272`, `77.yaml:2`). -/
def globalContractStoragePerByte : Nat := 100000000000000000000
/-- `deploy_global_contract_execution_base` (`parameters.snap:273`, `84.yaml:39`), a *compute* cost
charged when the distribution receipt executes, not an action fee. -/
def deployGlobalExecBase : Nat := 20000000000000
/-- `deploy_global_contract_execution_per_byte` (`parameters.snap:274`, `84.yaml:40`). -/
def deployGlobalExecPerByte : Nat := 250000000

/-- Send fee of a `DeployGlobalContract` action (`config.rs:150-161`): base + per byte of `code`. -/
def deployGlobalSend (sir : Bool) (d : DeployGlobal) : Cost :=
  let b := feeDeployGlobalBase.send sir
  let y := (feeDeployGlobalByte.send sir).scale d.code.length
  ⟨b.gas + y.gas, b.compute + y.compute⟩

/-- Exec fee of a `DeployGlobalContract` action (`config.rs:320-328`): base + per byte of `code`. -/
def deployGlobalExec (d : DeployGlobal) : Cost :=
  let b := feeDeployGlobalBase.ex
  let y := feeDeployGlobalByte.ex.scale d.code.length
  ⟨b.gas + y.gas, b.compute + y.compute⟩

/-- Send fee of a `UseGlobalContract` action (`config.rs:162-172`): base + per *identifier* byte
(`Gci.len`, not the borsh length). -/
def useGlobalSend (sir : Bool) (u : UseGlobal) : Cost :=
  let b := feeUseGlobalBase.send sir
  let y := (feeUseGlobalByte.send sir).scale u.gci.len
  ⟨b.gas + y.gas, b.compute + y.compute⟩

/-- Exec fee of a `UseGlobalContract` action (`config.rs:329-337`). -/
def useGlobalExec (u : UseGlobal) : Cost :=
  let b := feeUseGlobalBase.ex
  let y := feeUseGlobalByte.ex.scale u.gci.len
  ⟨b.gas + y.gas, b.compute + y.compute⟩

/-- Send fee of a `DeterministicStateInit` action (`config.rs:173-193`): base + per entry + per byte
of `len_bytes()`. -/
def stateInitSend (sir : Bool) (d : Dsi) : Cost :=
  let b := feeStateInitBase.send sir
  let e := (feeStateInitEntry.send sir).scale d.stateInit.data.length
  let y := (feeStateInitByte.send sir).scale d.stateInit.lenBytes
  ⟨b.gas + e.gas + y.gas, b.compute + e.compute + y.compute⟩

/-- Exec fee of a `DeterministicStateInit` action (`config.rs:338-352`). -/
def stateInitExec (d : Dsi) : Cost :=
  let b := feeStateInitBase.ex
  let e := feeStateInitEntry.ex.scale d.stateInit.data.length
  let y := feeStateInitByte.ex.scale d.stateInit.lenBytes
  ⟨b.gas + e.gas + y.gas, b.compute + e.compute + y.compute⟩

/-! ## 10. Validation facts (`runtime/runtime/src/action_validation.rs`) -/

/-- `validate_global_contract_identifier` (`action_validation.rs:128-131, 452-462`): `CodeHash` is
always valid; `AccountId` must pass `AccountId::validate`. Note this is *only* account-id validity —
implicit ids are not rejected here. -/
def gciValid : Gci → Bool
  | .codeHash _ => true
  | .accountId id => AccountId.valid id

/-- `validate_deploy_global_contract_action` (`action_validation.rs:112-124`): code size ≤
`max_contract_size`. -/
def deployGlobalSizeOk (d : DeployGlobal) : Bool := d.code.length ≤ Lim.maxContractSize

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
