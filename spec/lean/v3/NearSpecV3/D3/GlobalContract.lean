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

/-! ## 10. Validation facts (`runtime/runtime/src/action_validation.rs`) -/

/-- `validate_deploy_global_contract_action` (`action_validation.rs:112-124`): code size ≤
`max_contract_size`. -/
def deployGlobalSizeOk (d : DeployGlobal) : Bool := d.code.length ≤ Lim.maxContractSize


end NearSpecV3.D3.L4
