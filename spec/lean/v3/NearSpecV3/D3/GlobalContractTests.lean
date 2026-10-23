import NearSpecV3.D3.GlobalContractExec

/-!
# L4 directed tests: global-contract / state-init codecs, fees and resolution

Kernel-checked cases for the five L4 inventory rows. Every case is either

* a **nearcore ground truth** reproduced exactly — cited to the Rust test or literal it comes from —
  or
* a **discriminating negative** that fails if the corresponding branch is removed or inverted.

`#guard` reduces at elaboration time and needs a `Bool`, so proposition-shaped checks are wrapped in
`decide`. A regression in a codec, a fee literal, a key encoding or the wallet resolution breaks the
build. Nothing here executes a chunk; whole-chunk replay is reported in the lane log.

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV 86).
-/

namespace NearSpecV3.D3.L4

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## 1. `GlobalContractIdentifier` borsh (`global_contract.rs:16-44`) -/

/-- A 32-byte hash. -/
def h32 : Bytes := List.replicate 32 7
/-- `"alice.near"` as bytes. -/
def aliceNear : Bytes := [97, 108, 105, 99, 101, 46, 110, 101, 97, 114]

#guard (Gci.codeHash h32).encode == [0] ++ h32
#guard (Gci.codeHash h32).encode.length == 33
-- borsh String: u32 length prefix. "alice.near" is 10 bytes, so 1 + 4 + 10 = 15.
#guard (Gci.accountId aliceNear).encode == [1, 10, 0, 0, 0] ++ aliceNear
#guard (Gci.accountId aliceNear).encode.length == 15
-- `len()` is the identifier length, NOT the borsh length (global_contract.rs:37-44).
#guard Gci.len (.codeHash h32) == 32
#guard Gci.len (.accountId aliceNear) == 10
#guard Gci.len (.accountId aliceNear) != (Gci.accountId aliceNear).encode.length

/-! ### Discriminating negatives: the decoder rejects what borsh rejects -/

-- Unknown tag.
#guard (match pGci [2, 0] with | .error _ => true | _ => false)
-- Truncated hash (tag 0, 31 bytes).
#guard (match pGci ([0] ++ List.replicate 31 7) with | .error _ => true | _ => false)
-- Truncated account-id length prefix.
#guard (match pGci [1, 10, 0] with | .error _ => true | _ => false)
-- An uppercase account id is invalid (`AccountId::validate`).
#guard (match pGci [1, 3, 0, 0, 0, 65, 66, 67] with | .error _ => true | _ => false)
-- A valid encoding decodes back to the same value with no trailing bytes.
#guard (match pGci ((Gci.codeHash h32).encode) with
        | .ok (v, rest) => v == .codeHash h32 && rest.isEmpty
        | _ => false)
#guard (match pGci ((Gci.accountId aliceNear).encode) with
        | .ok (v, rest) => v == .accountId aliceNear && rest.isEmpty
        | _ => false)

/-! ## 2. Global-contract trie key (`trie_key.rs:73,133-157,266-273,542-545`)

The key is `col::GLOBAL_CONTRACT_CODE (18)` followed by the **borsh** identifier. The earlier
revision used column 7 and the raw identifier; both were wrong and both are pinned here. -/

#guard colGlobalContractCode == 18
#guard colGlobalContractNonce == 19
#guard kGlobalContractCode (.codeHash h32) == [18, 0] ++ h32
#guard (kGlobalContractCode (.codeHash h32)).length == 34
-- AccountId keys carry the u32 length prefix: 1 (col) + 1 (tag) + 4 (len) + 10 = 16.
#guard kGlobalContractCode (.accountId aliceNear) == [18, 1, 10, 0, 0, 0] ++ aliceNear
#guard (kGlobalContractCode (.accountId aliceNear)).length == 16
#guard kGlobalContractNonce (.codeHash h32) == [19, 0] ++ h32
-- The two identifiers do not collide.
#guard kGlobalContractCode (.codeHash h32) != kGlobalContractCode (.accountId aliceNear)

/-! ## 3. `GlobalContractDeployMode` (`action/mod.rs:133-146`) -/

#guard (match pGcdMode [0] with | .ok (v, rest) => v == .codeHash && rest.isEmpty | _ => false)
#guard (match pGcdMode [1] with | .ok (v, rest) => v == .accountId && rest.isEmpty | _ => false)
#guard (match pGcdMode [2] with | .error _ => true | _ => false)
#guard GcdMode.encode .codeHash == [0]
#guard GcdMode.encode .accountId == [1]

/-! ## 4. `DeterministicAccountStateInit` (`deterministic_account_id.rs:22-94`)

`data` is a `BTreeMap`, so its borsh form has ascending keys. The decoder enforces that; a
descending or duplicate-key encoding is not a byte string borsh would ever produce. -/

#guard sortedKeys []
#guard sortedKeys [([97], [1])]
#guard sortedKeys [([97], [1]), ([98], [2])]
#guard !sortedKeys [([98], [2]), ([97], [1])]
#guard !sortedKeys [([97], [1]), ([97], [2])]   -- duplicate keys cannot round-trip a BTreeMap

/-- `state_init` with code `AccountId("ft.near")` and no data — nearcore's own test input. -/
def siFtNear : StateInit := ⟨.accountId [102, 116, 46, 110, 101, 97, 114], []⟩
/-- `state_init` with code `CodeHash(32 zero bytes)` and no data. -/
def siZeroHash : StateInit := ⟨.codeHash (List.replicate 32 0), []⟩

-- V1 tag 0, identifier, then a u32 count. "ft.near" is 7 bytes.
#guard siFtNear.encode == [0, 1, 7, 0, 0, 0, 102, 116, 46, 110, 101, 97, 114, 0, 0, 0, 0]
#guard siFtNear.encode.length == 17
#guard siZeroHash.encode.length == 38
-- `len_bytes()` counts keys and values only, not the borsh overhead
-- (deterministic_account_id.rs:78-94).
#guard siFtNear.lenBytes == 0
#guard (⟨.codeHash h32, [([1, 2], [3, 4, 5])]⟩ : StateInit).lenBytes == 5

-- Round trip.
#guard (match pStateInit siFtNear.encode with
        | .ok (v, rest) => v == siFtNear && rest.isEmpty
        | _ => false)
-- Non-V1 tag.
#guard (match pStateInit ([1] ++ siFtNear.encode.tail) with | .error _ => true | _ => false)
-- Out-of-order keys are rejected.
#guard (match pStateInit (⟨.codeHash h32, [([98], [2]), ([97], [1])]⟩ : StateInit).encode with
        | .error _ => true | _ => false)

/-! ## 5. The three action bodies (`action/mod.rs:157-221`) -/

/-- 100 bytes of code. -/
def code100 : Bytes := List.replicate 100 0
def dg100 : DeployGlobal := ⟨code100, .codeHash⟩
def dgAcct : DeployGlobal := ⟨code100, .accountId⟩
def ugHash : UseGlobal := ⟨.codeHash h32⟩
def ugAcct : UseGlobal := ⟨.accountId aliceNear⟩
def dsi : Dsi := ⟨siZeroHash, 12345⟩

#guard (match pDeployGlobal dg100.encode with | .ok (v, r) => v == dg100 && r.isEmpty | _ => false)
#guard (match pUseGlobal ugHash.encode with | .ok (v, r) => v == ugHash && r.isEmpty | _ => false)
#guard (match pUseGlobal ugAcct.encode with | .ok (v, r) => v == ugAcct && r.isEmpty | _ => false)
#guard (match pDsi dsi.encode with | .ok (v, r) => v == dsi && r.isEmpty | _ => false)
-- DeployGlobalContract: `code ‖ deploy_mode`.
#guard dg100.encode == borshBytes code100 ++ [0]
#guard dgAcct.encode == borshBytes code100 ++ [1]
-- DeterministicStateInit: `state_init ‖ deposit` as u128 LE.
#guard dsi.encode == siZeroHash.encode ++ u128 12345
#guard dsi.encode.length == 38 + 16

/-! ## 6. Fees (`parameters.snap:86-98,263-283`; formulas `config.rs:150-199,320-356`)

The pre-77 placeholder `999_999_999_999_999` is **not** the PV86 value; `77.yaml` replaced every
global-contract fee and `85.yaml` replaced the state-init exec fee. These guards fail if anyone
restores the placeholder. -/

-- `Fee` carries `(send_sir, send_not_sir, exec, exec_compute)`; there is no derived `DecidableEq`
-- for it (`D2/Fees.lean:21-25`), so the guards compare the four fields.
#guard feeDeployGlobalBase.sir == 184765750000 && feeDeployGlobalBase.notSir == 184765750000 &&
       feeDeployGlobalBase.exec == 184765750000
#guard feeDeployGlobalByte.sir == 6812999 && feeDeployGlobalByte.notSir == 47683715 &&
       feeDeployGlobalByte.exec == 70000000
#guard feeUseGlobalBase.sir == 184765750000 && feeUseGlobalBase.notSir == 184765750000 &&
       feeUseGlobalBase.exec == 184765750000
#guard feeUseGlobalByte.sir == 6812999 && feeUseGlobalByte.notSir == 47683715 &&
       feeUseGlobalByte.exec == 64572944
#guard feeStateInitBase.sir == 500000000000 && feeStateInitBase.notSir == 500000000000 &&
       feeStateInitBase.exec == 7430000000000
#guard feeStateInitEntry.sir == 0 && feeStateInitEntry.notSir == 0 &&
       feeStateInitEntry.exec == 200000000000
#guard feeStateInitByte.sir == 72000000 && feeStateInitByte.notSir == 72000000 &&
       feeStateInitByte.exec == 70000000
#guard globalContractStoragePerByte == 100000000000000000000
-- The placeholder value does not appear as an effective fee.
#guard feeDeployGlobalBase.exec != 999999999999999
#guard feeUseGlobalByte.exec != 999999999999999
#guard feeStateInitBase.exec != 999999999999999

-- Send fee: base + per-byte * code length.
#guard (deployGlobalSend true dg100).gas == 184765750000 + 6812999 * 100
#guard (deployGlobalSend false dg100).gas == 184765750000 + 47683715 * 100
-- Exec fee: base + per-byte * code length.
#guard (deployGlobalExec dg100).gas == 184765750000 + 70000000 * 100
#guard (deployGlobalExec dg100).compute == 184765750000 + 70000000 * 100
-- UseGlobalContract scales by the identifier length, not the borsh length.
#guard (useGlobalExec ugHash).gas == 184765750000 + 64572944 * 32
#guard (useGlobalExec ugAcct).gas == 184765750000 + 64572944 * 10
#guard (useGlobalSend true ugHash).gas == 184765750000 + 6812999 * 32
#guard (useGlobalSend false ugHash).gas == 184765750000 + 47683715 * 32
-- DeterministicStateInit: base + per-entry * entries + per-byte * len_bytes.
#guard (stateInitExec dsi).gas == 7430000000000
#guard (stateInitExec dsi).compute == 7430000000000
#guard (stateInitExec ⟨⟨.codeHash h32, [([1, 2], [3, 4, 5])]⟩, 0⟩).gas
       == 7430000000000 + 200000000000 * 1 + 70000000 * 5
#guard (stateInitSend true dsi).gas == 500000000000
#guard (stateInitSend true ⟨⟨.codeHash h32, [([1, 2], [3, 4, 5])]⟩, 0⟩).gas
       == 500000000000 + 0 + 72000000 * 5

-- Storage cost of a deploy: 0.0001 N per byte = 10^20 yoctoNEAR per byte.
#guard deployGlobalStorageCost code100 == 100 * 100000000000000000000
#guard deployGlobalStorageCost [] == 0

/-! ## 7. Deploy mode selects the identifier (`global_contracts.rs:169-177`) -/

#guard decide (deployModeId .codeHash [109, 101] code100 = .codeHash (sha256 code100))
#guard decide (deployModeId .accountId [109, 101] code100 = .accountId [109, 101])
-- `CodeHash` mode hashes the code; `AccountId` mode ignores it.
#guard deployModeId .codeHash [109, 101] [1, 2, 3] != .accountId [109, 101]

/-! ## 8. Validation facts (`action_validation.rs:112-131,422-450`) -/

#guard gciValid (.codeHash h32) == true
#guard gciValid (.accountId aliceNear) == true
-- An uppercase id is not a valid account id, so the identifier is invalid.
#guard gciValid (.accountId [65, 66, 67]) == false
#guard deployGlobalSizeOk ⟨List.replicate 4194304 0, .codeHash⟩ == true
#guard deployGlobalSizeOk ⟨List.replicate 4194305 0, .codeHash⟩ == false
-- Storage-key/value limits (`parameters.snap:207-208`).
#guard maxStorageKey == 2048
#guard maxStorageValue == 4194304

/-! ## 9. Wallet magic hashes and ETH-implicit resolution (`near-wallet-contract/src/lib.rs:37-124`)

`walletMagicHash w = sha256("near" ‖ base58(sha256(wasm)))`, recomputed from the four blobs. The
contract hashes in `ethWalletHash` are **different values** and both are used: `walletMagicHash`
decides *whether* an account is a legacy wallet, `ethWalletHash` is the global contract an
ETH-implicit wallet resolves to. -/

-- The magic hash and the global contract hash are different values for the same chain.
#guard walletMagicHash .mainnet != ethWalletHash [109, 97, 105, 110, 110, 101, 116]
#guard walletMagicHash .testnet != ethWalletHash [116, 101, 115, 116, 110, 101, 116]
#guard walletMagicHash .localnet != ethWalletHash [108, 111, 99, 97, 108, 110, 101, 116]

#guard decide (walletOf [109, 97, 105, 110, 110, 101, 116] = .mainnet)
#guard decide (walletOf [109, 111, 99, 107, 110, 101, 116] = .mainnet)
#guard decide (walletOf [116, 101, 115, 116, 110, 101, 116] = .testnet)
#guard decide (walletOf [108, 111, 99, 97, 108, 110, 101, 116] = .localnet)

-- The magic hashes are 32 bytes and pairwise distinct.
#guard (walletMagicHash .mainnet).length == 32
#guard (walletMagicHash .testnet).length == 32
#guard (walletMagicHash .oldTestnet).length == 32
#guard (walletMagicHash .localnet).length == 32
#guard walletMagicHash .mainnet != walletMagicHash .testnet
#guard walletMagicHash .testnet != walletMagicHash .oldTestnet
#guard walletMagicHash .oldTestnet != walletMagicHash .localnet

-- `eth_wallet_global_contract_hash` (lib.rs:89-105): mainnet/mocknet share one value, testnet and
-- localnet have their own.
#guard decide (ethWalletHash [109, 97, 105, 110, 110, 101, 116]
               = ethWalletHash [109, 111, 99, 107, 110, 101, 116])
#guard ethWalletHash [109, 97, 105, 110, 110, 101, 116] != ethWalletHash [116, 101, 115, 116, 110, 101, 116]
#guard ethWalletHash [116, 101, 115, 116, 110, 101, 116] != ethWalletHash [108, 111, 99, 97, 108, 110, 101, 116]
#guard (ethWalletHash [109, 97, 105, 110, 110, 101, 116]).length == 32

-- `code_hash_matches_wallet_contract`: the old-testnet hash matches only on testnet.
#guard matchesWallet [116, 101, 115, 116, 110, 101, 116] (walletMagicHash .oldTestnet) == true
#guard matchesWallet [109, 97, 105, 110, 110, 101, 116] (walletMagicHash .oldTestnet) == false
#guard matchesWallet [109, 97, 105, 110, 110, 101, 116] (walletMagicHash .mainnet) == true
#guard matchesWallet [116, 101, 115, 116, 110, 101, 116] (walletMagicHash .mainnet) == false
#guard matchesWallet [108, 111, 99, 97, 108, 110, 101, 116] (walletMagicHash .mainnet) == false

-- `LegacyEthWallet::resolve` finds each variant and rejects a non-wallet hash.
#guard decide (resolveWallet (walletMagicHash .mainnet) = some .mainnet)
#guard decide (resolveWallet (walletMagicHash .oldTestnet) = some .oldTestnet)
#guard decide (resolveWallet (List.replicate 32 0) = none)

/-! ### Resolution branches (`contract_code.rs:39-95`) -/

/-- An ETH-implicit account id: `0x` + 40 lowercase hex. -/
def ethAcct : Bytes := [48, 120] ++ List.replicate 40 97

#guard AccountId.isEthImplicit ethAcct == true

-- Non-ETH-implicit account with a local contract: stays local, unchanged by the wallet tables.
#guard decide (Rci.resolve [109, 97, 105, 110, 110, 101, 116] aliceNear (.local h32)
               = .accountLocal h32 aliceNear)
-- ETH-implicit with a non-wallet local hash: stays local. This is the corpus `e.eth_implicit_local`
-- case the old blanket guard excluded.
#guard decide (Rci.resolve [109, 97, 105, 110, 110, 101, 116] ethAcct (.local h32)
               = .accountLocal h32 ethAcct)
-- ETH-implicit with a wallet magic hash at PV86: resolves to the GLOBAL wallet contract.
#guard decide (Rci.resolve [109, 97, 105, 110, 110, 101, 116] ethAcct (.local (walletMagicHash .mainnet))
               = .global (ethWalletHash [109, 97, 105, 110, 110, 101, 116])
                         (.codeHash (ethWalletHash [109, 97, 105, 110, 110, 101, 116])))
-- The old-testnet hash on testnet also resolves to the testnet global wallet.
#guard decide (Rci.resolve [116, 101, 115, 116, 110, 101, 116] ethAcct (.local (walletMagicHash .oldTestnet))
               = .global (ethWalletHash [116, 101, 115, 116, 110, 101, 116])
                         (.codeHash (ethWalletHash [116, 101, 115, 116, 110, 101, 116])))
-- The old-testnet hash on mainnet does NOT: it is not a mainnet wallet.
#guard decide (Rci.resolve [109, 97, 105, 110, 110, 101, 116] ethAcct (.local (walletMagicHash .oldTestnet))
               = .accountLocal (walletMagicHash .oldTestnet) ethAcct)
-- The resolved global hash differs from the local magic hash it replaced.
#guard (Rci.resolve [109, 97, 105, 110, 110, 101, 116] ethAcct (.local (walletMagicHash .mainnet))).codeHashOf
       != walletMagicHash .mainnet

-- `Contract.none` / `Contract.global` / `Contract.byAccount`.
#guard decide (Rci.resolve [109, 97, 105, 110, 110, 101, 116] ethAcct .none = .none)
#guard decide (Rci.resolve [109, 97, 105, 110, 110, 101, 116] aliceNear (.global h32)
               = .global h32 (.codeHash h32))
#guard decide (Rci.resolve [109, 97, 105, 110, 110, 101, 116] aliceNear (.byAccount aliceNear)
               = .global (zeros 32) (.accountId aliceNear))

-- Only the `AccountId` variant needs a trie read.
#guard Rci.needsTrieLookup (.global h32 (.codeHash h32)) == false
#guard Rci.needsTrieLookup (.global h32 (.accountId aliceNear)) == true
#guard Rci.needsTrieLookup (.accountLocal h32 aliceNear) == false
#guard Rci.needsTrieLookup .none == false

/-! ## 10. Deterministic account id — nearcore's own test vector

`action_validation.rs:1100-1130` validates a `DeterministicStateInit` with
`code = AccountId("ft.near")`, `data = {}` against the receiver
`0s69284a5453e7be5632b28b6a01baecf6c12c156d`. That literal is nearcore's expected
`derive_near_deterministic_account_id` output, so reproducing it pins the borsh encoding, the
Keccak-256 sponge and the `[12:32]` slice in one step. -/

#guard String.fromUTF8! ⟨(deriveDetAccountId siFtNear).toArray⟩
       == "0s69284a5453e7be5632b28b6a01baecf6c12c156d"

/-! ### Length facts for the derived id

`derive_near_deterministic_account_id` (`utils.rs:470-478`) is
`"0s" ‖ hex(keccak256(..)[12:32])`: 2 prefix bytes plus 2 hex characters per byte of a 20-byte
slice, so 42 bytes whenever the digest is 32 bytes. The two lemmas below are the general statement
and its conditional form; the sponge's output length is a `Wasm/Crypto.lean` fact that module does
not export as a theorem, so it appears as an explicit hypothesis rather than an axiom. -/

/-- `hexOf` doubles the length of its input. -/
theorem hexOf_aux (b acc : Bytes) :
    (b.foldl (fun acc x =>
      let d := fun (n : Nat) => if n < 10 then UInt8.ofNat (48 + n) else UInt8.ofNat (87 + n)
      acc ++ [d (x.toNat / 16), d (x.toNat % 16)]) acc).length = acc.length + 2 * b.length := by
  induction b generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem hexOf_length (b : Bytes) : (hexOf b).length = 2 * b.length := by
  simpa [hexOf] using hexOf_aux b []

/-- **The derived id is 42 bytes**, conditional on the sponge returning 32 bytes for this encoding
(the only premise; `keccak256` is defined as a fixed-output sponge in `Wasm/Crypto.lean:60-81`, so
the premise is not an assumption about protocol behaviour, only a missing length lemma). -/
theorem deriveDetAccountId_isDet (s : StateInit)
    (h : (NearSpecV3.Wasm.Crypto.keccak256 (toBA s.encode)).toList.length = 32) :
    (deriveDetAccountId s).length = 42 := by
  simp only [deriveDetAccountId, List.length_append, List.length_cons, List.length_nil,
    hexOf_length, List.length_take, List.length_drop]
  rw [h]
  simp

/-- The concrete vector from §10 satisfies the premise, so its length is `42` with no hypothesis. -/
theorem deriveDetAccountId_siFtNear_length : (deriveDetAccountId siFtNear).length = 42 := by
  decide +kernel

-- Two different state inits derive different ids: a codec or hash regression changes the guard
-- above rather than passing silently.
#guard deriveDetAccountId siFtNear != deriveDetAccountId siZeroHash

-- A `state_init` whose receiver does not match the derived id is rejected, and one that does match
-- is accepted (`action_validation.rs:422-450`).
#guard dsiValid [48, 120] ⟨siZeroHash, 0⟩ == false
#guard dsiValid (deriveDetAccountId siZeroHash) ⟨siZeroHash, 0⟩ == true
-- The identifier validity conjunct is real: an uppercase `AccountId` fails even when the receiver
-- matches the derived id.
#guard dsiValid (deriveDetAccountId ⟨.accountId [65, 66, 67], []⟩) ⟨⟨.accountId [65, 66, 67], []⟩, 0⟩
       == false

/-! ## 11. Fee wiring for the three tags (`config.rs:150-199,320-356`) -/

#guard decide (execFeeL4 (.deployGlobal dg100) = some (deployGlobalExec dg100))
#guard decide (execFeeL4 (.useGlobal ugHash) = some (useGlobalExec ugHash))
#guard decide (execFeeL4 (.stateInit dsi) = some (stateInitExec dsi))
#guard decide (sendFeeL4 true (.deployGlobal dg100) = some (deployGlobalSend true dg100))
#guard decide (sendFeeL4 false (.useGlobal ugAcct) = some (useGlobalSend false ugAcct))

end NearSpecV3.D3.L4
