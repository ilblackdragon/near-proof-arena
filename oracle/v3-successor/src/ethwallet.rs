//! `eth-wallet` scenario helpers (row L0-D3-006): ETH-implicit accounts holding a legacy wallet
//! magic hash, and the Ethereum transactions their wallet contract (`rlp_execute`) accepts.
//!
//! Pre-PV83, an ETH-implicit account created by a transfer got the contract code
//! `"near" ‖ base58(sha256(wallet wasm))` (the *magic bytes*) and the code hash `sha256` of those
//! bytes (`runtime/runtime/src/actions.rs:251-270`, `else` branch). From PV83 nearcore resolves any
//! such account to the chain's global wallet (`contract_code.rs:56-76`). A PV86 chain only gets
//! such accounts from genesis, so the scenario writes them as genesis records, exactly as the old
//! code wrote them (account + `Contract` record with the magic bytes, no access key).
//!
//! The Ethereum side follows nearcore's own test (`integration-tests/src/tests/features/
//! wallet_contract.rs`, `create_rlp_execute_tx`/`sign_eth_transaction`/`abi_encode`): an EIP-2930
//! transaction (`0x01 ‖ rlp([...])`) with EVM chain id 399 (the localnet wallet build,
//! `near-wallet-contract/build.rs`), signed with near-crypto's recoverable secp256k1 signature
//! over `keccak256(0x01 ‖ rlp(unsigned))`. RLP and the ABI words are encoded here (the crates
//! nearcore's test uses are dev-dependencies outside this crate's lock).

use near_crypto::{KeyType, SecretKey};
use near_primitives::types::AccountId;
use sha3::{Digest, Keccak256};

/// The EVM chain id compiled into `wallet_contract_localnet.wasm` (`build.rs` `LOCALNET_CHAIN_ID`).
pub const EVM_CHAIN_ID: u64 = 399;
/// Selectors of `near-wallet-contract/implementation/wallet-contract/src/types.rs`.
const FUNCTION_CALL_SELECTOR: [u8; 4] = [0x61, 0x79, 0xb7, 0x07];
const TRANSFER_SELECTOR: [u8; 4] = [0x3e, 0xd6, 0x41, 0x24];

static LOCALNET_WASM: &[u8] = include_bytes!("../../vendor/nearcore/runtime/near-wallet-contract/res/wallet_contract_localnet.wasm");
static MAINNET_WASM: &[u8] = include_bytes!("../../vendor/nearcore/runtime/near-wallet-contract/res/wallet_contract_mainnet.wasm");
static TESTNET_WASM: &[u8] = include_bytes!("../../vendor/nearcore/runtime/near-wallet-contract/res/wallet_contract_testnet.wasm");
static OLD_TESTNET_WASM: &[u8] = include_bytes!("../../vendor/nearcore/runtime/near-wallet-contract/res/wallet_contract_testnet_pv70.wasm");

/// The code the chain's global wallet is deployed with (`eth_wallet_global_contract_hash` of a
/// non-mainnet, non-testnet chain is `sha256` of this blob).
pub fn localnet_wallet() -> &'static [u8] {
    LOCALNET_WASM
}

/// The four legacy variants nearcore's `LegacyEthWallet::resolve` knows.
pub const VARIANTS: [&str; 4] = ["mainnet", "testnet", "oldtestnet", "localnet"];

fn variant_wasm(v: &str) -> &'static [u8] {
    match v {
        "mainnet" => MAINNET_WASM,
        "testnet" => TESTNET_WASM,
        "oldtestnet" => OLD_TESTNET_WASM,
        "localnet" => LOCALNET_WASM,
        _ => panic!("unknown wallet variant {v}"),
    }
}

/// `WalletContract::magic_bytes` (`near-wallet-contract/src/lib.rs`): `"near" ‖ Display(sha256(wasm))`.
pub fn magic_bytes(v: &str) -> Vec<u8> {
    let h = near_primitives::hash::CryptoHash::hash_bytes(variant_wasm(v));
    format!("near{h}").into_bytes()
}

/// The secp256k1 key of a scenario ETH-implicit account.
pub fn eth_key(tag: &str) -> SecretKey {
    SecretKey::from_seed(KeyType::SECP256K1, &format!("ethwallet-{tag}"))
}

/// `derive_eth_implicit_account_id` of the key.
pub fn eth_account(tag: &str) -> AccountId {
    near_primitives::utils::derive_eth_implicit_account_id(eth_key(tag).public_key().unwrap_as_secp256k1())
}

fn keccak(b: &[u8]) -> [u8; 32] {
    Keccak256::digest(b).into()
}

/// The 20-byte address the wallet compares `to` with: the hex of an ETH-implicit id, else
/// `keccak256(account id)[12..]` (`internal.rs` `account_id_to_address`).
fn address_of(a: &AccountId) -> Vec<u8> {
    let s = a.as_str();
    if s.len() == 42 && s.starts_with("0x") {
        return hex::decode(&s[2..]).unwrap();
    }
    keccak(s.as_bytes())[12..].to_vec()
}

// ------------------------------------------------------------------------------------- RLP

fn rlp_len(prefix_short: u8, prefix_long: u8, len: usize) -> Vec<u8> {
    if len < 56 {
        vec![prefix_short + len as u8]
    } else {
        let be = be_min(len as u128);
        let mut v = vec![prefix_long + be.len() as u8];
        v.extend(be);
        v
    }
}
fn be_min(x: u128) -> Vec<u8> {
    let b = x.to_be_bytes();
    let i = b.iter().position(|&c| c != 0).unwrap_or(16);
    b[i..].to_vec()
}
fn rlp_bytes(b: &[u8]) -> Vec<u8> {
    if b.len() == 1 && b[0] < 0x80 {
        return b.to_vec();
    }
    let mut v = rlp_len(0x80, 0xb7, b.len());
    v.extend_from_slice(b);
    v
}
fn rlp_uint(x: u128) -> Vec<u8> {
    rlp_bytes(&be_min(x))
}
/// A big-endian 256-bit unsigned value with leading zeros stripped.
fn rlp_u256(b: &[u8; 32]) -> Vec<u8> {
    let i = b.iter().position(|&c| c != 0).unwrap_or(32);
    rlp_bytes(&b[i..])
}
fn rlp_list(items: &[Vec<u8>]) -> Vec<u8> {
    let body: Vec<u8> = items.concat();
    let mut v = rlp_len(0xc0, 0xf7, body.len());
    v.extend(body);
    v
}

// ------------------------------------------------------------------------------------- ABI

/// A Solidity ABI argument: a static unsigned word or a dynamic byte string.
pub enum Abi {
    Uint(u128),
    Dyn(Vec<u8>),
}
fn word(x: u128) -> Vec<u8> {
    let mut w = vec![0u8; 16];
    w.extend(x.to_be_bytes());
    w
}
fn abi(selector: [u8; 4], args: &[Abi]) -> Vec<u8> {
    let mut head = Vec::new();
    let mut tail = Vec::new();
    let head_len = 32 * args.len();
    for a in args {
        match a {
            Abi::Uint(x) => head.extend(word(*x)),
            Abi::Dyn(b) => {
                head.extend(word((head_len + tail.len()) as u128));
                tail.extend(word(b.len() as u128));
                tail.extend_from_slice(b);
                tail.resize(tail.len() + (32 - b.len() % 32) % 32, 0);
            }
        }
    }
    let mut v = selector.to_vec();
    v.extend(head);
    v.extend(tail);
    v
}

/// What the Ethereum transaction asks the wallet to do.
pub enum EthOp {
    /// `transfer(receiver_id, yocto_near)` with `value` wei (1 wei = 10^6 yocto).
    Transfer { receiver: AccountId, wei: u128, yocto: u32 },
    /// `functionCall(receiver_id, method_name, args, gas, yocto_near)`.
    FunctionCall { receiver: AccountId, method: String, args: Vec<u8>, gas: u64, wei: u128 },
    /// No call data: an Ethereum base-token transfer to `receiver` (an EOA transfer).
    Plain { receiver: AccountId, wei: u128 },
}

/// The `rlp_execute` JSON arguments for `op`, signed by the wallet `tag`'s key (or by `signer_tag`
/// to produce a signature of the wrong sender) with EVM chain id `chain_id` and the given nonce.
pub fn rlp_execute_args(tag: &str, signer_tag: &str, op: &EthOp, nonce: u64, chain_id: u64) -> Vec<u8> {
    let _ = tag;
    let (target, data, wei) = match op {
        EthOp::Transfer { receiver, wei, yocto } => (
            receiver.clone(),
            abi(TRANSFER_SELECTOR, &[Abi::Dyn(receiver.as_bytes().to_vec()), Abi::Uint(*yocto as u128)]),
            *wei,
        ),
        EthOp::FunctionCall { receiver, method, args, gas, wei } => (
            receiver.clone(),
            abi(FUNCTION_CALL_SELECTOR, &[
                Abi::Dyn(receiver.as_bytes().to_vec()),
                Abi::Dyn(method.as_bytes().to_vec()),
                Abi::Dyn(args.clone()),
                Abi::Uint(*gas as u128),
                Abi::Uint(0),
            ]),
            *wei,
        ),
        EthOp::Plain { receiver, wei } => (receiver.clone(), vec![], *wei),
    };
    // EIP-2930: [chainId, nonce, gasPrice, gasLimit, to, value, data, accessList]
    let unsigned = vec![
        rlp_uint(chain_id as u128),
        rlp_uint(nonce as u128),
        rlp_uint(0),
        rlp_uint(0),
        rlp_bytes(&address_of(&target)),
        rlp_uint(wei),
        rlp_bytes(&data),
        rlp_list(&[]),
    ];
    let mut pre = vec![0x01u8];
    pre.extend(rlp_list(&unsigned));
    let sig = match eth_key(signer_tag).sign(&keccak(&pre)) {
        near_crypto::Signature::SECP256K1(s) => {
            let b: [u8; 65] = s.into();
            b
        }
        _ => unreachable!(),
    };
    let r: [u8; 32] = sig[0..32].try_into().unwrap();
    let s: [u8; 32] = sig[32..64].try_into().unwrap();
    let mut signed = unsigned;
    signed.push(rlp_uint(sig[64] as u128));
    signed.push(rlp_u256(&r));
    signed.push(rlp_u256(&s));
    let mut tx = vec![0x01u8];
    tx.extend(rlp_list(&signed));
    let b64 = near_primitives::serialize::to_base64(&tx);
    format!(r#"{{"target":"{target}","tx_bytes_b64":"{b64}"}}"#).into_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rlp_vectors() {
        // Ethereum wiki RLP vectors
        assert_eq!(rlp_bytes(b"dog"), vec![0x83, b'd', b'o', b'g']);
        assert_eq!(rlp_uint(0), vec![0x80]);
        assert_eq!(rlp_uint(15), vec![0x0f]);
        assert_eq!(rlp_uint(1024), vec![0x82, 0x04, 0x00]);
        assert_eq!(rlp_list(&[]), vec![0xc0]);
        assert_eq!(rlp_list(&[rlp_bytes(b"cat"), rlp_bytes(b"dog")]),
                   vec![0xc8, 0x83, b'c', b'a', b't', 0x83, b'd', b'o', b'g']);
    }
    #[test]
    fn magic_hashes_match_nearcore() {
        for v in VARIANTS {
            let h = near_primitives::hash::CryptoHash::hash_bytes(&magic_bytes(v));
            assert!(near_wallet_contract::wallet_contract(h).is_some(), "{v}");
        }
    }
}
