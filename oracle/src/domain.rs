//! Slice domain predicate, re-implemented in Rust *without* nearcore runtime
//! code (only nearcore data types). Mirrors `NearSpec.TransferV1.Domain`.
//! Used by the generator (to keep valid cases in-domain and invalid cases
//! out) and recorded in diagnostics; nearcore's observed behaviour is checked
//! against it separately.

use near_primitives::account::id::AccountType;
use near_primitives::receipt::{Receipt, ReceiptEnum};
use near_primitives::transaction::Action;
use near_crypto::PublicKey;
use std::collections::{BTreeMap, HashSet};

use crate::enc::Request;

pub const PROTOCOL_VERSION: u32 = 86;
pub const CHAIN_ID: &str = "mainnet";
/// exec(new_action_receipt) + exec(transfer, named receiver), PV86 mainnet params.
pub const GAS_PER_TRANSFER: u64 = 108_059_500_000 + 115_123_062_500;
pub const MAX_BATCH: usize = 256;
pub const MAX_WITNESS_BYTES: usize = 3_000_000;
pub const STORAGE_AMOUNT_PER_BYTE: u128 = 10_000_000_000_000_000_000;
pub const ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT: u64 = 770;

pub fn account_key(id: &str) -> Vec<u8> {
    let mut k = vec![0u8];
    k.extend_from_slice(id.as_bytes());
    k
}

/// Static (state-independent) per-receipt shape check.
pub fn receipt_shape(r: &Receipt) -> Result<(), String> {
    let Receipt::V0(v0) = r;
    let ReceiptEnum::Action(a) = &v0.receipt else {
        return Err("receipt is not ReceiptEnum::Action".into());
    };
    if a.actions.len() != 1 {
        return Err(format!("{} actions (need exactly 1)", a.actions.len()));
    }
    if !matches!(a.actions[0], Action::Transfer(_)) {
        return Err("action is not Transfer".into());
    }
    if !a.input_data_ids.is_empty() || !a.output_data_receivers.is_empty() {
        return Err("input_data_ids/output_data_receivers not empty".into());
    }
    if v0.predecessor_id.is_system() {
        return Err("predecessor is system (refund receipt input)".into());
    }
    if v0.receiver_id.get_account_type() != AccountType::NamedAccount {
        return Err(format!("receiver {} is not a NamedAccount", v0.receiver_id));
    }
    match &a.signer_public_key {
        PublicKey::ED25519(_) | PublicKey::SECP256K1(_) => {}
        _ => return Err("signer key type not ED25519/SECP256K1".into()),
    }
    Ok(())
}

pub struct Sim {
    pub tokens_burnt_total: u128,
    pub refunds: usize,
}

/// Full domain check: static request checks + sequential simulation on the
/// pre-state key/value map.
pub fn check(
    req: &Request,
    kv: &BTreeMap<Vec<u8>, Vec<u8>>,
    witness_bytes: usize,
) -> Result<Sim, String> {
    if req.protocol_version != PROTOCOL_VERSION {
        return Err("protocol_version != 86".into());
    }
    if req.chain_id != CHAIN_ID {
        return Err("chain_id != mainnet".into());
    }
    let n = req.receipts.len();
    if n == 0 || n > MAX_BATCH {
        return Err(format!("batch size {n} not in 1..={MAX_BATCH}"));
    }
    if (n as u128 - 1) * GAS_PER_TRANSFER as u128 >= req.gas_limit as u128 {
        return Err("compute limit reached before last receipt ((n-1)*G >= gas_limit)".into());
    }
    if witness_bytes > MAX_WITNESS_BYTES {
        return Err("slice witness too large".into());
    }
    let mut ids = HashSet::new();
    for r in &req.receipts {
        receipt_shape(r)?;
        if !ids.insert(*r.receipt_id()) {
            return Err("duplicate receipt id".into());
        }
    }
    let g = GAS_PER_TRANSFER as u128;
    let mut kv = kv.clone();
    let mut total: u128 = 0;
    let mut refunds = 0;
    for r in &req.receipts {
        let Receipt::V0(v0) = r;
        let ReceiptEnum::Action(a) = &v0.receipt else { unreachable!() };
        let Action::Transfer(t) = &a.actions[0] else { unreachable!() };
        let key = account_key(v0.receiver_id.as_str());
        let Some(val) = kv.get(&key) else {
            return Err(format!("receiver {} does not exist", v0.receiver_id));
        };
        if val.len() != 72 {
            return Err("receiver account value is not 72 bytes (AccountV1)".into());
        }
        let amount = u128::from_le_bytes(val[0..16].try_into().unwrap());
        let locked = u128::from_le_bytes(val[16..32].try_into().unwrap());
        let su = u64::from_le_bytes(val[64..72].try_into().unwrap());
        if amount == u128::MAX {
            return Err("receiver account uses the V2 sentinel".into());
        }
        let deposit = t.deposit.as_yoctonear();
        let new_amount = amount.checked_add(deposit).ok_or("balance overflow")?;
        if new_amount == u128::MAX {
            return Err("new balance equals the V2 sentinel u128::MAX".into());
        }
        let avail = new_amount.checked_add(locked).ok_or("amount+locked overflow")?;
        if !(avail >= STORAGE_AMOUNT_PER_BYTE * su as u128 || su <= ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT) {
            return Err("storage stake not covered after transfer".into());
        }
        let pr = a.gas_price.as_yoctonear();
        let pb = req.block_gas_price;
        let p = pr.min(pb);
        let burnt = p.checked_mul(g).ok_or("tokens_burnt overflow")?;
        let surplus = (pr - p).checked_mul(g).ok_or("refund overflow")?;
        if surplus > 0 {
            refunds += 1;
        }
        total = total.checked_add(burnt).ok_or("tokens_burnt_total overflow")?;
        let mut nv = val.clone();
        nv[0..16].copy_from_slice(&new_amount.to_le_bytes());
        kv.insert(key, nv);
    }
    Ok(Sim { tokens_burnt_total: total, refunds })
}
