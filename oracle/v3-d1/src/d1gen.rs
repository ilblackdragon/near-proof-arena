//! Domain D1 chain generation (spec/near-chunk-validation-v0.md §6 D1,
//! spec/near-chunk-validation-d1.md): Transfer transactions of every validity class
//! inside real chunks of a real multi-shard nearcore TestEnv.
//!
//! Honest chunk producers never include an invalid transaction (prepare_transactions
//! re-verifies every pool transaction), so the invalid classes come from an
//! *adversarial chunk producer*: the client that produces the chunk of the chosen
//! shard at the next height processes the block without producing chunks, then
//! produces its chunks exactly as `Client::produce_chunks` does (client.rs:2093-2160:
//! `ChunkProducer::produce_chunk`, `send_chunk_state_witness_to_chunk_validators`,
//! `distribute_and_persist_encoded_chunk`), except that the chosen shard's chunk is
//! rebuilt (`ShardChunkWithEncoding::new`, sharding.rs:1427-1482, the same constructor
//! `produce_chunk` uses) with crafted transactions added to the pool transactions.
//! Everything downstream (inclusion in blocks, application of the chunk by every
//! node, the next chunk's state witness, its validation) is unmodified nearcore.
//! The witness that *applies* the crafted transactions is the next new chunk's witness
//! of that shard (its `transactions`); the crafted chunk's own witness carries them as
//! `new_transactions`.

use near_crypto::{InMemorySigner, KeyType, PublicKey, SecretKey, Signature, Signer};
use near_parameters::RuntimeConfig;
use near_primitives::account::{AccessKey, AccessKeyPermission, FunctionCallPermission, GasKeyInfo};
use near_primitives::action::{Action, AddKeyAction, TransferAction};
use near_primitives::bandwidth_scheduler::BandwidthRequests;
use near_primitives::hash::CryptoHash;
use near_primitives::merkle::merklize;
use near_primitives::sharding::{ShardChunkHeader, ShardChunkWithEncoding};
use near_primitives::state_record::StateRecord;
use near_primitives::transaction::{
    NonceMode, SignedTransaction, Transaction, TransactionNonce, TransactionV0, TransactionV1,
    ValidatedTransaction,
};
use near_primitives::types::{AccountId, Balance, ShardId};
use near_primitives::version::PROTOCOL_VERSION;
use near_client::Client;
use rand::Rng;
use rand::rngs::StdRng;
use reed_solomon_erasure::galois_8::ReedSolomon;
use std::collections::HashMap;
use std::sync::Arc;

/// Accounts per shard used by honest (pool) traffic in D1 mode: `s{k}a00..s{k}a04`.
/// Accounts `a05..a09` are reserved for crafted transactions, so the injector knows their
/// exact state when it crafts (no concurrent pool traffic touches them).
pub const HONEST_ACCTS: usize = 5;

pub fn fc_signer(a: &AccountId) -> Signer {
    InMemorySigner::from_seed(a.clone(), KeyType::ED25519, &format!("fc-{a}"))
}
pub fn gk_signer(a: &AccountId) -> Signer {
    InMemorySigner::from_seed(a.clone(), KeyType::ED25519, &format!("gk-{a}"))
}
pub fn secp_signer(a: &AccountId) -> Signer {
    InMemorySigner::from_seed(a.clone(), KeyType::SECP256K1, &format!("secp-{a}"))
}

/// Extra genesis access keys for D1 chains (per shard k):
///   a06: a GasKeyFullAccess key (2 nonces)          → V0 Transfer fails (InvalidNonceIndex)
///   a07: a FunctionCall key, unlimited allowance     → Transfer fails (RequiresFullAccess)
///   a08: a FunctionCall key, allowance 1 yoctoNEAR   → Transfer fails (NotEnoughAllowance)
///   a09: 14 extra full-access keys (storage usage > 770 bytes, so not a zero-balance account:
///        LackBalanceForState becomes reachable) and a SECP256K1 full-access key.
pub fn genesis_records(accounts: &[Vec<AccountId>]) -> Vec<StateRecord> {
    let mut r = Vec::new();
    for shard in accounts {
        let a6 = &shard[6];
        let gk = gk_signer(a6).public_key();
        r.push(StateRecord::access_key(
            a6.clone(),
            &gk,
            AccessKey {
                nonce: 0,
                permission: AccessKeyPermission::GasKeyFullAccess(GasKeyInfo {
                    balance: Balance::ZERO,
                    num_nonces: 2,
                }),
            },
        ));
        for i in 0..2u16 {
            r.push(StateRecord::gas_key_nonce(a6.clone(), &gk, i, 0));
        }
        for (j, allowance) in [(7usize, None), (8, Some(Balance::from_yoctonear(1)))] {
            let a = &shard[j];
            r.push(StateRecord::access_key(
                a.clone(),
                &fc_signer(a).public_key(),
                AccessKey {
                    nonce: 0,
                    permission: AccessKeyPermission::FunctionCall(FunctionCallPermission {
                        allowance,
                        receiver_id: shard[0].to_string(),
                        method_names: vec![],
                    }),
                },
            ));
        }
        let a9 = &shard[9];
        for i in 0..14 {
            let s = InMemorySigner::from_seed(a9.clone(), KeyType::ED25519, &format!("extra-{a9}-{i}"));
            r.push(StateRecord::access_key(a9.clone(), &s.public_key(), AccessKey::full_access()));
        }
        r.push(StateRecord::access_key(a9.clone(), &secp_signer(a9).public_key(), AccessKey::full_access()));
    }
    r
}

/// Mutable view of an account the injector crafts for (state after the previous block).
#[derive(Clone, Debug)]
pub struct AcctView {
    pub amount: u128,
    pub storage_usage: u64,
    pub ak_nonce: u64,
}

pub struct Ctx<'a> {
    pub accounts: &'a [Vec<AccountId>],
    pub k: usize,
    pub n_shards: usize,
    /// height of the block that will include the crafted chunk (= apply height of its txs)
    pub apply_height: u64,
    /// gas price the txs are charged at (`next_gas_price` of the chunk's prev block)
    pub gas_price: u128,
    pub tip_hash: CryptoHash,
    pub old_hash: CryptoHash,
    pub config: &'a RuntimeConfig,
    /// pre-state of reserved accounts (keyed by (account, full-access key))
    pub view: HashMap<AccountId, AcctView>,
}

fn v0(signer: &Signer, signer_id: &AccountId, receiver: &AccountId, nonce: u64, deposit: u128, bh: CryptoHash) -> Transaction {
    Transaction::V0(TransactionV0 {
        signer_id: signer_id.clone(),
        public_key: signer.public_key(),
        nonce,
        receiver_id: receiver.clone(),
        block_hash: bh,
        actions: vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(deposit) })],
    })
}

fn sign(tx: Transaction, signer: &Signer) -> SignedTransaction {
    let sig = signer.sign(tx.get_hash_and_size().0.as_ref());
    SignedTransaction::new(sig, tx)
}

fn ed_sig_bytes(s: &Signature) -> [u8; 64] {
    match s {
        Signature::ED25519(x) => x.to_bytes(),
        _ => panic!("not ed25519"),
    }
}

fn with_sig_bytes(tx: Transaction, b: [u8; 64]) -> SignedTransaction {
    SignedTransaction::new(Signature::ED25519(ed25519_dalek::Signature::from_bytes(&b)), tx)
}

/// ℓ = 2^252 + 27742317777372353535851937790883648493 (little-endian)
const ELL: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
];

fn add_le(a: &[u8], b: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut c = 0u16;
    for i in 0..32 {
        let s = a[i] as u16 + b[i] as u16 + c;
        out[i] = s as u8;
        c = s >> 8;
    }
    out
}

fn total_cost(cfg: &RuntimeConfig, tx: &Transaction, gas_price: u128) -> Option<u128> {
    node_runtime::config::tx_cost(cfg, tx, Balance::from_yoctonear(gas_price))
        .ok()
        .map(|c| c.total_cost.as_yoctonear())
}

/// Classes of crafted transactions. `ood_*` classes leave D1 (shape restrictions).
pub const CLASSES: &[&str] = &[
    "valid", "valid_self", "valid_zero_deposit", "valid_implicit_receiver", "valid_v1_monotonic",
    "valid_v1_strict", "bad_sig_flip_r", "bad_sig_flip_s", "bad_sig_wrong_msg", "bad_sig_s_plus_l",
    "bad_sig_wrong_key", "bad_sig_negated_r", "nonce_zero", "nonce_dup", "nonce_too_large",
    "v1_strict_gap", "insufficient_balance", "lack_storage", "cost_overflow", "missing_account",
    "foreign_signer", "missing_key", "fc_key_unlimited", "fc_key_allowance", "gas_key_v0",
    "expired_unknown_block", "expired_old_block", "dup_identical", "dup_bad_sig_first",
];
pub const OOD_CLASSES: &[&str] = &["ood_two_actions", "ood_secp256k1", "ood_add_key", "ood_gas_key_nonce"];

/// Craft `n` transactions (class label, tx) for shard `ctx.k`. Signers are the reserved
/// accounts a05..a09 of the shard (a05 for ordinary classes).
pub fn craft(rng: &mut StdRng, ctx: &mut Ctx, n: usize, p_ood: f64) -> Vec<(String, SignedTransaction)> {
    let mut out: Vec<(String, SignedTransaction)> = Vec::new();
    let accounts: &[Vec<AccountId>] = ctx.accounts;
    let n_shards = ctx.n_shards;
    let sh = &accounts[ctx.k];
    let a5 = sh[5].clone();
    let s5 = InMemorySigner::test_signer(&a5);
    let recv_named = |rng: &mut StdRng| -> AccountId {
        let ts = rng.gen_range(0..n_shards);
        accounts[ts][rng.gen_range(0..HONEST_ACCTS)].clone()
    };
    let mut classes: Vec<&str> = (0..n).map(|_| CLASSES[rng.gen_range(0..CLASSES.len())]).collect();
    if rng.gen_bool(p_ood) {
        classes.push(OOD_CLASSES[rng.gen_range(0..OOD_CLASSES.len())]);
    }
    let bh = ctx.tip_hash;
    for class in classes {
        let view5 = ctx.view.get(&a5).cloned().unwrap();
        let fresh = |ctx: &mut Ctx, a: &AccountId| -> u64 {
            let v = ctx.view.get_mut(a).unwrap();
            v.ak_nonce += 1;
            v.ak_nonce
        };
        let dep = rng.gen_range(1..10u128.pow(24));
        let txs: Vec<SignedTransaction> = match class {
            "valid" => {
                let r = recv_named(rng);
                let nn = fresh(ctx, &a5);
                vec![sign(v0(&s5, &a5, &r, nn, dep, bh), &s5)]
            }
            "valid_self" => {
                let nn = fresh(ctx, &a5);
                vec![sign(v0(&s5, &a5, &a5, nn, dep, bh), &s5)]
            }
            "valid_zero_deposit" => {
                let r = recv_named(rng);
                let nn = fresh(ctx, &a5);
                vec![sign(v0(&s5, &a5, &r, nn, 0, bh), &s5)]
            }
            "valid_implicit_receiver" => {
                let h: [u8; 32] = rng.r#gen();
                let r: AccountId = hex::encode(h).parse().unwrap();
                let nn = fresh(ctx, &a5);
                vec![sign(v0(&s5, &a5, &r, nn, dep, bh), &s5)]
            }
            "valid_v1_monotonic" | "valid_v1_strict" | "v1_strict_gap" => {
                let r = recv_named(rng);
                let mode = if class == "valid_v1_monotonic" { NonceMode::Monotonic } else { NonceMode::Strict };
                let nn = if class == "v1_strict_gap" {
                    view5.ak_nonce + 2
                } else {
                    fresh(ctx, &a5)
                };
                let tx = Transaction::V1(TransactionV1 {
                    signer_id: a5.clone(),
                    public_key: s5.public_key(),
                    nonce: TransactionNonce::from_nonce(nn),
                    receiver_id: r,
                    block_hash: bh,
                    actions: vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(dep) })],
                    nonce_mode: mode,
                });
                vec![sign(tx, &s5)]
            }
            "bad_sig_flip_r" | "bad_sig_flip_s" | "bad_sig_wrong_msg" | "bad_sig_s_plus_l"
            | "bad_sig_negated_r" => {
                let r = recv_named(rng);
                let tx = v0(&s5, &a5, &r, view5.ak_nonce + 1, dep, bh);
                let good = ed_sig_bytes(&s5.sign(tx.get_hash_and_size().0.as_ref()));
                let mut b = good;
                match class {
                    "bad_sig_flip_r" => b[rng.gen_range(0..32)] ^= 1 << rng.gen_range(0..8),
                    "bad_sig_flip_s" => b[32 + rng.gen_range(0..28)] ^= 1 << rng.gen_range(0..8),
                    "bad_sig_wrong_msg" => {
                        b = ed_sig_bytes(&s5.sign(CryptoHash::hash_bytes(&[rng.r#gen::<u8>()]).as_ref()))
                    }
                    "bad_sig_s_plus_l" => {
                        let s2 = add_le(&good[32..], &ELL);
                        if s2[31] & 0xe0 != 0 {
                            continue; // would not even decode (borsh check); skip this draw
                        }
                        b[32..].copy_from_slice(&s2);
                    }
                    _ => {
                        // non-canonical R: y + p (only possible when y < 19)… use a valid point with the
                        // sign bit flipped instead (R' = −R), which never verifies for an honest sig
                        b[31] ^= 0x80;
                    }
                }
                vec![with_sig_bytes(tx, b)]
            }
            "bad_sig_wrong_key" => {
                let r = recv_named(rng);
                let other = InMemorySigner::from_seed(a5.clone(), KeyType::ED25519, "other");
                let tx = v0(&s5, &a5, &r, view5.ak_nonce + 1, dep, bh);
                vec![SignedTransaction::new(other.sign(tx.get_hash_and_size().0.as_ref()), tx)]
            }
            "nonce_zero" => vec![sign(v0(&s5, &a5, &recv_named(rng), 0, dep, bh), &s5)],
            "nonce_dup" => {
                let nn = fresh(ctx, &a5);
                let r = recv_named(rng);
                vec![sign(v0(&s5, &a5, &r, nn, dep, bh), &s5), sign(v0(&s5, &a5, &r, nn, dep + 1, bh), &s5)]
            }
            "nonce_too_large" => {
                let nn = ctx.apply_height * near_primitives::account::AccessKey::ACCESS_KEY_NONCE_RANGE_MULTIPLIER
                    + rng.gen_range(0..3);
                vec![sign(v0(&s5, &a5, &recv_named(rng), nn, dep, bh), &s5)]
            }
            "insufficient_balance" => {
                let nn = view5.ak_nonce + 1;
                vec![sign(v0(&s5, &a5, &recv_named(rng), nn, view5.amount + 1, bh), &s5)]
            }
            "lack_storage" => {
                let a9 = sh[9].clone();
                let s9 = InMemorySigner::test_signer(&a9);
                let v9 = ctx.view.get(&a9).cloned().unwrap();
                let r = recv_named(rng);
                let probe = v0(&s9, &a9, &r, v9.ak_nonce + 1, 0, bh);
                let Some(gas_cost) = total_cost(ctx.config, &probe, ctx.gas_price) else { continue };
                let need = ctx.config.storage_amount_per_byte().as_yoctonear() * v9.storage_usage as u128;
                // leave half of the storage requirement: amount − cost < need, and ≥ 0
                let Some(d) = v9.amount.checked_sub(gas_cost + need / 2) else { continue };
                let nn = v9.ak_nonce + 1;
                vec![sign(v0(&s9, &a9, &r, nn, d, bh), &s9)]
            }
            "cost_overflow" => {
                let nn = view5.ak_nonce + 1;
                vec![sign(v0(&s5, &a5, &recv_named(rng), nn, u128::MAX - rng.gen_range(0..1000u128), bh), &s5)]
            }
            "missing_account" => {
                let ghost: AccountId = format!("{}ghost{}", ctx.accounts[ctx.k][0].as_str().split('a').next().unwrap(), rng.gen_range(0..1_000_000)).parse().unwrap();
                let s = InMemorySigner::test_signer(&ghost);
                vec![sign(v0(&s, &ghost, &recv_named(rng), 1, dep, bh), &s)]
            }
            "foreign_signer" => {
                let other_k = (ctx.k + 1 + rng.gen_range(0..ctx.n_shards.max(2) - 1)) % ctx.n_shards;
                let fa = ctx.accounts[other_k][5].clone();
                let fs = InMemorySigner::test_signer(&fa);
                vec![sign(v0(&fs, &fa, &recv_named(rng), 1 + rng.gen_range(0..1000), dep, bh), &fs)]
            }
            "missing_key" => {
                let s = InMemorySigner::from_seed(a5.clone(), KeyType::ED25519, &format!("nokey-{}", rng.r#gen::<u64>()));
                vec![sign(v0(&s, &a5, &recv_named(rng), view5.ak_nonce + 1, dep, bh), &s)]
            }
            "fc_key_unlimited" | "fc_key_allowance" => {
                let a = sh[if class == "fc_key_unlimited" { 7 } else { 8 }].clone();
                let s = fc_signer(&a);
                vec![sign(v0(&s, &a, &sh[0], 1 + rng.gen_range(0..1000), dep, bh), &s)]
            }
            "gas_key_v0" => {
                let a = sh[6].clone();
                let s = gk_signer(&a);
                vec![sign(v0(&s, &a, &recv_named(rng), 1 + rng.gen_range(0..1000), dep, bh), &s)]
            }
            "expired_unknown_block" => {
                let nn = view5.ak_nonce + 1;
                vec![sign(v0(&s5, &a5, &recv_named(rng), nn, dep, CryptoHash(rng.r#gen())), &s5)]
            }
            "expired_old_block" => {
                let nn = view5.ak_nonce + 1;
                vec![sign(v0(&s5, &a5, &recv_named(rng), nn, dep, ctx.old_hash), &s5)]
            }
            "dup_identical" => {
                let nn = fresh(ctx, &a5);
                let t = sign(v0(&s5, &a5, &recv_named(rng), nn, dep, bh), &s5);
                vec![t.clone(), t]
            }
            "dup_bad_sig_first" => {
                // same Transaction (same hash) twice: first with a corrupted signature, then the
                // valid one; UniqueChunkTransactions skips the second (lib.rs:2004-2012)
                let tx = v0(&s5, &a5, &recv_named(rng), view5.ak_nonce + 1, dep, bh);
                let good = ed_sig_bytes(&s5.sign(tx.get_hash_and_size().0.as_ref()));
                let mut bad = good;
                bad[0] ^= 1;
                vec![with_sig_bytes(tx.clone(), bad), with_sig_bytes(tx, good)]
            }
            "ood_two_actions" => {
                let nn = fresh(ctx, &a5);
                let mut tx = v0(&s5, &a5, &recv_named(rng), nn, dep, bh);
                if let Transaction::V0(t) = &mut tx {
                    t.actions.push(Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(1) }));
                }
                vec![sign(tx, &s5)]
            }
            "ood_secp256k1" => {
                let a9 = sh[9].clone();
                let s = secp_signer(&a9);
                vec![sign(v0(&s, &a9, &recv_named(rng), 1 + rng.gen_range(0..1000), dep, bh), &s)]
            }
            "ood_add_key" => {
                // signed by a key that does not exist: fails, but the action is not a Transfer
                let s = InMemorySigner::from_seed(a5.clone(), KeyType::ED25519, "nokey-addkey");
                let mut tx = v0(&s, &a5, &a5, 1, 0, bh);
                if let Transaction::V0(t) = &mut tx {
                    t.actions = vec![Action::AddKey(Box::new(AddKeyAction {
                        public_key: s.public_key(),
                        access_key: AccessKey::full_access(),
                    }))];
                }
                vec![sign(tx, &s)]
            }
            "ood_gas_key_nonce" => {
                let a = sh[6].clone();
                let s = gk_signer(&a);
                let tx = Transaction::V1(TransactionV1 {
                    signer_id: a.clone(),
                    public_key: s.public_key(),
                    nonce: TransactionNonce::from_nonce_and_index(1 + rng.gen_range(0..1000), 0),
                    receiver_id: recv_named(rng),
                    block_hash: bh,
                    actions: vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(dep) })],
                    nonce_mode: NonceMode::Monotonic,
                });
                vec![sign(tx, &s)]
            }
            _ => unreachable!(),
        };
        for t in txs {
            out.push((class.to_string(), t));
        }
    }
    let _ = PublicKey::empty;
    let _ = SecretKey::from_seed;
    out
}

/// `Client::produce_chunks` (client.rs:2093-2160) for one client and block, with the
/// chunk of `inject.0` rebuilt to carry the pool transactions plus `inject.1`
/// (inserted at random positions). Returns the hash of the rebuilt chunk, if any.
pub fn produce_chunks_with_injection(
    client: &mut Client,
    block: &near_chain::Block,
    inject: Option<(ShardId, Vec<SignedTransaction>)>,
    rng: &mut StdRng,
) -> Option<CryptoHash> {
    let signer = client.validator_signer.get().unwrap();
    let validator_id = signer.validator_id().clone();
    let epoch_id = client.epoch_manager.get_epoch_id_from_prev_block(block.header().hash()).unwrap();
    let mut rebuilt = None;
    for shard_id in client.epoch_manager.shard_ids(&epoch_id).unwrap() {
        let next_height = block.header().height() + 1;
        let last_header = client.epoch_manager.get_prev_chunk_header(block, shard_id).unwrap();
        let result = {
            let tvc = client.chain.transaction_validity_check(block.header().clone().into());
            client.chunk_producer.produce_chunk(
                block,
                &epoch_id,
                last_header.clone(),
                next_height,
                shard_id,
                &signer,
                &tvc,
                &|_| true,
            )
        };
        let near_client::ProduceChunkResult { chunk, encoded_chunk_parts_paths, receipts } = match result {
            Ok(Some(r)) => r,
            Ok(None) => continue,
            Err(e) => panic!("produce_chunk: {e:?}"),
        };
        let (chunk, paths) = match &inject {
            Some((s, extra)) if *s == shard_id => {
                let sc = chunk.to_shard_chunk();
                let header = sc.cloned_header();
                let mut txs: Vec<SignedTransaction> = sc.to_transactions().to_vec();
                for t in extra {
                    let pos = rng.gen_range(0..=txs.len());
                    txs.insert(pos, t.clone());
                }
                let tx_root = merklize(&txs).0;
                let total = client.epoch_manager.num_total_parts();
                let data = client.epoch_manager.num_data_parts();
                let rs = ReedSolomon::new(data, total - data).unwrap();
                let (c2, p2) = ShardChunkWithEncoding::new(
                    *header.prev_block_hash(),
                    header.prev_state_root(),
                    *header.prev_outcome_root(),
                    header.height_created(),
                    header.shard_id(),
                    header.prev_gas_used(),
                    header.gas_limit(),
                    header.prev_balance_burnt(),
                    header.prev_validator_proposals().collect(),
                    txs.into_iter().map(ValidatedTransaction::new_for_test).collect(),
                    sc.prev_outgoing_receipts().to_vec(),
                    *header.prev_outgoing_receipts_root(),
                    tx_root,
                    header.congestion_info(),
                    header.bandwidth_requests().cloned().unwrap_or_else(BandwidthRequests::empty),
                    header.proposed_split().cloned(),
                    &signer,
                    &rs,
                    PROTOCOL_VERSION,
                );
                rebuilt = Some(c2.to_shard_chunk().chunk_hash().0);
                (c2, p2)
            }
            _ => (chunk, encoded_chunk_parts_paths),
        };
        client
            .send_chunk_state_witness_to_chunk_validators(&epoch_id, block.header(), &last_header, chunk.to_shard_chunk())
            .expect("send witness");
        client
            .distribute_and_persist_encoded_chunk(chunk, paths, receipts, validator_id.clone())
            .expect("distribute chunk");
    }
    let _ = ShardChunkHeader::is_genesis;
    let _: Option<Arc<()>> = None;
    rebuilt
}
