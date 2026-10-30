//! Opt-in key-family and gas-key scenario (`NEAR_SUCCESSOR_SCENARIO=keys`).
//!
//! Dedicated genesis accounts (never touched by the baseline workload) run labelled steps:
//! secp256k1 transaction keys (valid, recovery-id/high-s/bit-flip/stale-nonce/type-mismatch
//! signatures, AddKey/DeleteKey, off-curve keys), delegate actions whose inner signer key is
//! secp256k1, ML-DSA-65 keys in key-storage positions plus one ML-DSA-signed transaction, and gas
//! keys (AddKey, TransferToGasKey, WithdrawFromGasKey, nonce-index transactions, deletion with
//! balance, the three gas-key promise host functions). A step is submitted either through the
//! transaction pool (`Pool`, nearcore admits it first) or injected into the next chunk of the
//! account's shard (`Inject`, for transactions the pool refuses). Labels are
//! `successor.keys.NN.name`; a label says what was submitted, never what nearcore did with it.
//!
//! `NEAR_SUCCESSOR_SCENARIO=mldsa` runs a second step table (`step_mldsa`, labels
//! `successor.mldsa.NN.name`) on the same accounts plus three: ML-DSA-65-signed transactions
//! (valid, every malformed-signature class, type mismatches, nonces), ML-DSA keys added and then
//! used, an FC call reading `signer_account_pk`, ML-DSA gas keys and delegates, and balance /
//! gas-key-balance boundaries at exactly the `ml_dsa_65_verification_cost` term. With `keys` the
//! behaviour is unchanged.
use crate::chaingen::Setup;
use crate::d2gen::{view_gk_nonce, view_key};
use near_crypto::{InMemorySigner, KeyType, PublicKey, Secp256K1PublicKey, Secp256K1Signature, Signature, Signer};
use near_primitives::account::{AccessKey, AccessKeyPermission, AccountContract, FunctionCallPermission, GasKeyInfo};
use near_primitives::action::delegate::{
    DelegateAction, DelegateActionV2, NonDelegateAction, SignedDelegateAction, VersionedDelegateActionPayload,
    VersionedSignedDelegateAction,
};
use near_primitives::action::{
    Action, AddKeyAction, DeleteKeyAction, FunctionCallAction, TransferAction, TransferToGasKeyAction,
    WithdrawFromGasKeyAction,
};
use near_primitives::hash::CryptoHash;
use near_primitives::state_record::StateRecord;
use near_primitives::transaction::{NonceMode, SignedTransaction, Transaction, TransactionNonce, TransactionV0, TransactionV1};
use near_primitives::types::{AccountId, Balance, Gas};
use near_primitives_core::account::Account;
use std::collections::{HashMap, VecDeque};

mod mldsa;
use mldsa::N_STEPS_MLDSA;

pub const SCENARIO: &str = "keys";
pub const SCENARIO_MLDSA: &str = "mldsa";
pub const LABEL_PREFIX: &str = "successor.keys.";
pub const LABEL_PREFIX_MLDSA: &str = "successor.mldsa.";
/// Blocks between steps (receipt delivery across shards and the next chunk of every shard).
const GAP: u64 = 4;
const FIRST_HEIGHT: u64 = 10004;

pub fn enabled() -> bool {
    std::env::var("NEAR_SUCCESSOR_SCENARIO").as_deref() == Ok(SCENARIO) || mldsa_mode()
}
/// The `mldsa` step table instead of the `keys` one (same accounts, same driver).
pub fn mldsa_mode() -> bool {
    std::env::var("NEAR_SUCCESSOR_SCENARIO").as_deref() == Ok(SCENARIO_MLDSA)
}
/// `mldsa` with `NEAR_MLDSA_BOUND_SIGNER` set (item 10: the `z`-bound steps).
pub fn mldsa_bound_mode() -> bool {
    mldsa_mode() && mldsa::bound_signer().is_some()
}
fn label_prefix() -> &'static str {
    if mldsa_mode() { LABEL_PREFIX_MLDSA } else { LABEL_PREFIX }
}
fn n_steps() -> usize {
    if mldsa_mode() { N_STEPS_MLDSA + if mldsa::bound_signer().is_some() { mldsa::N_STEPS_MLDSA_BOUND } else { 0 } } else { N_STEPS }
}

fn acct(s: &str) -> AccountId {
    s.parse().unwrap()
}
pub fn a_secp() -> AccountId {
    acct("s0ksecp")
}
pub fn a_deleg() -> AccountId {
    acct("s1kdeleg")
}
pub fn a_relay() -> AccountId {
    acct("s1krelay")
}
pub fn a_mldsa() -> AccountId {
    acct("s2kmldsa")
}
pub fn a_gas() -> AccountId {
    acct("s3kgas")
}
pub fn a_host() -> AccountId {
    acct("s3kgashost")
}
fn sk(a: &AccountId, tag: &str, kt: KeyType) -> Signer {
    InMemorySigner::from_seed(a.clone(), kt, &format!("keys-{tag}-{a}"))
}
fn ed(a: &AccountId) -> Signer {
    InMemorySigner::test_signer(a)
}

/// The gas-key host contract (contracts/kgashost.wat), assembled deterministically.
pub fn host_code() -> Vec<u8> {
    wat::parse_str(include_str!("../contracts/kgashost.wat")).expect("kgashost.wat")
}

/// Genesis records of the scenario accounts. Each has 1,000,000 NEAR and its ED25519 test key.
pub fn genesis_records() -> (Vec<StateRecord>, Balance) {
    let mut r = Vec::new();
    let mut supply = Balance::ZERO;
    let host = host_code();
    for a in [a_secp(), a_deleg(), a_relay(), a_mldsa(), a_gas(), a_host()] {
        let amount = Balance::from_near(1_000_000);
        let contract = if a == a_host() { AccountContract::Local(CryptoHash::hash_bytes(&host)) } else { AccountContract::None };
        r.push(StateRecord::Account { account_id: a.clone(), account: Account::new(amount, Balance::ZERO, contract, 0) });
        r.push(StateRecord::access_key(a.clone(), &ed(&a).public_key(), AccessKey::full_access()));
        supply = supply.checked_add(amount).unwrap();
    }
    r.push(StateRecord::Contract { account_id: a_host(), code: host });
    r.push(StateRecord::access_key(a_secp(), &sk(&a_secp(), "main", KeyType::SECP256K1).public_key(), AccessKey::full_access()));
    r.push(StateRecord::access_key(a_deleg(), &sk(&a_deleg(), "main", KeyType::SECP256K1).public_key(), AccessKey::full_access()));
    r.push(StateRecord::access_key(a_mldsa(), &sk(&a_mldsa(), "main", KeyType::MLDSA65).public_key(), AccessKey::full_access()));
    if mldsa_mode() {
        // ML-DSA keys for the delegate sender and the relayer; a poor account (1 NEAR) for the
        // balance boundary; the `kmlpk` contract account
        r.push(StateRecord::access_key(a_deleg(), &sk(&a_deleg(), "main", KeyType::MLDSA65).public_key(), AccessKey::full_access()));
        r.push(StateRecord::access_key(a_relay(), &sk(&a_relay(), "main", KeyType::MLDSA65).public_key(), AccessKey::full_access()));
        let code = mlpk_code();
        for (a, amount, contract) in [
            (a_poor(), Balance::from_near(1), AccountContract::None),
            (a_mlpk(), Balance::from_near(1_000_000), AccountContract::Local(CryptoHash::hash_bytes(&code))),
        ] {
            r.push(StateRecord::Account { account_id: a.clone(), account: Account::new(amount, Balance::ZERO, contract, 0) });
            r.push(StateRecord::access_key(a.clone(), &ed(&a).public_key(), AccessKey::full_access()));
            supply = supply.checked_add(amount).unwrap();
        }
        r.push(StateRecord::access_key(a_poor(), &sk(&a_poor(), "main", KeyType::MLDSA65).public_key(), AccessKey::full_access()));
        r.push(StateRecord::Contract { account_id: a_mlpk(), code });
    }
    (r, supply)
}

pub fn a_poor() -> AccountId {
    acct("s2kmlpoor")
}
pub fn a_mlpk() -> AccountId {
    acct("s2kmlpk")
}
/// `kmlpk` (mldsa scenario only): method `pk` returns `signer_account_pk` (the Borsh signer key,
/// 1,953 bytes for an ML-DSA-65 signer).
pub fn mlpk_code() -> Vec<u8> {
    wat::parse_str(
        r#"(module
  (import "env" "signer_account_pk" (func $spk (param i64)))
  (import "env" "register_len" (func $rlen (param i64) (result i64)))
  (import "env" "read_register" (func $rr (param i64 i64)))
  (import "env" "value_return" (func $vr (param i64 i64)))
  (memory 1)
  (func $pk (call $spk (i64.const 0)) (call $rr (i64.const 0) (i64.const 0))
    (call $vr (call $rlen (i64.const 0)) (i64.const 0)))
  (export "pk" (func $pk)))"#,
    )
    .expect("kmlpk")
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Mode {
    Pool,
    Inject,
}

pub struct KeysWorld {
    next_step: usize,
    next_height: u64,
    /// heights a step has waited for its prerequisite state (a key added by an earlier step)
    waited: u64,
    used: HashMap<(AccountId, PublicKey, Option<u16>), u64>,
    /// injected steps waiting for the producer of their shard: (shard index, labelled txs)
    pending: VecDeque<(usize, Vec<(String, SignedTransaction)>)>,
}

/// secp256k1 group order n, big-endian.
const SECP_N: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6,
    0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41,
];

fn secp_bytes(sig: &Signature) -> [u8; 65] {
    match sig {
        Signature::SECP256K1(s) => <[u8; 65]>::from(s.clone()),
        _ => panic!("not a secp256k1 signature"),
    }
}
fn secp_sig(b: [u8; 65]) -> Signature {
    Signature::SECP256K1(Secp256K1Signature::from(b))
}

/// Signature edits applied to a valid secp256k1 signature.
#[derive(Clone, Copy, Debug)]
enum SecpEdit {
    /// recovery id XOR 1 (nearcore's `Signature::verify` never uses the recovery id's key)
    RecIdFlip,
    /// recovery id 4: `RecoveryId::from_i32` fails
    RecId4,
    /// one bit of r flipped
    BitFlip,
    /// s := n - s (the high-s twin; libsecp256k1 verification requires low s)
    HighS,
}

fn edit_secp(sig: &Signature, e: SecpEdit) -> Signature {
    let mut b = secp_bytes(sig);
    match e {
        SecpEdit::RecIdFlip => b[64] ^= 1,
        SecpEdit::RecId4 => b[64] = 4,
        SecpEdit::BitFlip => b[5] ^= 0x10,
        SecpEdit::HighS => {
            // n - s, 256-bit big-endian subtraction (s < n for a valid signature)
            let mut borrow = 0i16;
            for i in (0..32).rev() {
                let d = SECP_N[i] as i16 - b[32 + i] as i16 - borrow;
                borrow = if d < 0 { 1 } else { 0 };
                b[32 + i] = (d + 256 * borrow) as u8;
            }
            b[64] ^= 1;
        }
    }
    secp_sig(b)
}

fn edit_ed(sig: &Signature) -> Signature {
    match sig {
        Signature::ED25519(x) => {
            let mut b = x.to_bytes();
            b[40] ^= 0x04;
            Signature::ED25519(ed25519_dalek::Signature::from_bytes(&b))
        }
        _ => panic!("not an ed25519 signature"),
    }
}

fn tr(d: u128) -> Action {
    Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(d) })
}
fn add_key(pk: PublicKey, perm: AccessKeyPermission) -> Action {
    Action::AddKey(Box::new(AddKeyAction { public_key: pk, access_key: AccessKey { nonce: 0, permission: perm } }))
}
fn del_key(pk: PublicKey) -> Action {
    Action::DeleteKey(Box::new(DeleteKeyAction { public_key: pk }))
}
fn fc(method: &str, args: Vec<u8>, tgas: u64) -> Action {
    Action::FunctionCall(Box::new(FunctionCallAction { method_name: method.into(), args, gas: Gas::from_teragas(tgas), deposit: Balance::ZERO }))
}
fn gas_full(n: u16) -> AccessKeyPermission {
    AccessKeyPermission::GasKeyFullAccess(GasKeyInfo { balance: Balance::ZERO, num_nonces: n })
}
fn fc_perm(receiver: &AccountId) -> FunctionCallPermission {
    FunctionCallPermission { allowance: None, receiver_id: receiver.to_string(), method_names: vec![] }
}
const NEAR: u128 = 10u128.pow(24);

fn v0_unsigned(pk: PublicKey, signer_id: &AccountId, receiver: &AccountId, nonce: u64, actions: Vec<Action>, bh: CryptoHash) -> Transaction {
    Transaction::V0(TransactionV0 { signer_id: signer_id.clone(), public_key: pk, nonce, receiver_id: receiver.clone(), block_hash: bh, actions })
}
fn v1_unsigned(pk: PublicKey, signer_id: &AccountId, receiver: &AccountId, nonce: TransactionNonce, mode: NonceMode, actions: Vec<Action>, bh: CryptoHash) -> Transaction {
    Transaction::V1(TransactionV1 { signer_id: signer_id.clone(), public_key: pk, nonce, receiver_id: receiver.clone(), block_hash: bh, actions, nonce_mode: mode })
}
fn sign(tx: Transaction, s: &Signer) -> SignedTransaction {
    let sig = s.sign(tx.get_hash_and_size().0.as_ref());
    SignedTransaction::new(sig, tx)
}
fn with_sig(tx: Transaction, sig: Signature) -> SignedTransaction {
    SignedTransaction::new(sig, tx)
}

impl KeysWorld {
    pub fn new() -> Self {
        Self { next_step: 0, next_height: FIRST_HEIGHT, waited: 0, used: HashMap::new(), pending: VecDeque::new() }
    }

    fn cur(&self, s: &Setup, bh: &CryptoHash, a: &AccountId, pk: &PublicKey, idx: Option<u16>) -> Option<u64> {
        match idx {
            None => view_key(s, bh, a, pk).map(|k| k.nonce),
            Some(i) => view_gk_nonce(s, bh, a, pk, i),
        }
    }
    /// The next valid nonce: above both the tip state and every nonce this scenario submitted.
    fn next(&mut self, s: &Setup, bh: &CryptoHash, a: &AccountId, pk: &PublicKey, idx: Option<u16>) -> Option<u64> {
        let cur = self.cur(s, bh, a, pk, idx)?;
        let key = (a.clone(), pk.clone(), idx);
        let n = cur.max(self.used.get(&key).copied().unwrap_or(0)) + 1;
        self.used.insert(key, n);
        Some(n)
    }
    /// A plain transaction signed with the account's ED25519 test key.
    fn ed_tx(&mut self, s: &Setup, bh: &CryptoHash, a: &AccountId, r: &AccountId, actions: Vec<Action>) -> Option<SignedTransaction> {
        let k = ed(a);
        let n = self.next(s, bh, a, &k.public_key(), None)?;
        Some(sign(v0_unsigned(k.public_key(), a, r, n, actions, *bh), &k))
    }

    /// Called once per round before the block. Returns the pool transactions of a step due at
    /// this height; injected steps are queued for `take_injection`.
    pub fn round(&mut self, s: &Setup, bh: &CryptoHash, height: u64) -> Vec<(String, SignedTransaction)> {
        if !enabled() || height < self.next_height || !self.pending.is_empty() {
            return vec![];
        }
        loop {
            let i = self.next_step;
            let built = if mldsa_mode() { self.step_mldsa(i, s, bh) } else { self.step(i, s, bh) };
            let Some((name, mode, k, txs)) = built else {
                if i >= n_steps() {
                    return vec![];
                }
                // a pool transaction of an earlier step can land a few blocks late: wait for it
                if self.waited < 2 * GAP {
                    self.waited += 1;
                    eprintln!("keys scenario: step {i} waits for its prerequisite state at height {height}");
                    return vec![];
                }
                eprintln!("keys scenario: step {i} could not be built at height {height}; skipped");
                self.waited = 0;
                self.next_step += 1;
                continue;
            };
            self.waited = 0;
            self.next_step += 1;
            self.next_height = height + GAP;
            let label = format!("{}{i:02}.{name}", label_prefix());
            let txs: Vec<(String, SignedTransaction)> = txs.into_iter().map(|t| (label.clone(), t)).collect();
            eprintln!("keys scenario: step {label} ({mode:?}, shard index {k}) at height {height}");
            return match mode {
                Mode::Pool => txs,
                Mode::Inject => {
                    self.pending.push_back((k, txs));
                    vec![]
                }
            };
        }
    }
    /// The injected step due now, if any: (shard index, labelled transactions).
    pub fn take_injection(&mut self) -> Option<(usize, Vec<(String, SignedTransaction)>)> {
        self.pending.pop_front()
    }
    /// The chunk producer did not produce (skipped): retry at the next height.
    pub fn requeue(&mut self, x: (usize, Vec<(String, SignedTransaction)>)) {
        self.pending.push_front(x);
    }

    fn step(&mut self, i: usize, s: &Setup, bh: &CryptoHash) -> Option<(&'static str, Mode, usize, Vec<SignedTransaction>)> {
        use Mode::*;
        let bh = *bh;
        let (sa, da, ra, ma, ga, ha) = (a_secp(), a_deleg(), a_relay(), a_mldsa(), a_gas(), a_host());
        let s1 = sk(&sa, "main", KeyType::SECP256K1);
        let s2 = sk(&sa, "second", KeyType::SECP256K1);
        let s3 = sk(&sa, "fc", KeyType::SECP256K1);
        let off_curve = PublicKey::SECP256K1(Secp256K1PublicKey::from([1u8; 64]));
        let sd = sk(&da, "main", KeyType::SECP256K1);
        let ml1 = sk(&ma, "main", KeyType::MLDSA65);
        let ml2 = sk(&ma, "second", KeyType::MLDSA65);
        let ml3 = sk(&ma, "fc", KeyType::MLDSA65);
        let mlg = sk(&ma, "gas", KeyType::MLDSA65);
        let gk = sk(&ga, "gk", KeyType::ED25519);
        let gs = sk(&ga, "gks", KeyType::SECP256K1);
        let hk1 = sk(&ha, "hk1", KeyType::ED25519);
        let hk2 = sk(&ha, "hk2", KeyType::ED25519);
        let hk3 = sk(&ha, "hk3", KeyType::SECP256K1);
        let sink0 = acct("s0a00");
        let sink1 = acct("s1a00");
        let sink3 = acct("s3a00");
        let pkb = |pk: &PublicKey| borsh::to_vec(pk).unwrap();
        // a secp-signed V0 transfer from s0ksecp with key `k`, nonce `n`
        let secp_tx = |k: &Signer, n: u64, d: u128| v0_unsigned(k.public_key(), &sa, &sink0, n, vec![tr(d)], bh);
        let signed_with = |tx: Transaction, k: &Signer| -> Signature { k.sign(tx.get_hash_and_size().0.as_ref()) };
        // a delegate from s1kdeleg relayed by s1krelay
        let deleg = |this: &mut Self, nonce: u64, inner: Vec<Action>, receiver: &AccountId, pk: PublicKey, sig: &dyn Fn(&DelegateAction) -> Signature| -> Option<SignedTransaction> {
            let da_ = DelegateAction {
                sender_id: da.clone(),
                receiver_id: receiver.clone(),
                actions: inner.into_iter().map(|a| NonDelegateAction::try_from(a).unwrap()).collect(),
                nonce,
                max_block_height: 10_000_000,
                public_key: pk,
            };
            let signature = sig(&da_);
            this.ed_tx(s, &bh, &ra, &da, vec![Action::Delegate(Box::new(SignedDelegateAction { delegate_action: da_, signature }))])
        };
        let nep = |d: &DelegateAction, k: &Signer| k.sign(d.get_nep461_hash().as_bytes());
        let x: (&'static str, Mode, usize, Vec<SignedTransaction>) = match i {
            // ---- secp256k1 transaction keys (s0ksecp, shard index 0)
            0 => {
                let n = self.next(s, &bh, &sa, &s1.public_key(), None)?;
                ("secp-tx-transfer", Pool, 0, vec![sign(secp_tx(&s1, n, NEAR), &s1)])
            }
            1 | 2 | 3 | 4 => {
                let n = self.next(s, &bh, &sa, &s1.public_key(), None)?;
                let tx = secp_tx(&s1, n, 1 + i as u128);
                let e = [SecpEdit::RecIdFlip, SecpEdit::BitFlip, SecpEdit::HighS, SecpEdit::RecId4][i - 1];
                if !matches!(e, SecpEdit::RecIdFlip) {
                    // an invalid signature does not consume the nonce
                    self.used.insert((sa.clone(), s1.public_key(), None), n - 1);
                }
                let sig = edit_secp(&signed_with(tx.clone(), &s1), e);
                let name = ["secp-tx-recid-flip", "secp-tx-bad-sig", "secp-tx-high-s", "secp-tx-recid-4"][i - 1];
                (name, Inject, 0, vec![with_sig(tx, sig)])
            }
            5 => {
                let cur = self.cur(s, &bh, &sa, &s1.public_key(), None)?;
                ("secp-tx-stale-nonce", Inject, 0, vec![sign(secp_tx(&s1, cur, 5), &s1)])
            }
            6 => {
                // secp key, ED25519 signature by the account's test key: type mismatch
                let n = self.cur(s, &bh, &sa, &s1.public_key(), None)? + 1;
                let tx = secp_tx(&s1, n, 6);
                let sig = signed_with(tx.clone(), &ed(&sa));
                ("secp-tx-ed25519-sig", Inject, 0, vec![with_sig(tx, sig)])
            }
            7 => {
                let t = self.ed_tx(s, &bh, &sa, &sa, vec![
                    add_key(s2.public_key(), AccessKeyPermission::FullAccess),
                    add_key(s3.public_key(), AccessKeyPermission::FunctionCall(fc_perm(&sink0))),
                ])?;
                ("secp-add-keys", Pool, 0, vec![t])
            }
            8 => {
                let n = self.next(s, &bh, &sa, &s2.public_key(), None)?;
                let tx = v0_unsigned(s2.public_key(), &sa, &sink0, n, vec![tr(8), tr(9)], bh);
                ("secp-new-key-multi-action", Pool, 0, vec![sign(tx, &s2)])
            }
            9 => {
                let n = self.next(s, &bh, &sa, &s3.public_key(), None)?;
                let tx = v0_unsigned(s3.public_key(), &sa, &sink0, n, vec![fc("m", vec![1], 2)], bh);
                ("secp-fc-key-call", Pool, 0, vec![sign(tx, &s3)])
            }
            10 => {
                let n = self.next(s, &bh, &sa, &s1.public_key(), None)?;
                let tx = v0_unsigned(s1.public_key(), &sa, &sa, n, vec![del_key(s2.public_key())], bh);
                ("secp-signed-delete-key", Pool, 0, vec![sign(tx, &s1)])
            }
            11 => {
                let n = self.used.get(&(sa.clone(), s2.public_key(), None)).copied().unwrap_or(0) + 1;
                ("secp-deleted-key-tx", Inject, 0, vec![sign(secp_tx(&s2, n, 11), &s2)])
            }
            12 => {
                let t = self.ed_tx(s, &bh, &sa, &sa, vec![add_key(off_curve.clone(), AccessKeyPermission::FullAccess)])?;
                ("secp-add-off-curve-key", Pool, 0, vec![t])
            }
            13 => {
                // a well-formed (r, s) from a real key over this transaction, against the
                // off-curve key: public-key parsing fails
                let n = self.cur(s, &bh, &sa, &off_curve, None).unwrap_or(0) + 1;
                let tx = v0_unsigned(off_curve.clone(), &sa, &sink0, n, vec![tr(13)], bh);
                let sig = signed_with(tx.clone(), &s1);
                ("secp-off-curve-key-tx", Inject, 0, vec![with_sig(tx, sig)])
            }
            14 => {
                let t = self.ed_tx(s, &bh, &sa, &sa, vec![del_key(off_curve.clone())])?;
                ("secp-delete-off-curve-key", Pool, 0, vec![t])
            }
            // ---- delegate actions with a secp256k1 inner signer key (s1kdeleg, relayer s1krelay)
            15 => {
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                ("deleg-secp-valid", Pool, 1, vec![deleg(self, n, vec![tr(NEAR)], &sink1, sd.public_key(), &|d| nep(d, &sd))?])
            }
            16 | 17 | 19 => {
                let e = match i {
                    16 => SecpEdit::BitFlip,
                    17 => SecpEdit::HighS,
                    _ => SecpEdit::RecIdFlip,
                };
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                if i != 19 {
                    self.used.insert((da.clone(), sd.public_key(), None), n - 1);
                }
                let name = match i {
                    16 => "deleg-secp-bad-sig",
                    17 => "deleg-secp-high-s",
                    _ => "deleg-secp-recid-flip",
                };
                (name, Pool, 1, vec![deleg(self, n, vec![tr(i as u128)], &sink1, sd.public_key(), &|d| edit_secp(&nep(d, &sd), e))?])
            }
            18 => {
                let cur = self.cur(s, &bh, &da, &sd.public_key(), None)?;
                ("deleg-secp-stale-nonce", Pool, 1, vec![deleg(self, cur, vec![tr(18)], &sink1, sd.public_key(), &|d| nep(d, &sd))?])
            }
            20 => {
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                let k2 = sk(&da, "second", KeyType::SECP256K1).public_key();
                let inner = vec![add_key(k2.clone(), AccessKeyPermission::FullAccess), tr(20)];
                ("deleg-secp-inner-add-key", Pool, 1, vec![deleg(self, n, inner, &da, sd.public_key(), &|d| nep(d, &sd))?])
            }
            21 => {
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                let payload = VersionedDelegateActionPayload::V2(DelegateActionV2 {
                    sender_id: da.clone(),
                    receiver_id: sink1.clone(),
                    actions: vec![NonDelegateAction::try_from(tr(21)).unwrap()],
                    nonce: TransactionNonce::from_nonce(n),
                    max_block_height: 10_000_000,
                    public_key: sd.public_key(),
                });
                let a = Action::DelegateV2(Box::new(VersionedSignedDelegateAction::sign(&sd, payload)));
                ("deleg-v2-secp", Pool, 1, vec![self.ed_tx(s, &bh, &ra, &da, vec![a])?])
            }
            22 => {
                let n = self.cur(s, &bh, &da, &sd.public_key(), None)? + 1;
                let edk = ed(&da);
                ("deleg-secp-key-ed25519-sig", Pool, 1, vec![deleg(self, n, vec![tr(22)], &sink1, sd.public_key(), &|d| nep(d, &edk))?])
            }
            // ---- ML-DSA-65 keys (s2kmldsa, shard index 2)
            23 => {
                let t = self.ed_tx(s, &bh, &ma, &ma, vec![
                    add_key(ml2.public_key(), AccessKeyPermission::FullAccess),
                    add_key(ml3.public_key(), AccessKeyPermission::FunctionCall(fc_perm(&ma))),
                ])?;
                ("mldsa-add-keys", Pool, 2, vec![t])
            }
            24 => ("mldsa-delete-key", Pool, 2, vec![self.ed_tx(s, &bh, &ma, &ma, vec![del_key(ml2.public_key())])?]),
            25 => {
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                let tx = v0_unsigned(ml1.public_key(), &ma, &acct("s2a00"), n, vec![tr(25)], bh);
                ("mldsa-signed-tx", Inject, 2, vec![sign(tx, &ml1)])
            }
            26 => ("mldsa-add-gas-key", Pool, 2, vec![self.ed_tx(s, &bh, &ma, &ma, vec![add_key(mlg.public_key(), gas_full(1))])?]),
            // ---- gas keys (s3kgas, shard index 3)
            27 => ("gas-add-key", Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![add_key(gk.public_key(), gas_full(3))])?]),
            28 => {
                let a = Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: gk.public_key(), deposit: Balance::from_yoctonear(5 * NEAR) }));
                ("gas-fund", Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![a])?])
            }
            29 | 30 => {
                let idx = if i == 29 { 0 } else { 2 };
                let n = self.next(s, &bh, &ga, &gk.public_key(), Some(idx))?;
                let mode = if i == 29 { NonceMode::Monotonic } else { NonceMode::Strict };
                let tx = v1_unsigned(gk.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, idx), mode, vec![tr(i as u128)], bh);
                (if i == 29 { "gas-tx-index0" } else { "gas-tx-index2-strict" }, Pool, 3, vec![sign(tx, &gk)])
            }
            31 => {
                let cur = self.cur(s, &bh, &ga, &gk.public_key(), Some(0))?;
                let tx = v1_unsigned(gk.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(cur, 0), NonceMode::Monotonic, vec![tr(31)], bh);
                ("gas-tx-stale-nonce", Inject, 3, vec![sign(tx, &gk)])
            }
            32 => {
                let n = self.cur(s, &bh, &ga, &gk.public_key(), Some(0))? + 1;
                let tx = v1_unsigned(gk.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, 3), NonceMode::Monotonic, vec![tr(32)], bh);
                ("gas-tx-index-out-of-range", Inject, 3, vec![sign(tx, &gk)])
            }
            33 => {
                let n = self.cur(s, &bh, &ga, &gk.public_key(), Some(1))? + 1;
                let tx = v1_unsigned(gk.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, 1), NonceMode::Monotonic, vec![tr(33)], bh);
                let sig = edit_ed(&signed_with(tx.clone(), &gk));
                ("gas-tx-bad-sig", Inject, 3, vec![with_sig(tx, sig)])
            }
            34 => {
                let n = self.cur(s, &bh, &ga, &gk.public_key(), None)? + 1;
                let tx = v0_unsigned(gk.public_key(), &ga, &sink3, n, vec![tr(34)], bh);
                ("gas-key-plain-nonce-tx", Inject, 3, vec![sign(tx, &gk)])
            }
            35 | 36 => {
                let amount = if i == 35 { NEAR } else { 100 * NEAR };
                let a = Action::WithdrawFromGasKey(Box::new(WithdrawFromGasKeyAction { public_key: gk.public_key(), amount: Balance::from_yoctonear(amount) }));
                (if i == 35 { "gas-withdraw" } else { "gas-withdraw-too-much" }, Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![a])?])
            }
            37 => {
                let a = Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: gs.public_key(), deposit: Balance::from_yoctonear(1000) }));
                ("gas-add-secp-key-underfunded", Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![add_key(gs.public_key(), gas_full(2)), a])?])
            }
            38 => {
                let n = self.cur(s, &bh, &ga, &gs.public_key(), Some(1))? + 1;
                let tx = v1_unsigned(gs.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, 1), NonceMode::Monotonic, vec![tr(38)], bh);
                ("gas-tx-insufficient-balance", Inject, 3, vec![sign(tx, &gs)])
            }
            39 => {
                let a = Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: gs.public_key(), deposit: Balance::from_yoctonear(NEAR) }));
                ("gas-fund-secp-key", Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![a])?])
            }
            40 => {
                let n = self.next(s, &bh, &ga, &gs.public_key(), Some(1))?;
                let tx = v1_unsigned(gs.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, 1), NonceMode::Monotonic, vec![tr(40)], bh);
                ("gas-secp-key-tx", Pool, 3, vec![sign(tx, &gs)])
            }
            41 => {
                // DelegateV2 whose nonce is a gas-key nonce (index 1) of s3kgas, relayed by s1krelay
                let n = self.next(s, &bh, &ga, &gk.public_key(), Some(1))?;
                let payload = VersionedDelegateActionPayload::V2(DelegateActionV2 {
                    sender_id: ga.clone(),
                    receiver_id: sink3.clone(),
                    actions: vec![NonDelegateAction::try_from(tr(41)).unwrap()],
                    nonce: TransactionNonce::from_nonce_and_index(n, 1),
                    max_block_height: 10_000_000,
                    public_key: gk.public_key(),
                });
                let a = Action::DelegateV2(Box::new(VersionedSignedDelegateAction::sign(&gk, payload)));
                ("gas-delegate-v2-gas-key-nonce", Pool, 1, vec![self.ed_tx(s, &bh, &ra, &ga, vec![a])?])
            }
            42 => ("gas-delete-key-with-balance", Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![del_key(gk.public_key())])?]),
            43 => {
                let n = self.used.get(&(ga.clone(), gk.public_key(), Some(0))).copied().unwrap_or(0) + 1;
                let tx = v1_unsigned(gk.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, 0), NonceMode::Monotonic, vec![tr(43)], bh);
                ("gas-deleted-key-tx", Inject, 3, vec![sign(tx, &gk)])
            }
            44 => {
                let k = ed(&ga);
                let n = self.cur(s, &bh, &ga, &k.public_key(), None)? + 1;
                let bad = sk(&ga, "zero", KeyType::ED25519).public_key();
                let tx = v0_unsigned(k.public_key(), &ga, &ga, n, vec![add_key(bad, gas_full(0))], bh);
                ("gas-add-key-zero-nonces", Inject, 3, vec![sign(tx, &k)])
            }
            45 | 46 => {
                let pk = if i == 45 { sk(&ga, "absent", KeyType::ED25519).public_key() } else { ed(&ga).public_key() };
                let a = Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: pk, deposit: Balance::from_yoctonear(NEAR) }));
                (if i == 45 { "gas-fund-missing-key" } else { "gas-fund-regular-key" }, Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![a])?])
            }
            // ---- gas-key promise hosts (s3kgashost)
            47..=54 => {
                let (name, method, args): (&'static str, &str, Vec<u8>) = match i {
                    47 => ("host-add-gas-key-full", "addfull", pkb(&hk1.public_key())),
                    48 => ("host-add-gas-key-function-call", "addfc", pkb(&hk2.public_key())),
                    49 => ("host-fund-gas-key", "fund", pkb(&hk1.public_key())),
                    50 => ("host-add-and-fund-secp-gas-key", "addfund", pkb(&hk3.public_key())),
                    51 => {
                        let mut v = vec![ga.as_str().len() as u8];
                        v.extend(ga.as_bytes());
                        v.extend(pkb(&gs.public_key()));
                        ("host-fund-other-account-gas-key", "fundto", v)
                    }
                    52 => ("host-fund-missing-gas-key", "fund", pkb(&sk(&ha, "absent", KeyType::ED25519).public_key())),
                    53 => ("host-malformed-key", "addfull", vec![7, 1, 2, 3]),
                    _ => ("host-add-mldsa-gas-key", "addfull", pkb(&sk(&ha, "ml", KeyType::MLDSA65).public_key())),
                };
                (name, Pool, 3, vec![self.ed_tx(s, &bh, &ha, &ha, vec![fc(method, args, 30)])?])
            }
            55 => {
                let n = self.next(s, &bh, &ha, &hk1.public_key(), Some(0))?;
                let tx = v1_unsigned(hk1.public_key(), &ha, &sink3, TransactionNonce::from_nonce_and_index(n, 0), NonceMode::Monotonic, vec![tr(55)], bh);
                ("host-gas-key-tx", Pool, 3, vec![sign(tx, &hk1)])
            }
            // ---- gas-key deletion once empty (step 42 shows a funded gas key cannot be deleted)
            56 => {
                let bal = view_key(s, &bh, &ga, &gk.public_key())?.gas_key_info()?.balance;
                let a = Action::WithdrawFromGasKey(Box::new(WithdrawFromGasKeyAction { public_key: gk.public_key(), amount: bal }));
                ("gas-withdraw-all", Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![a])?])
            }
            57 => ("gas-delete-empty-key", Pool, 3, vec![self.ed_tx(s, &bh, &ga, &ga, vec![del_key(gk.public_key())])?]),
            58 => {
                let n = self.used.get(&(ga.clone(), gk.public_key(), Some(0))).copied().unwrap_or(0) + 1;
                let tx = v1_unsigned(gk.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, 0), NonceMode::Monotonic, vec![tr(58)], bh);
                ("gas-removed-key-tx", Inject, 3, vec![sign(tx, &gk)])
            }
            59 => {
                let k = ed(&ga);
                let n = self.cur(s, &bh, &ga, &k.public_key(), None)? + 1;
                let tx = v1_unsigned(k.public_key(), &ga, &sink3, TransactionNonce::from_nonce_and_index(n, 0), NonceMode::Monotonic, vec![tr(59)], bh);
                ("gas-nonce-index-on-regular-key", Inject, 3, vec![sign(tx, &k)])
            }
            _ => return None,
        };
        Some(x)
    }
}

pub const N_STEPS: usize = 60;

/// Every outcome nearcore recorded for the scenario's transactions, walked through their receipts:
/// (label, tx hash) -> outcomes with executor, status, block height and executing shard. A
/// transaction without an outcome was dropped as invalid (or never included).
pub fn write_outcomes(s: &Setup, labels: &HashMap<CryptoHash, String>, path: &std::path::Path) {
    use near_primitives::transaction::ExecutionOutcomeWithIdAndProof;
    let find = |id: &CryptoHash| -> Option<ExecutionOutcomeWithIdAndProof> {
        s.env.clients.iter().find_map(|c| c.chain.get_execution_outcome(id).ok())
    };
    let where_ = |bh: &CryptoHash, a: &AccountId| -> (Option<u64>, Option<String>) {
        let c = &s.env.clients[0];
        let Ok(h) = c.chain.get_block_header(bh) else { return (None, None) };
        let shard = c.epoch_manager.get_shard_layout(h.epoch_id()).ok().map(|l| l.account_id_to_shard_id(a).to_string());
        (Some(h.height()), shard)
    };
    let mut rows: Vec<(String, serde_json::Value)> = Vec::new();
    for (hash, label) in labels {
        if !label.starts_with(label_prefix()) {
            continue;
        }
        let mut outcomes = Vec::new();
        let mut queue = vec![*hash];
        while let Some(id) = queue.pop() {
            let Some(o) = find(&id) else {
                outcomes.push(serde_json::json!({"id": id.to_string(), "outcome": null}));
                continue;
            };
            let oc = &o.outcome_with_id.outcome;
            let (height, shard) = where_(&o.block_hash, &oc.executor_id);
            outcomes.push(serde_json::json!({
                "id": id.to_string(), "executor": oc.executor_id.to_string(),
                "status": format!("{:?}", oc.status), "gas_burnt": oc.gas_burnt.as_gas(),
                "tokens_burnt": oc.tokens_burnt.as_yoctonear().to_string(),
                "block_height": height, "shard_id": shard,
            }));
            queue.extend(oc.receipt_ids.iter().rev().copied());
        }
        rows.push((label.clone(), serde_json::json!({"label": label, "tx_hash": hash.to_string(), "outcomes": outcomes})));
    }
    rows.sort_by(|a, b| a.0.cmp(&b.0).then(a.1["tx_hash"].as_str().cmp(&b.1["tx_hash"].as_str())));
    let v: Vec<serde_json::Value> = rows.into_iter().map(|x| x.1).collect();
    std::fs::write(path, serde_json::to_string_pretty(&v).unwrap()).unwrap();
}
