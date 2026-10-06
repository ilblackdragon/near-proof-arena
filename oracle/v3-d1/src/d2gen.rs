//! Domain D2 chain traffic (spec/near-chunk-validation-v0.md §6 D2): every non-WASM action
//! kind inside real chunks of a real multi-shard nearcore TestEnv.
//!
//! * Genesis (`genesis_records`): the D1 reserved-account keys (a05..a09, src/d1gen.rs) plus
//!   a `registrar` account (short top-level account creation), per shard a contract account
//!   `s{k}ct` holding `PROGRAM_WASM` (a tiny promise interpreter, below) and some contract
//!   data, and per shard three "fat" accounts `s{k}d0..d2` (many access keys, contract data,
//!   contract code, a gas key with nonces) that honest traffic deletes.
//! * Honest traffic (`World::gen_txs`, accounts a00..a04 and the accounts they create): plain,
//!   multi-action and self transactions; CreateAccount+Transfer+AddKey bundles (sub-accounts
//!   on any shard), creation failures (existing, top-level by non-registrar, not a
//!   sub-account, implicit), registrar top-level creation; transfers to NEAR-implicit,
//!   ETH-implicit, deterministic (`0s…`) and missing named receivers; AddKey (full access,
//!   function call with allowance and method names, gas keys), AddKey of an existing key,
//!   DeleteKey (regular, gas key, missing); Stake / unstake by validators and non-validators
//!   (incl. below-minimum, more-than-balance, unstake-without-stake); DeleteAccount with
//!   existing / missing / implicit beneficiaries, of fat accounts and of staking accounts;
//!   DeployContract of small real wasm modules (no call); TransferToGasKey, WithdrawFromGasKey,
//!   gas-key-nonce transactions; Delegate / DelegateV2 meta transactions (valid, bad signature,
//!   expired, stale nonce, sender mismatch, function-call key, missing key, gas-key nonce,
//!   inner DeleteAccount = instant receipt, also cross-shard); and contract calls that create
//!   promise chains with Transfer-only callbacks (postponed receipts, data receipts,
//!   `promise_and` with two inputs, callbacks creating accounts) and `promise_yield_create`
//!   (yield timeouts 200 blocks later). The contract-call chunks themselves execute WASM and
//!   are out of D2; the chunks that later process the data, the postponed Transfer callbacks
//!   and the yield timeouts are in D2.
//! * Crafted transactions (`craft`, reserved accounts, exact pre-state): invalid D2 shapes
//!   the honest pool never includes (gas-key nonce errors, deposit failure on a gas-key
//!   transaction, function-call keys used for non-FunctionCall actions, invalid action lists,
//!   …), injected by the adversarial chunk producer of src/d1gen.rs.

use crate::chaingen::Setup;
use near_crypto::{InMemorySigner, KeyType, PublicKey, Signature, Signer};
use near_primitives::account::{AccessKey, AccessKeyPermission, AccountContract, FunctionCallPermission, GasKeyInfo};
use near_primitives::action::delegate::{
    DelegateAction, DelegateActionV2, NonDelegateAction, SignedDelegateAction, VersionedDelegateActionPayload,
    VersionedSignedDelegateAction,
};
use near_primitives::action::{
    Action, AddKeyAction, CreateAccountAction, DeleteAccountAction, DeleteKeyAction, DeployContractAction,
    FunctionCallAction, StakeAction, TransferAction, TransferToGasKeyAction, WithdrawFromGasKeyAction,
};
use near_primitives::hash::CryptoHash;
use near_primitives::state_record::StateRecord;
use near_primitives::transaction::{SignedTransaction, Transaction, TransactionNonce, TransactionV0, TransactionV1, NonceMode};
use near_primitives::types::{AccountId, Balance, Gas};
use near_primitives_core::account::Account;
use near_store::Trie;
use rand::Rng;
use rand::rngs::StdRng;
use std::collections::HashMap;
use std::sync::OnceLock;

/// A promise "interpreter" contract (WAT below). `run` reads its input as a program:
///   1 n acct            push promise_batch_create(acct)
///   2 s n acct          push promise_batch_then(slot s, acct)
///   3 a b               push promise_and([slot a, slot b])
///   4 s amount(16 LE)   promise_batch_action_transfer(slot s, amount)
///   5 s                 promise_batch_action_create_account(slot s)
///   6 s pk(33)          promise_batch_action_add_key_with_full_access(slot s, pk, 0)
///   7 n method          push promise_yield_create(method, "", 5 Tgas, 0, register 0)
/// `cb` does nothing (the yield callback).
const PROGRAM_WAT: &str = r#"(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "promise_batch_create" (func $pbc (param i64 i64) (result i64)))
  (import "env" "promise_batch_then" (func $pbt (param i64 i64 i64) (result i64)))
  (import "env" "promise_and" (func $pand (param i64 i64) (result i64)))
  (import "env" "promise_batch_action_create_account" (func $pca (param i64)))
  (import "env" "promise_batch_action_transfer" (func $ptr (param i64 i64)))
  (import "env" "promise_batch_action_add_key_with_full_access" (func $pak (param i64 i64 i64 i64)))
  (import "env" "promise_yield_create" (func $pyc (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (memory 1)
  (global $ns (mut i32) (i32.const 0))
  (func $push (param $v i64)
    (i64.store (i32.add (i32.const 4096) (i32.mul (global.get $ns) (i32.const 8))) (local.get $v))
    (global.set $ns (i32.add (global.get $ns) (i32.const 1))))
  (func $slot (param $i i32) (result i64)
    (i64.load (i32.add (i32.const 4096) (i32.mul (local.get $i) (i32.const 8)))))
  (func $p64 (param $x i32) (result i64) (i64.extend_i32_u (local.get $x)))
  (func (export "cb"))
  (func (export "run") (local $pc i32) (local $len i32) (local $op i32) (local $n i32) (local $s i32)
    (call $input (i64.const 0))
    (local.set $len (i32.wrap_i64 (call $register_len (i64.const 0))))
    (call $read_register (i64.const 0) (i64.const 0))
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $pc) (local.get $len)))
        (local.set $op (i32.load8_u (local.get $pc)))
        (local.set $pc (i32.add (local.get $pc) (i32.const 1)))
        (if (i32.eq (local.get $op) (i32.const 1)) (then
          (local.set $n (i32.load8_u (local.get $pc)))
          (call $push (call $pbc (call $p64 (local.get $n)) (call $p64 (i32.add (local.get $pc) (i32.const 1)))))
          (local.set $pc (i32.add (local.get $pc) (i32.add (local.get $n) (i32.const 1))))
          (br $next)))
        (if (i32.eq (local.get $op) (i32.const 2)) (then
          (local.set $s (i32.load8_u (local.get $pc)))
          (local.set $n (i32.load8_u (i32.add (local.get $pc) (i32.const 1))))
          (call $push (call $pbt (call $slot (local.get $s)) (call $p64 (local.get $n)) (call $p64 (i32.add (local.get $pc) (i32.const 2)))))
          (local.set $pc (i32.add (local.get $pc) (i32.add (local.get $n) (i32.const 2))))
          (br $next)))
        (if (i32.eq (local.get $op) (i32.const 3)) (then
          (i64.store (i32.const 8192) (call $slot (i32.load8_u (local.get $pc))))
          (i64.store (i32.const 8200) (call $slot (i32.load8_u (i32.add (local.get $pc) (i32.const 1)))))
          (call $push (call $pand (i64.const 8192) (i64.const 2)))
          (local.set $pc (i32.add (local.get $pc) (i32.const 2)))
          (br $next)))
        (if (i32.eq (local.get $op) (i32.const 4)) (then
          (call $ptr (call $slot (i32.load8_u (local.get $pc))) (call $p64 (i32.add (local.get $pc) (i32.const 1))))
          (local.set $pc (i32.add (local.get $pc) (i32.const 17)))
          (br $next)))
        (if (i32.eq (local.get $op) (i32.const 5)) (then
          (call $pca (call $slot (i32.load8_u (local.get $pc))))
          (local.set $pc (i32.add (local.get $pc) (i32.const 1)))
          (br $next)))
        (if (i32.eq (local.get $op) (i32.const 6)) (then
          (call $pak (call $slot (i32.load8_u (local.get $pc))) (i64.const 33) (call $p64 (i32.add (local.get $pc) (i32.const 1))) (i64.const 0))
          (local.set $pc (i32.add (local.get $pc) (i32.const 34)))
          (br $next)))
        (if (i32.eq (local.get $op) (i32.const 7)) (then
          (local.set $n (i32.load8_u (local.get $pc)))
          (call $push (call $pyc (call $p64 (local.get $n)) (call $p64 (i32.add (local.get $pc) (i32.const 1)))
                                 (i64.const 0) (i64.const 0) (i64.const 5000000000000) (i64.const 0) (i64.const 0)))
          (local.set $pc (i32.add (local.get $pc) (i32.add (local.get $n) (i32.const 1))))
          (br $next)))
        (br $done))))
)"#;

pub fn program_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(PROGRAM_WAT).expect("program wat"))
}

/// Small real wasm modules deployed (never called) by honest DeployContract traffic.
pub fn small_wasm(i: usize) -> Vec<u8> {
    match i % 4 {
        0 => wat::parse_str(r#"(module (func (export "main")))"#).unwrap(),
        1 => wat::parse_str(r#"(module (memory 1) (func (export "a")) (func (export "b")) (data (i32.const 0) "near-arena-d2"))"#).unwrap(),
        2 => program_wasm().to_vec(),
        _ => {
            // > 770 bytes: the account stops being a zero-balance account
            let payload = "d".repeat(900);
            wat::parse_str(&format!(r#"(module (memory 1) (func (export "main")) (data (i32.const 0) "{payload}"))"#)).unwrap()
        }
    }
}

pub fn acct(s: &str) -> AccountId {
    s.parse().unwrap()
}
pub fn contract_acct(k: usize) -> AccountId {
    acct(&format!("s{k}ct"))
}
pub fn fat_acct(k: usize, j: usize) -> AccountId {
    acct(&format!("s{k}d{j}"))
}
pub fn registrar() -> AccountId {
    acct("registrar")
}
pub fn key_signer(a: &AccountId, tag: &str) -> Signer {
    InMemorySigner::from_seed(a.clone(), KeyType::ED25519, &format!("{tag}-{a}"))
}

/// Extra genesis records of D2 chains (on top of the D0 accounts and the D1 reserved keys).
/// Returns (records, extra total supply).
pub fn genesis_records(accounts: &[Vec<AccountId>]) -> (Vec<StateRecord>, Balance) {
    let mut r = crate::d1gen::genesis_records(accounts);
    let mut supply = Balance::ZERO;
    let mut add_acct = |r: &mut Vec<StateRecord>, a: &AccountId, amount: Balance, contract: AccountContract| {
        r.push(StateRecord::Account { account_id: a.clone(), account: Account::new(amount, Balance::ZERO, contract, 0) });
        r.push(StateRecord::access_key(a.clone(), &InMemorySigner::test_signer(a).public_key(), AccessKey::full_access()));
        supply = supply.checked_add(amount).unwrap();
    };
    add_acct(&mut r, &registrar(), Balance::from_near(1_000_000), AccountContract::None);
    // a second full-access key of each honest account, used only to sign delegate actions
    // (its nonce advances independently of the account's transactions)
    for sh in accounts {
        for a in sh.iter().take(HONEST) {
            r.push(StateRecord::access_key(a.clone(), &key_signer(a, "dl").public_key(), AccessKey::full_access()));
        }
    }
    let code = program_wasm().to_vec();
    let code_hash = CryptoHash::hash_bytes(&code);
    for k in 0..accounts.len() {
        let c = contract_acct(k);
        add_acct(&mut r, &c, Balance::from_near(1_000_000), AccountContract::Local(code_hash));
        r.push(StateRecord::Contract { account_id: c.clone(), code: code.clone() });
        for i in 0..4u8 {
            r.push(StateRecord::Data { account_id: c.clone(), data_key: vec![b'k', i].into(), value: vec![i; 10].into() });
        }
        // fat accounts: d0 small (deletable), d1 with code + gas key, d2 large state (> 10 000 bytes)
        for j in 0..3 {
            let a = fat_acct(k, j);
            let small = small_wasm(1);
            let contract = if j == 1 { AccountContract::Local(CryptoHash::hash_bytes(&small)) } else { AccountContract::None };
            add_acct(&mut r, &a, Balance::from_near(100), contract);
            let nkeys = [12, 6, 60][j];
            for i in 0..nkeys {
                r.push(StateRecord::access_key(a.clone(), &key_signer(&a, &format!("fat{i}")).public_key(), AccessKey::full_access()));
            }
            let ndata = [20u8, 5, 80][j];
            for i in 0..ndata {
                r.push(StateRecord::Data { account_id: a.clone(), data_key: vec![b'd', i].into(), value: vec![i; 40].into() });
            }
            if j == 1 {
                r.push(StateRecord::Contract { account_id: a.clone(), code: small });
                let gk = key_signer(&a, "gk").public_key();
                r.push(StateRecord::access_key(
                    a.clone(),
                    &gk,
                    AccessKey { nonce: 0, permission: AccessKeyPermission::GasKeyFullAccess(GasKeyInfo { balance: Balance::ZERO, num_nonces: 3 }) },
                ));
                for i in 0..3u16 {
                    r.push(StateRecord::gas_key_nonce(a.clone(), &gk, i, 0));
                }
            }
        }
    }
    (r, supply)
}

// ---------------------------------------------------------------------------------------------
// state views (the tip state of a shard, from any client that has the chunk extra)
// ---------------------------------------------------------------------------------------------

pub fn trie_for(s: &Setup, block_hash: &CryptoHash, a: &AccountId) -> Option<Trie> {
    let c0 = &s.env.clients[0];
    let epoch_id = c0.epoch_manager.get_epoch_id(block_hash).ok()?;
    let layout = c0.epoch_manager.get_shard_layout(&epoch_id).ok()?;
    let sid = layout.account_id_to_shard_id(a);
    let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(sid, &layout);
    let (c, extra) = s.env.clients.iter().find_map(|c| c.chain.get_chunk_extra(block_hash, &uid).ok().map(|e| (c, e)))?;
    c.runtime_adapter.get_trie_for_shard(sid, block_hash, *extra.state_root(), false).ok()
}

pub fn view_account(s: &Setup, bh: &CryptoHash, a: &AccountId) -> Option<Account> {
    near_store::get_account(&trie_for(s, bh, a)?, a).ok().flatten()
}
pub fn view_key(s: &Setup, bh: &CryptoHash, a: &AccountId, pk: &PublicKey) -> Option<AccessKey> {
    near_store::get_access_key(&trie_for(s, bh, a)?, a, pk).ok().flatten()
}
pub fn view_gk_nonce(s: &Setup, bh: &CryptoHash, a: &AccountId, pk: &PublicKey, i: u16) -> Option<u64> {
    near_store::get_gas_key_nonce(&trie_for(s, bh, a)?, a, pk, i).ok().flatten()
}

// ---------------------------------------------------------------------------------------------
// honest traffic
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct KeyRec {
    pub signer: Signer,
    pub gas_nonces: u16, // 0 = not a gas key
    pub fc: bool,
    /// function-call key for a contract account: (receiver, method)
    pub fc_contract: Option<(AccountId, String)>,
}

pub struct World {
    pub accounts: Vec<Vec<AccountId>>,
    pub n_shards: usize,
    /// known keys per account (index 0 = main full-access key)
    pub keys: HashMap<AccountId, Vec<KeyRec>>,
    /// local next-nonce cache per (account, key[, gas nonce index])
    nonces: HashMap<(AccountId, PublicKey, Option<u16>), u64>,
    /// accounts created by honest traffic (sub-accounts, top-level by registrar, contract callbacks)
    pub created: Vec<AccountId>,
    pub ctr: u64,
    pub validators: Vec<AccountId>,
    /// non-validators allowed to stake successfully (they run TestEnv clients)
    pub stakers: Vec<AccountId>,
    pub minimum_stake: u128,
    pub seat_price: u128,
    /// contract calls are mostly `promise_yield_create`
    pub yield_bias: bool,
}

pub const HONEST: usize = 5;

impl World {
    pub fn new(accounts: &[Vec<AccountId>], validators: Vec<AccountId>, stakers: Vec<AccountId>) -> Self {
        let mut keys = HashMap::new();
        let mut add = |a: &AccountId| {
            keys.insert(a.clone(), vec![KeyRec { signer: InMemorySigner::test_signer(a), gas_nonces: 0, fc: false, fc_contract: None }]);
        };
        for sh in accounts {
            for a in sh.iter().take(HONEST) {
                add(a);
            }
        }
        add(&registrar());
        for k in 0..accounts.len() {
            for j in 0..3 {
                add(&fat_acct(k, j));
            }
        }
        // the genesis gas key of the fat account d1
        for k in 0..accounts.len() {
            let a = fat_acct(k, 1);
            keys.get_mut(&a).unwrap().push(KeyRec { signer: key_signer(&a, "gk"), gas_nonces: 3, fc: false, fc_contract: None });
        }
        World {
            accounts: accounts.to_vec(),
            n_shards: accounts.len(),
            keys,
            nonces: HashMap::new(),
            created: vec![],
            ctr: 0,
            validators,
            stakers,
            minimum_stake: 0,
            seat_price: 0,
            yield_bias: false,
        }
    }

    fn honest(&self, rng: &mut StdRng, k: usize) -> AccountId {
        self.accounts[k][rng.gen_range(0..HONEST)].clone()
    }
    fn any_honest(&self, rng: &mut StdRng) -> AccountId {
        let k = rng.gen_range(0..self.n_shards);
        self.honest(rng, k)
    }

    /// next nonce of (account, key[, index]); reads the tip state the first time
    fn next_nonce(&mut self, s: &Setup, bh: &CryptoHash, a: &AccountId, pk: &PublicKey, idx: Option<u16>) -> Option<u64> {
        let key = (a.clone(), pk.clone(), idx);
        if let Some(n) = self.nonces.get_mut(&key) {
            *n += 1;
            return Some(*n);
        }
        let cur = match idx {
            None => view_key(s, bh, a, pk)?.nonce,
            Some(i) => view_gk_nonce(s, bh, a, pk, i)?,
        };
        self.nonces.insert(key, cur + 1);
        Some(cur + 1)
    }

    fn main_signer(&self, a: &AccountId) -> Signer {
        self.keys.get(a).map(|v| v[0].signer.clone()).unwrap_or_else(|| InMemorySigner::test_signer(a))
    }

    fn tx(&mut self, s: &Setup, bh: &CryptoHash, signer_id: &AccountId, receiver: &AccountId, actions: Vec<Action>) -> Option<SignedTransaction> {
        let signer = self.main_signer(signer_id);
        let n = self.next_nonce(s, bh, signer_id, &signer.public_key(), None)?;
        Some(SignedTransaction::from_actions(n, signer_id.clone(), receiver.clone(), &signer, actions, *bh))
    }

    /// a transaction signed with the account's main key (bursts)
    pub fn plain_tx(&mut self, s: &Setup, bh: &CryptoHash, signer_id: &AccountId, receiver: &AccountId, actions: Vec<Action>) -> Option<SignedTransaction> {
        self.tx(s, bh, signer_id, receiver, actions)
    }

    fn fresh(&mut self) -> u64 {
        self.ctr += 1;
        self.ctr
    }

    fn sub_name(&mut self, rng: &mut StdRng, parent: &AccountId) -> AccountId {
        let t = rng.gen_range(0..self.n_shards);
        let n = self.fresh();
        acct(&format!("s{t}x{n}.{parent}"))
    }

    fn transfer(dep: u128) -> Action {
        Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(dep) })
    }
    fn add_full(pk: PublicKey) -> Action {
        Action::AddKey(Box::new(AddKeyAction { public_key: pk, access_key: AccessKey::full_access() }))
    }

    /// Honest D2 transactions for this height: (label, tx).
    pub fn gen_txs(&mut self, s: &Setup, bh: &CryptoHash, height: u64, rng: &mut StdRng, n: usize, p_contract: f64) -> Vec<(String, SignedTransaction)> {
        let mut out = Vec::new();
        for _ in 0..n {
            if let Some(x) = self.one(s, bh, height, rng, p_contract) {
                out.push(x);
            }
        }
        out
    }

    fn one(&mut self, s: &Setup, bh: &CryptoHash, height: u64, rng: &mut StdRng, p_contract: f64) -> Option<(String, SignedTransaction)> {
        let me = self.any_honest(rng);
        let dep = rng.gen_range(1..10u128.pow(24));
        if rng.gen_bool(p_contract) {
            return self.contract_call(s, bh, rng, &me);
        }
        let kind = rng.gen_range(0..34);
        let (label, receiver, actions): (&str, AccountId, Vec<Action>) = match kind {
            0 => ("h.transfer", self.any_honest(rng), vec![Self::transfer(dep)]),
            1 => {
                let r = self.any_honest(rng);
                let m = rng.gen_range(2..5);
                ("h.transfer_multi", r, (0..m).map(|_| Self::transfer(rng.gen_range(1..10u128.pow(22)))).collect())
            }
            2 | 3 => {
                // CreateAccount + Transfer + AddKey(full access): a sub-account on any shard
                let sub = self.sub_name(rng, &me);
                let ks = key_signer(&sub, "sub");
                let amount = if rng.gen_bool(0.8) { 10u128.pow(24) * rng.gen_range(1..20) } else { 0 };
                let mut acts = vec![Action::CreateAccount(CreateAccountAction {}), Self::transfer(amount), Self::add_full(ks.public_key())];
                if rng.gen_bool(0.3) {
                    // a function-call key and a gas key too
                    acts.push(Action::AddKey(Box::new(AddKeyAction {
                        public_key: key_signer(&sub, "subfc").public_key(),
                        access_key: AccessKey {
                            nonce: 0,
                            permission: AccessKeyPermission::FunctionCall(FunctionCallPermission {
                                allowance: Some(Balance::from_near(1)),
                                receiver_id: me.to_string(),
                                method_names: vec!["m".into(), "nn".into()],
                            }),
                        },
                    })));
                }
                if amount > 0 && rng.gen_bool(0.2) {
                    acts.push(Action::DeployContract(DeployContractAction { code: small_wasm(rng.gen_range(0..4)) }));
                }
                self.keys.insert(sub.clone(), vec![KeyRec { signer: ks, gas_nonces: 0, fc: false, fc_contract: None }]);
                self.created.push(sub.clone());
                ("h.create_bundle", sub, acts)
            }
            4 => {
                // CreateAccount of an existing account (AccountAlreadyExists)
                let r = if !self.created.is_empty() && rng.gen_bool(0.5) {
                    self.created[rng.gen_range(0..self.created.len())].clone()
                } else {
                    self.any_honest(rng)
                };
                ("h.create_existing", r, vec![Action::CreateAccount(CreateAccountAction {}), Self::transfer(dep)])
            }
            5 => {
                let n = self.fresh();
                let t = rng.gen_range(0..self.n_shards);
                if rng.gen_bool(0.5) {
                    // registrar creates a short top-level account
                    let r = acct(&format!("s{t}r{n}"));
                    let ks = key_signer(&r, "sub");
                    let acts = vec![Action::CreateAccount(CreateAccountAction {}), Self::transfer(10u128.pow(24)), Self::add_full(ks.public_key())];
                    self.keys.insert(r.clone(), vec![KeyRec { signer: ks, gas_nonces: 0, fc: false, fc_contract: None }]);
                    self.created.push(r.clone());
                    let reg = registrar();
                    let t = self.tx(s, bh, &reg, &r, acts)?;
                    return Some(("h.create_toplevel_registrar".into(), t));
                }
                ("h.create_toplevel", acct(&format!("s{t}r{n}")), vec![Action::CreateAccount(CreateAccountAction {}), Self::transfer(dep)])
            }
            6 => {
                // not a sub-account of the predecessor
                let other = self.any_honest(rng);
                let n = self.fresh();
                let t = rng.gen_range(0..self.n_shards);
                let r = acct(&format!("s{t}y{n}.{other}"));
                let label = if other == me { "h.create_bundle" } else { "h.create_not_sub" };
                (label, r, vec![Action::CreateAccount(CreateAccountAction {}), Self::transfer(dep)])
            }
            7 => {
                let h: [u8; 32] = rng.r#gen();
                ("h.create_implicit", acct(&hex::encode(h)), vec![Action::CreateAccount(CreateAccountAction {}), Self::transfer(dep)])
            }
            8 => {
                let h: [u8; 32] = rng.r#gen();
                ("h.implicit_near", acct(&hex::encode(h)), vec![Self::transfer(dep)])
            }
            9 => {
                let h: [u8; 20] = rng.r#gen();
                ("h.implicit_eth", acct(&format!("0x{}", hex::encode(h))), vec![Self::transfer(dep)])
            }
            10 => {
                let h: [u8; 20] = rng.r#gen();
                ("h.deterministic", acct(&format!("0s{}", hex::encode(h))), vec![Self::transfer(dep)])
            }
            11 => {
                let n = self.fresh();
                let t = rng.gen_range(0..self.n_shards);
                ("h.transfer_missing", acct(&format!("s{t}zz{n}")), vec![Self::transfer(dep)])
            }
            12 => {
                // AddKey: full access / function call (allowance, methods) / gas key
                let i = self.fresh();
                let ks = key_signer(&me, &format!("k{i}"));
                let which = rng.gen_range(0..3);
                let (ak, gn, fc) = match which {
                    0 => (AccessKey::full_access(), 0, false),
                    1 => (
                        AccessKey {
                            nonce: 0,
                            permission: AccessKeyPermission::FunctionCall(FunctionCallPermission {
                                allowance: if rng.gen_bool(0.5) { Some(Balance::from_near(rng.gen_range(1..5))) } else { None },
                                receiver_id: self.any_honest(rng).to_string(),
                                method_names: (0..rng.gen_range(0..3)).map(|j| format!("method{j}")).collect(),
                            }),
                        },
                        0,
                        true,
                    ),
                    _ => {
                        let nn = rng.gen_range(1..4);
                        (AccessKey { nonce: 0, permission: AccessKeyPermission::GasKeyFullAccess(GasKeyInfo { balance: Balance::ZERO, num_nonces: nn }) }, nn, false)
                    }
                };
                self.keys.get_mut(&me).unwrap().push(KeyRec { signer: ks.clone(), gas_nonces: gn, fc, fc_contract: None });
                ("h.add_key", me.clone(), vec![Action::AddKey(Box::new(AddKeyAction { public_key: ks.public_key(), access_key: ak }))])
            }
            13 => {
                // AddKey of the main key again (AddKeyAlreadyExists)
                let pk = self.main_signer(&me).public_key();
                ("h.add_key_existing", me.clone(), vec![Self::add_full(pk)])
            }
            14 => {
                // DeleteKey of an added key (regular or gas key), or of a missing key
                let ks = self.keys.get(&me).unwrap();
                if ks.len() > 1 && rng.gen_bool(0.7) {
                    let i = rng.gen_range(1..ks.len());
                    let k = self.keys.get_mut(&me).unwrap().remove(i);
                    ("h.delete_key", me.clone(), vec![Action::DeleteKey(Box::new(DeleteKeyAction { public_key: k.signer.public_key() }))])
                } else {
                    let pk = key_signer(&me, &format!("missing{}", self.fresh())).public_key();
                    ("h.delete_key_missing", me.clone(), vec![Action::DeleteKey(Box::new(DeleteKeyAction { public_key: pk }))])
                }
            }
            15 | 16 => return self.stake(s, bh, rng),
            17 | 18 => return self.delete_account(s, bh, rng),
            19 => {
                let code = small_wasm(rng.gen_range(0..4));
                ("h.deploy", me.clone(), vec![Action::DeployContract(DeployContractAction { code })])
            }
            20 | 21 => return self.gas_key_op(s, bh, rng, &me, dep),
            22..=25 => return self.delegate(s, bh, height, rng),
            26 => {
                // self multi-action (local receipt): AddKey + DeleteKey + Transfer
                let i = self.fresh();
                let ks = key_signer(&me, &format!("tmp{i}"));
                (
                    "h.self_multi",
                    me.clone(),
                    vec![Self::add_full(ks.public_key()), Self::transfer(dep), Action::DeleteKey(Box::new(DeleteKeyAction { public_key: ks.public_key() }))],
                )
            }
            27 => {
                // a transaction from an account created by honest traffic (if it exists by now)
                if self.created.is_empty() {
                    return None;
                }
                let a = self.created[rng.gen_range(0..self.created.len())].clone();
                let r = self.any_honest(rng);
                let t = self.tx(s, bh, &a, &r, vec![Self::transfer(rng.gen_range(1..10u128.pow(22)))])?;
                return Some(("h.created_signer".into(), t));
            }
            28 => {
                // transfer to an account created by honest traffic (implicit/sub/top-level)
                if self.created.is_empty() {
                    return None;
                }
                let r = self.created[rng.gen_range(0..self.created.len())].clone();
                ("h.transfer_created", r, vec![Self::transfer(dep)])
            }
            29 => {
                // DeleteAccount must be final: [DeleteAccount, Transfer] is an invalid transaction
                // (the pool drops it); [Transfer, DeleteAccount] to another account fails
                // with ActorNoPermission
                let r = self.any_honest(rng);
                ("h.delete_other", r.clone(), vec![Self::transfer(dep), Action::DeleteAccount(DeleteAccountAction { beneficiary_id: me.clone() })])
            }
            30 => {
                // a larger batch: 6..12 transfers to one receiver
                let r = self.any_honest(rng);
                let m = rng.gen_range(6..13);
                ("h.transfer_batch", r, (0..m).map(|_| Self::transfer(rng.gen_range(1..10u128.pow(20)))).collect())
            }
            31 => {
                // a function-call key for a contract (allowance or unlimited, methods cb / any)
                let i = self.fresh();
                let ks = key_signer(&me, &format!("fck{i}"));
                let c = contract_acct(rng.gen_range(0..self.n_shards));
                let methods: Vec<String> = if rng.gen_bool(0.5) { vec!["cb".into()] } else { vec![] };
                let ak = AccessKey {
                    nonce: 0,
                    permission: AccessKeyPermission::FunctionCall(FunctionCallPermission {
                        allowance: if rng.gen_bool(0.7) { Some(Balance::from_near(1)) } else { None },
                        receiver_id: c.to_string(),
                        method_names: methods,
                    }),
                };
                self.keys.get_mut(&me).unwrap().push(KeyRec { signer: ks.clone(), gas_nonces: 0, fc: true, fc_contract: Some((c, "cb".into())) });
                ("h.add_fc_key_contract", me.clone(), vec![Action::AddKey(Box::new(AddKeyAction { public_key: ks.public_key(), access_key: ak }))])
            }
            32 | 33 => {
                // a FunctionCall signed by such a key (allowance charged; the gas refund later
                // tops the allowance up): converted and forwarded here, executed by the
                // contract's chunk (out of D2)
                let cands: Vec<(AccountId, KeyRec)> = self
                    .keys
                    .iter()
                    .flat_map(|(a, ks)| ks.iter().filter(|k| k.fc_contract.is_some()).map(move |k| (a.clone(), k.clone())))
                    .collect();
                if cands.is_empty() {
                    return None;
                }
                let mut cands = cands;
                cands.sort_by(|x, y| x.0.cmp(&y.0).then(x.1.signer.public_key().cmp(&y.1.signer.public_key())));
                let (owner, k) = cands[rng.gen_range(0..cands.len())].clone();
                let (c, m) = k.fc_contract.clone().unwrap();
                let pk = k.signer.public_key();
                let n = self.next_nonce(s, bh, &owner, &pk, None)?;
                let fc = Action::FunctionCall(Box::new(FunctionCallAction { method_name: m, args: vec![], gas: Gas::from_teragas(5), deposit: Balance::ZERO }));
                let t = SignedTransaction::from_actions(n, owner.clone(), c, &k.signer, vec![fc], *bh);
                return Some(("h.fc_key_call".into(), t));
            }
            _ => ("h.transfer", self.any_honest(rng), vec![Self::transfer(dep)]),
        };
        let t = self.tx(s, bh, &me, &receiver, actions)?;
        Some((label.to_string(), t))
    }

    fn stake(&mut self, s: &Setup, bh: &CryptoHash, rng: &mut StdRng) -> Option<(String, SignedTransaction)> {
        let min = self.minimum_stake;
        let which = rng.gen_range(0..7);
        let (label, a, amount): (&str, AccountId, u128) = match which {
            0 | 1 => {
                // a validator re-stakes (up or down by a little)
                let v = self.validators[rng.gen_range(0..self.validators.len())].clone();
                let acc = view_account(s, bh, &v)?;
                let cur = acc.locked().as_yoctonear();
                let delta = rng.gen_range(1..10u128.pow(27));
                let st = if rng.gen_bool(0.5) { cur + delta } else { cur.saturating_sub(delta).max(min) };
                ("h.stake_validator", v, st)
            }
            2 => {
                // a non-validator (with a client) stakes between the minimum and well below
                // the seat price
                let a = self.stakers[rng.gen_range(0..self.stakers.len())].clone();
                let hi = (min + min / 2).max(min + 1);
                ("h.stake_nonvalidator", a, rng.gen_range(min..hi))
            }
            3 => {
                let a = if rng.gen_bool(0.7) { self.stakers[rng.gen_range(0..self.stakers.len())].clone() } else { self.any_honest(rng) };
                if self.validators.contains(&a) {
                    return None;
                }
                let acc = view_account(s, bh, &a)?;
                if acc.locked().is_zero() {
                    ("h.unstake_not_staked", a, 0)
                } else {
                    ("h.unstake", a, 0)
                }
            }
            4 => {
                let a = self.any_honest(rng);
                ("h.stake_below_min", a, rng.gen_range(1..min.max(2)))
            }
            5 => {
                let a = self.any_honest(rng);
                let acc = view_account(s, bh, &a)?;
                // far above anything the account can hold by execution time (TriesToStake)
                ("h.stake_too_much", a, acc.amount().as_yoctonear() + acc.locked().as_yoctonear() + 10u128.pow(31) + rng.gen_range(1..10u128.pow(24)))
            }
            _ => {
                // DeleteAccount of a staking account fails (DeleteAccountStaking)
                let v = self.validators[rng.gen_range(0..self.validators.len())].clone();
                let b = self.any_honest(rng);
                let t = self.tx(s, bh, &v, &v, vec![Action::DeleteAccount(DeleteAccountAction { beneficiary_id: b })])?;
                return Some(("h.delete_staking".into(), t));
            }
        };
        let pk = self.main_signer(&a).public_key();
        let t = self.tx(s, bh, &a, &a, vec![Action::Stake(Box::new(StakeAction { stake: Balance::from_yoctonear(amount), public_key: pk }))])?;
        Some((label.into(), t))
    }

    fn delete_account(&mut self, s: &Setup, bh: &CryptoHash, rng: &mut StdRng) -> Option<(String, SignedTransaction)> {
        // a created account (signed with its own key) or a fat genesis account
        let a = if !self.created.is_empty() && rng.gen_bool(0.7) {
            self.created[rng.gen_range(0..self.created.len())].clone()
        } else {
            let k = rng.gen_range(0..self.n_shards);
            fat_acct(k, rng.gen_range(0..3))
        };
        let b = match rng.gen_range(0..6) {
            0 => {
                let n = self.fresh();
                acct(&format!("s{}zz{n}", rng.gen_range(0..self.n_shards)))
            }
            1 => {
                let h: [u8; 32] = rng.r#gen();
                acct(&hex::encode(h))
            }
            _ => self.any_honest(rng),
        };
        let label = match b.get_account_type() {
            near_primitives_core::account::id::AccountType::NamedAccount if b.as_str().contains("zz") => "h.delete_account_missing_beneficiary",
            near_primitives_core::account::id::AccountType::NamedAccount => "h.delete_account",
            _ => "h.delete_account_implicit_beneficiary",
        };
        let t = self.tx(s, bh, &a, &a, vec![Action::DeleteAccount(DeleteAccountAction { beneficiary_id: b })])?;
        Some((label.into(), t))
    }

    fn gas_key_op(&mut self, s: &Setup, bh: &CryptoHash, rng: &mut StdRng, me: &AccountId, dep: u128) -> Option<(String, SignedTransaction)> {
        // pick some account that has a gas key
        let cands: Vec<(AccountId, KeyRec)> = self
            .keys
            .iter()
            .flat_map(|(a, ks)| ks.iter().filter(|k| k.gas_nonces > 0).map(move |k| (a.clone(), k.clone())))
            .collect();
        if cands.is_empty() {
            return None;
        }
        let mut cands = cands;
        cands.sort_by(|x, y| x.0.cmp(&y.0).then(x.1.signer.public_key().cmp(&y.1.signer.public_key())));
        let (owner, k) = cands[rng.gen_range(0..cands.len())].clone();
        let pk = k.signer.public_key();
        match rng.gen_range(0..4) {
            0 => {
                // anyone funds a gas key
                let amt = Balance::from_yoctonear(rng.gen_range(10u128.pow(23)..10u128.pow(24)));
                let t = self.tx(s, bh, me, &owner, vec![Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: pk, deposit: amt }))])?;
                Some(("h.gas_fund".into(), t))
            }
            1 => {
                let amt = Balance::from_yoctonear(rng.gen_range(1..10u128.pow(23)));
                let t = self.tx(s, bh, &owner, &owner, vec![Action::WithdrawFromGasKey(Box::new(WithdrawFromGasKeyAction { public_key: pk, amount: amt }))])?;
                Some(("h.gas_withdraw".into(), t))
            }
            _ => {
                // a gas-key-nonce transaction (V1) signed by the gas key
                let idx = rng.gen_range(0..k.gas_nonces);
                let n = self.next_nonce(s, bh, &owner, &pk, Some(idx))?;
                let r = self.any_honest(rng);
                let acts = if rng.gen_bool(0.5) { vec![Self::transfer(dep / 1000)] } else { vec![Self::transfer(1), Self::transfer(2)] };
                let t = SignedTransaction::from_actions_v1(TransactionNonce::from_nonce_and_index(n, idx), owner.clone(), r, &k.signer, acts, *bh);
                Some(("h.gas_key_tx".into(), t))
            }
        }
    }

    fn delegate(&mut self, s: &Setup, bh: &CryptoHash, height: u64, rng: &mut StdRng) -> Option<(String, SignedTransaction)> {
        let relayer = self.any_honest(rng);
        // the sender: an honest account or a created one
        let sender = if !self.created.is_empty() && rng.gen_bool(0.3) {
            self.created[rng.gen_range(0..self.created.len())].clone()
        } else {
            self.any_honest(rng)
        };
        let ss = if self.accounts.iter().any(|sh| sh[..HONEST].contains(&sender)) { key_signer(&sender, "dl") } else { self.main_signer(&sender) };
        let variant = rng.gen_range(0..12);
        let dep = rng.gen_range(1..10u128.pow(23));
        let mut receiver = self.any_honest(rng);
        let mut inner: Vec<Action> = vec![Self::transfer(dep)];
        let mut label = "h.delegate";
        match variant {
            0 => {
                // inner CreateAccount bundle
                let sub = self.sub_name(rng, &sender);
                let ks = key_signer(&sub, "sub");
                inner = vec![Action::CreateAccount(CreateAccountAction {}), Self::transfer(10u128.pow(24)), Self::add_full(ks.public_key())];
                self.keys.insert(sub.clone(), vec![KeyRec { signer: ks, gas_nonces: 0, fc: false, fc_contract: None }]);
                self.created.push(sub.clone());
                receiver = sub;
                label = "h.delegate_create";
            }
            1 => {
                // inner DeleteAccount of the sender itself (an instant receipt)
                receiver = sender.clone();
                inner = vec![Action::DeleteAccount(DeleteAccountAction { beneficiary_id: relayer.clone() })];
                label = "h.delegate_delete_self";
            }
            2 => {
                // inner DeleteAccount of another account (an instant receipt processed on the
                // sender's shard: ActorNoPermission or AccountDoesNotExist)
                inner = vec![Action::DeleteAccount(DeleteAccountAction { beneficiary_id: relayer.clone() })];
                label = "h.delegate_delete_other";
            }
            3 => {
                inner = vec![Self::transfer(dep), Self::transfer(1), Self::add_full(key_signer(&sender, &format!("dk{}", self.fresh())).public_key())];
                receiver = sender.clone();
                label = "h.delegate_multi_self";
            }
            _ => {}
        }
        let nonce = self.next_nonce(s, bh, &sender, &ss.public_key(), None)?;
        let mut max_h = height + 100;
        let mut nonce_used = nonce;
        let mut da_sender = sender.clone();
        let mut sig_signer = ss.clone();
        let mut pk = ss.public_key();
        match variant {
            5 => {
                max_h = height.saturating_sub(5);
                label = "h.delegate_expired";
            }
            6 => {
                nonce_used = 1;
                label = "h.delegate_stale_nonce";
            }
            7 => {
                da_sender = self.any_honest(rng);
                label = "h.delegate_sender_mismatch";
            }
            8 => {
                sig_signer = key_signer(&sender, &format!("nokey{}", self.fresh()));
                pk = sig_signer.public_key();
                label = "h.delegate_missing_key";
            }
            9 => {
                label = "h.delegate_bad_sig";
            }
            _ => {}
        }
        let nda: Vec<NonDelegateAction> = inner.into_iter().map(|a| NonDelegateAction::try_from(a).unwrap()).collect();
        let action = if variant == 10 || variant == 11 {
            // DelegateV2: plain nonce, or a gas-key nonce of a gas key of the sender (if any)
            let gk = self.keys.get(&sender).and_then(|v| v.iter().find(|k| k.gas_nonces > 0).cloned());
            let (tn, signer2, lab) = match (variant, gk) {
                (11, Some(k)) => {
                    let idx = rng.gen_range(0..k.gas_nonces);
                    let n = self.next_nonce(s, bh, &sender, &k.signer.public_key(), Some(idx))?;
                    (TransactionNonce::from_nonce_and_index(n, idx), k.signer.clone(), "h.delegate_v2_gas_key")
                }
                _ => (TransactionNonce::from_nonce(nonce), ss.clone(), "h.delegate_v2"),
            };
            label = lab;
            let payload = VersionedDelegateActionPayload::V2(DelegateActionV2 {
                sender_id: sender.clone(),
                receiver_id: receiver.clone(),
                actions: nda,
                nonce: tn,
                max_block_height: max_h,
                public_key: signer2.public_key(),
            });
            Action::DelegateV2(Box::new(VersionedSignedDelegateAction::sign(&signer2, payload)))
        } else {
            let da = DelegateAction {
                sender_id: da_sender,
                receiver_id: receiver.clone(),
                actions: nda,
                nonce: nonce_used,
                max_block_height: max_h,
                public_key: pk,
            };
            let mut sda = SignedDelegateAction::sign(&sig_signer, da);
            if variant == 9 {
                if let Signature::ED25519(x) = &sda.signature {
                    let mut b = x.to_bytes();
                    b[rng.gen_range(0..32)] ^= 1 << rng.gen_range(0..8);
                    sda.signature = Signature::ED25519(ed25519_dalek::Signature::from_bytes(&b));
                }
            }
            Action::Delegate(Box::new(sda))
        };
        let t = self.tx(s, bh, &relayer, &sender, vec![action])?;
        Some((label.into(), t))
    }

    fn contract_call(&mut self, s: &Setup, bh: &CryptoHash, rng: &mut StdRng, me: &AccountId) -> Option<(String, SignedTransaction)> {
        let k = rng.gen_range(0..self.n_shards);
        let c = contract_acct(k);
        let mut prog: Vec<u8> = Vec::new();
        let push_acct = |prog: &mut Vec<u8>, a: &AccountId| {
            prog.push(a.len() as u8);
            prog.extend_from_slice(a.as_bytes());
        };
        let amt = |prog: &mut Vec<u8>, slot: u8, v: u128| {
            prog.push(4);
            prog.push(slot);
            prog.extend_from_slice(&v.to_le_bytes());
        };
        let which = if self.yield_bias && rng.gen_bool(0.7) { 5 } else { rng.gen_range(0..6) };
        let label;
        match which {
            0 | 1 => {
                // A.transfer().then(B.transfer()); A may be missing (failed input data)
                let a = if rng.gen_bool(0.25) { acct(&format!("s{}zz{}", rng.gen_range(0..self.n_shards), self.fresh())) } else { self.any_honest(rng) };
                let b = if rng.gen_bool(0.2) { c.clone() } else { self.any_honest(rng) };
                prog.push(1);
                push_acct(&mut prog, &a);
                amt(&mut prog, 0, rng.gen_range(1..10u128.pow(22)));
                prog.push(2);
                prog.push(0);
                push_acct(&mut prog, &b);
                amt(&mut prog, 1, rng.gen_range(1..10u128.pow(22)));
                if rng.gen_bool(0.3) {
                    amt(&mut prog, 1, 7);
                }
                label = "h.call_then";
            }
            2 => {
                // promise_and of two transfers, then a transfer callback (two input data ids)
                let a1 = self.any_honest(rng);
                let a2 = self.any_honest(rng);
                let b = self.any_honest(rng);
                prog.push(1);
                push_acct(&mut prog, &a1);
                amt(&mut prog, 0, 11);
                prog.push(1);
                push_acct(&mut prog, &a2);
                amt(&mut prog, 1, 12);
                prog.push(3);
                prog.push(0);
                prog.push(1);
                prog.push(2);
                prog.push(2);
                push_acct(&mut prog, &b);
                amt(&mut prog, 3, 13);
                label = "h.call_and_then";
            }
            3 => {
                // the callback creates a sub-account of the contract (CreateAccount+Transfer+AddKey)
                let a = self.any_honest(rng);
                let n = self.fresh();
                let t = rng.gen_range(0..self.n_shards);
                let sub = acct(&format!("s{t}q{n}.{c}"));
                let ks = key_signer(&sub, "sub");
                prog.push(1);
                push_acct(&mut prog, &a);
                amt(&mut prog, 0, 5);
                prog.push(2);
                prog.push(0);
                push_acct(&mut prog, &sub);
                prog.push(5);
                prog.push(1);
                amt(&mut prog, 1, 10u128.pow(24));
                prog.push(6);
                prog.push(1);
                prog.extend(borsh::to_vec(&ks.public_key()).unwrap());
                self.keys.insert(sub.clone(), vec![KeyRec { signer: ks, gas_nonces: 0, fc: false, fc_contract: None }]);
                self.created.push(sub);
                label = "h.call_then_create";
            }
            _ => {
                prog.push(7);
                prog.push(2);
                prog.extend_from_slice(b"cb");
                label = "h.call_yield";
            }
        }
        let fc = Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: "run".into(),
            args: prog,
            gas: Gas::from_teragas(100),
            deposit: Balance::ZERO,
        }));
        let t = self.tx(s, bh, me, &c, vec![fc])?;
        Some((label.into(), t))
    }
}

// ---------------------------------------------------------------------------------------------
// crafted transactions (adversarial chunk producer), reserved accounts a05..a09
// ---------------------------------------------------------------------------------------------

/// Pre-state of a reserved account at craft time.
#[derive(Clone, Debug)]
pub struct Reserved {
    pub amount: u128,
    pub ak_nonce: u64,
    /// a06's gas key: (balance, nonces)
    pub gk: Option<(u128, Vec<u64>)>,
    pub fc_nonce: u64,
}

pub struct CraftCtx<'a> {
    pub accounts: &'a [Vec<AccountId>],
    pub k: usize,
    pub n_shards: usize,
    pub apply_height: u64,
    pub gas_price: u128,
    pub tip_hash: CryptoHash,
    pub config: &'a near_parameters::RuntimeConfig,
    pub view: HashMap<AccountId, Reserved>,
}

pub const CLASSES: &[&str] = &[
    "x.multi_valid", "x.gas_fund", "x.gas_fund", "x.gas_tx_valid", "x.gas_tx_valid", "x.gas_nonce_index_oob", "x.gas_nonce_low",
    "x.gas_balance_low", "x.gas_deposit_failed", "x.gas_nonce_on_regular_key", "x.gas_key_plain_nonce",
    "x.fc_key_add_key", "x.fc_key_multi", "x.fc_key_stake", "x.invalid_delete_not_last",
    "x.invalid_two_delegates", "x.invalid_gas_key_balance", "x.invalid_gas_key_nonces", "x.invalid_stake_key",
    "x.invalid_too_many_actions", "x.multi_insufficient_balance", "x.multi_cost_overflow",
    "x.delegate_bad_sig", "x.delegate_valid", "x.withdraw_too_much", "x.gas_strict_nonce",
    "x.function_call_tx", "x.delegate_function_call", "x.fc_key_call", "x.delegate_secp_mismatch",
];
pub const OOD_CLASSES: &[&str] = &["ood_secp256k1_multi", "ood_delegate_secp", "ood_mldsa"];

fn sign_tx(tx: Transaction, s: &Signer) -> SignedTransaction {
    let sig = s.sign(tx.get_hash_and_size().0.as_ref());
    SignedTransaction::new(sig, tx)
}

fn v0(signer: &Signer, signer_id: &AccountId, receiver: &AccountId, nonce: u64, actions: Vec<Action>, bh: CryptoHash) -> SignedTransaction {
    sign_tx(
        Transaction::V0(TransactionV0 {
            signer_id: signer_id.clone(),
            public_key: signer.public_key(),
            nonce,
            receiver_id: receiver.clone(),
            block_hash: bh,
            actions,
        }),
        signer,
    )
}

fn v1(signer: &Signer, signer_id: &AccountId, receiver: &AccountId, nonce: TransactionNonce, mode: NonceMode, actions: Vec<Action>, bh: CryptoHash) -> SignedTransaction {
    sign_tx(
        Transaction::V1(TransactionV1 {
            signer_id: signer_id.clone(),
            public_key: signer.public_key(),
            nonce,
            receiver_id: receiver.clone(),
            block_hash: bh,
            actions,
            nonce_mode: mode,
        }),
        signer,
    )
}

fn tr(d: u128) -> Action {
    Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(d) })
}

pub fn craft(rng: &mut StdRng, ctx: &mut CraftCtx, n: usize, p_ood: f64) -> Vec<(String, SignedTransaction)> {
    let mut out = Vec::new();
    let sh = &ctx.accounts[ctx.k];
    let (a5, a6, a7) = (sh[5].clone(), sh[6].clone(), sh[7].clone());
    let s5 = InMemorySigner::test_signer(&a5);
    let s6 = InMemorySigner::test_signer(&a6);
    let gk6 = crate::d1gen::gk_signer(&a6);
    let fc7 = crate::d1gen::fc_signer(&a7);
    let bh = ctx.tip_hash;
    let n_shards = ctx.n_shards;
    let accounts = ctx.accounts;
    let recv = |rng: &mut StdRng| -> AccountId { accounts[rng.gen_range(0..n_shards)][rng.gen_range(0..HONEST)].clone() };
    let mut classes: Vec<&str> = (0..n).map(|_| CLASSES[rng.gen_range(0..CLASSES.len())]).collect();
    if rng.gen_bool(p_ood) {
        classes.push(OOD_CLASSES[rng.gen_range(0..OOD_CLASSES.len())]);
    }
    for class in classes {
        let v5 = ctx.view.get(&a5).cloned().unwrap();
        let v6 = ctx.view.get(&a6).cloned().unwrap();
        let mut fresh5 = || {
            let v = ctx.view.get_mut(&a5).unwrap();
            v.ak_nonce += 1;
            v.ak_nonce
        };
        let gk_state = v6.gk.clone();
        let txs: Vec<SignedTransaction> = match class {
            "x.multi_valid" => {
                let r = recv(rng);
                let nn = fresh5();
                let i = rng.r#gen::<u32>();
                vec![v0(&s5, &a5, &a5, nn, vec![tr(5), Action::AddKey(Box::new(AddKeyAction { public_key: key_signer(&a5, &format!("x{i}")).public_key(), access_key: AccessKey::full_access() }))], bh)]
                    .into_iter()
                    .chain(if rng.gen_bool(0.5) { Some(v0(&s5, &a5, &r, fresh5(), vec![tr(1), tr(2), tr(3)], bh)) } else { None })
                    .collect()
            }
            "x.gas_fund" => {
                let nn = fresh5();
                vec![v0(&s5, &a5, &a6, nn, vec![Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: gk6.public_key(), deposit: Balance::from_near(2) }))], bh)]
            }
            "x.gas_tx_valid" | "x.gas_nonce_low" | "x.gas_balance_low" | "x.gas_deposit_failed" | "x.gas_strict_nonce" => {
                let Some((bal, nonces)) = gk_state else { continue };
                let idx = rng.gen_range(0..nonces.len()) as u16;
                let cur = nonces[idx as usize];
                let r = recv(rng);
                let (nonce, mode, acts) = match class {
                    "x.gas_tx_valid" => (cur + 1 + rng.gen_range(0..3), NonceMode::Monotonic, vec![tr(rng.gen_range(1..10u128.pow(20)))]),
                    "x.gas_strict_nonce" => (cur + 1 + rng.gen_range(0..2), NonceMode::Strict, vec![tr(1)]),
                    "x.gas_nonce_low" => (cur, NonceMode::Monotonic, vec![tr(1)]),
                    "x.gas_balance_low" => {
                        // more actions than the balance pays for: gas cost > balance
                        if bal > 10u128.pow(22) {
                            continue;
                        }
                        (cur + 1, NonceMode::Monotonic, vec![tr(1); 30])
                    }
                    _ => (cur + 1, NonceMode::Monotonic, vec![tr(v6.amount + 1)]),
                };
                if class == "x.gas_tx_valid" || class == "x.gas_deposit_failed" || class == "x.gas_strict_nonce" {
                    let v = ctx.view.get_mut(&a6).unwrap();
                    if let Some((_, ns)) = v.gk.as_mut() {
                        ns[idx as usize] = ns[idx as usize].max(nonce);
                    }
                }
                vec![v1(&gk6, &a6, &r, TransactionNonce::from_nonce_and_index(nonce, idx), mode, acts, bh)]
            }
            "x.gas_nonce_index_oob" => {
                vec![v1(&gk6, &a6, &recv(rng), TransactionNonce::from_nonce_and_index(10, 2 + rng.gen_range(0..5)), NonceMode::Monotonic, vec![tr(1)], bh)]
            }
            "x.gas_nonce_on_regular_key" => {
                vec![v1(&s6, &a6, &recv(rng), TransactionNonce::from_nonce_and_index(v6.ak_nonce + 1, 0), NonceMode::Monotonic, vec![tr(1)], bh)]
            }
            "x.gas_key_plain_nonce" => vec![v0(&gk6, &a6, &recv(rng), 1 + rng.gen_range(0..1000), vec![tr(1), tr(2)], bh)],
            "x.fc_key_add_key" | "x.fc_key_multi" | "x.fc_key_stake" => {
                let acts = match class {
                    "x.fc_key_add_key" => vec![Action::AddKey(Box::new(AddKeyAction { public_key: key_signer(&a7, "fcadd").public_key(), access_key: AccessKey::full_access() }))],
                    "x.fc_key_multi" => vec![tr(1), tr(2)],
                    _ => vec![Action::Stake(Box::new(StakeAction { stake: Balance::from_near(1), public_key: fc7.public_key() }))],
                };
                let r = if class == "x.fc_key_multi" { sh[0].clone() } else { a7.clone() };
                vec![v0(&fc7, &a7, &r, 1 + rng.gen_range(0..1000), acts, bh)]
            }
            "x.invalid_delete_not_last" => {
                let nn = v5.ak_nonce + 1;
                vec![v0(&s5, &a5, &a5, nn, vec![Action::DeleteAccount(DeleteAccountAction { beneficiary_id: sh[0].clone() }), tr(1)], bh)]
            }
            "x.invalid_two_delegates" => {
                let da = |n: u64| {
                    Action::Delegate(Box::new(SignedDelegateAction::sign(
                        &s5,
                        DelegateAction {
                            sender_id: a5.clone(),
                            receiver_id: sh[0].clone(),
                            actions: vec![NonDelegateAction::try_from(tr(1)).unwrap()],
                            nonce: n,
                            max_block_height: ctx.apply_height + 100,
                            public_key: s5.public_key(),
                        },
                    )))
                };
                vec![v0(&s5, &a5, &a5, v5.ak_nonce + 1, vec![da(1), da(2)], bh)]
            }
            "x.invalid_gas_key_balance" | "x.invalid_gas_key_nonces" => {
                let gi = if class == "x.invalid_gas_key_balance" {
                    GasKeyInfo { balance: Balance::from_yoctonear(1), num_nonces: 1 }
                } else {
                    GasKeyInfo { balance: Balance::ZERO, num_nonces: if rng.gen_bool(0.5) { 0 } else { 1025 } }
                };
                let ak = AccessKey { nonce: 0, permission: AccessKeyPermission::GasKeyFullAccess(gi) };
                vec![v0(&s5, &a5, &a5, v5.ak_nonce + 1, vec![Action::AddKey(Box::new(AddKeyAction { public_key: key_signer(&a5, "badgk").public_key(), access_key: ak }))], bh)]
            }
            "x.invalid_stake_key" => {
                let sk = InMemorySigner::from_seed(a5.clone(), KeyType::SECP256K1, "stake-secp");
                vec![v0(&s5, &a5, &a5, v5.ak_nonce + 1, vec![Action::Stake(Box::new(StakeAction { stake: Balance::from_near(1), public_key: sk.public_key() }))], bh)]
            }
            "x.invalid_too_many_actions" => vec![v0(&s5, &a5, &recv(rng), v5.ak_nonce + 1, vec![tr(1); 101], bh)],
            "x.multi_insufficient_balance" => vec![v0(&s5, &a5, &recv(rng), v5.ak_nonce + 1, vec![tr(v5.amount / 2), tr(v5.amount / 2 + 1)], bh)],
            "x.multi_cost_overflow" => vec![v0(&s5, &a5, &recv(rng), v5.ak_nonce + 1, vec![tr(u128::MAX / 2), tr(u128::MAX / 2 + 2)], bh)],
            "x.delegate_bad_sig" | "x.delegate_valid" => {
                // relayer a5, sender a6 (its full-access key), inner transfer
                let da = DelegateAction {
                    sender_id: a6.clone(),
                    receiver_id: recv(rng),
                    actions: vec![NonDelegateAction::try_from(tr(3)).unwrap()],
                    nonce: v6.ak_nonce + 1 + rng.gen_range(0..1000),
                    max_block_height: ctx.apply_height + 100,
                    public_key: s6.public_key(),
                };
                let mut sda = SignedDelegateAction::sign(&s6, da);
                if class == "x.delegate_bad_sig" {
                    if let Signature::ED25519(x) = &sda.signature {
                        let mut b = x.to_bytes();
                        b[32 + rng.gen_range(0..28)] ^= 1 << rng.gen_range(0..8);
                        sda.signature = Signature::ED25519(ed25519_dalek::Signature::from_bytes(&b));
                    }
                }
                let nn = fresh5();
                vec![v0(&s5, &a5, &a6, nn, vec![Action::Delegate(Box::new(sda))], bh)]
            }
            "x.withdraw_too_much" => {
                let Some((bal, _)) = gk_state else { continue };
                vec![v0(&s6, &a6, &a6, v6.ak_nonce + 1 + rng.gen_range(0..100), vec![Action::WithdrawFromGasKey(Box::new(WithdrawFromGasKeyAction { public_key: gk6.public_key(), amount: Balance::from_yoctonear(bal + 1) }))], bh)]
            }
            "x.function_call_tx" => {
                // a FunctionCall transaction: converted and forwarded here (in D2); executed by
                // the contract's chunk (out of D2, e.wasm)
                let fc = Action::FunctionCall(Box::new(FunctionCallAction { method_name: "cb".into(), args: vec![1, 2, 3], gas: Gas::from_teragas(5), deposit: Balance::from_yoctonear(rng.gen_range(0..1000)) }));
                let nn = fresh5();
                vec![v0(&s5, &a5, &contract_acct(rng.gen_range(0..n_shards)), nn, vec![fc], bh)]
            }
            "x.fc_key_call" => {
                // a07's function-call key (receiver a00): calls on a00 (the permission passes,
                // receipt forwarded) or on another receiver (ReceiverMismatch) or with a deposit
                let fc = Action::FunctionCall(Box::new(FunctionCallAction { method_name: "m".into(), args: vec![], gas: Gas::from_teragas(1), deposit: Balance::from_yoctonear(if rng.gen_bool(0.2) { 1 } else { 0 }) }));
                let r = if rng.gen_bool(0.7) { sh[0].clone() } else { sh[1].clone() };
                let nn = ctx.view.get(&a7).map(|v| v.fc_nonce).unwrap_or(0) + 1 + rng.gen_range(0..1000);
                vec![v0(&fc7, &a7, &r, nn, vec![fc], bh)]
            }
            "x.delegate_secp_mismatch" => {
                // a delegate with an ED25519 key and a SECP256K1 signature: Signature::verify
                // is false without any ECDSA recovery (DelegateActionInvalidSignature, in D2)
                let a9 = sh[9].clone();
                let da = DelegateAction {
                    sender_id: a6.clone(),
                    receiver_id: recv(rng),
                    actions: vec![NonDelegateAction::try_from(tr(3)).unwrap()],
                    nonce: v6.ak_nonce + 1,
                    max_block_height: ctx.apply_height + 100,
                    public_key: s6.public_key(),
                };
                let sig = crate::d1gen::secp_signer(&a9).sign(da.get_nep461_hash().as_bytes());
                let nn = fresh5();
                vec![v0(&s5, &a5, &a6, nn, vec![Action::Delegate(Box::new(SignedDelegateAction { delegate_action: da, signature: sig }))], bh)]
            }
            "ood_delegate_secp" => {
                // a delegate signed by a09's SECP256K1 key: the signature is verified (e.secp)
                let a9 = sh[9].clone();
                let sk = crate::d1gen::secp_signer(&a9);
                let da = DelegateAction {
                    sender_id: a9.clone(),
                    receiver_id: recv(rng),
                    actions: vec![NonDelegateAction::try_from(tr(3)).unwrap()],
                    nonce: 1 + rng.gen_range(0..1000),
                    max_block_height: ctx.apply_height + 100,
                    public_key: sk.public_key(),
                };
                let sda = SignedDelegateAction::sign(&sk, da);
                let nn = fresh5();
                vec![v0(&s5, &a5, &a9, nn, vec![Action::Delegate(Box::new(sda))], bh)]
            }
            "ood_mldsa" => {
                // an AddKey of an ML-DSA-65 key (w.shape)
                let pk = InMemorySigner::from_seed(a5.clone(), KeyType::MLDSA65, "mldsa").public_key();
                let nn = fresh5();
                vec![v0(&s5, &a5, &a5, nn, vec![Action::AddKey(Box::new(AddKeyAction { public_key: pk, access_key: AccessKey::full_access() }))], bh)]
            }
            "ood_secp256k1_multi" => {
                let a9 = sh[9].clone();
                let sk = crate::d1gen::secp_signer(&a9);
                vec![v0(&sk, &a9, &recv(rng), 1 + rng.gen_range(0..1000), vec![tr(1), tr(2)], bh)]
            }
            "x.delegate_function_call" => {
                let fc = Action::FunctionCall(Box::new(FunctionCallAction { method_name: "cb".into(), args: vec![], gas: Gas::from_teragas(5), deposit: Balance::ZERO }));
                let da = DelegateAction {
                    sender_id: a6.clone(),
                    receiver_id: contract_acct(ctx.k),
                    actions: vec![NonDelegateAction::try_from(fc).unwrap()],
                    nonce: v6.ak_nonce + 1 + rng.gen_range(0..1000),
                    max_block_height: ctx.apply_height + 100,
                    public_key: s6.public_key(),
                };
                let sda = SignedDelegateAction::sign(&s6, da);
                let nn = fresh5();
                vec![v0(&s5, &a5, &a6, nn, vec![Action::Delegate(Box::new(sda))], bh)]
            }
            _ => unreachable!("{class}"),
        };
        for t in txs {
            out.push((class.to_string(), t));
        }
    }
    let _ = ctx.gas_price;
    let _ = ctx.config;
    out
}
