//! Domain-D3 honest traffic: WASM FunctionCalls on top of the D2 workload (src/chaind3.rs runs
//! both). Contracts (src/d3contracts.rs):
//!   * `s{k}rc` (every shard): d3rich, driven by random programs (`Prog`) — storage, logs,
//!     value returns, getters, hashes, registers, promise DAGs across shards with callbacks
//!     reading promise results, batch actions (FunctionCall, Transfer, CreateAccount + Transfer
//!     + AddKey [+ DeployContract d3tiny] [+ FunctionCall] [+ DeleteAccount] on fresh
//!     sub-accounts, AddKey/DeleteKey/Stake on itself), promise_return, yields and resumes,
//!     panics / aborts / traps / gas exhaustion;
//!   * `s{k}ctr`, `s{k}ctr2` (every shard): oracle/d3-ttn's ttn2 (storage-heavy, promise chains);
//!   * `s0fl` (d3float), `s{1}cv` (d3curve), `s{2}ed` (d3ed): rarely called, out of D3α
//!     (floats, a curve call) / the ed25519_verify import;
//!   * `s{3}hx` (d3hostx): imports a curve function and state-init / global-contract / gas-key
//!     functions; `run` calls none of them (in D3α, §10.0a P3), `curve` / `glob` / `stinit` /
//!     `gaskey` call one (out), `mlkey` builds Stake / AddKey / DeleteKey with an ML-DSA-65 key
//!     (out, P4);
//!   * `ETH_LOCAL` (0x + 40 hex, d3tiny): an ETH-implicit account with a `Local` contract; calls
//!     to it are out of D3α (P5).
//! Transactions: single and multi-action FunctionCalls (attached deposits, tight gas, missing
//! methods, wrong signatures, calls to code-less accounts), Delegate meta transactions wrapping
//! FunctionCalls (key `d3dl` of the honest accounts), CreateAccount + DeployContract +
//! FunctionCall bundles (code deployed and executed in the same receipt: nearcore does not
//! count it as a contract access), and calls / redeploys on the accounts those bundles create.

use crate::chaingen::Setup;
use crate::d2gen::{HONEST, World, key_signer};
use near_crypto::{PublicKey, Signer};
use near_primitives::action::delegate::{DelegateAction, NonDelegateAction, SignedDelegateAction};
use near_primitives::action::{
    Action, AddKeyAction, CreateAccountAction, DeployContractAction, FunctionCallAction, TransferAction,
};
use near_primitives::account::AccessKey;
use near_primitives::hash::CryptoHash;
use near_primitives::state_record::StateRecord;
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{AccountId, Balance, Gas};
use rand::Rng;
use rand::rngs::StdRng;
use std::collections::HashMap;

pub fn acct(s: &str) -> AccountId {
    s.parse().unwrap()
}
pub fn rich(k: usize) -> AccountId {
    acct(&format!("s{k}rc"))
}
pub fn ttn(k: usize, two: bool) -> AccountId {
    acct(&format!("s{k}ctr{}", if two { "2" } else { "" }))
}
pub fn ood_accounts(n_shards: usize) -> Vec<(AccountId, &'static str)> {
    vec![
        (acct("s0fl"), "d3float"),
        (acct(&format!("s{}cv", 1 % n_shards)), "d3curve"),
        (acct(&format!("s{}ed", 2 % n_shards)), "d3ed"),
    ]
}
/// the d3hostx account (shard 3 mod n)
pub fn hostx(n_shards: usize) -> AccountId {
    acct(&format!("s{}hx", 3 % n_shards))
}
/// an ETH-implicit account (`0x` + 40 hex) with the `Local` contract d3tiny
pub const ETH_LOCAL: &str = "0xd3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3";
pub fn dl_signer(a: &AccountId) -> Signer {
    key_signer(a, "d3dl")
}

/// Genesis records of the D3 contracts and keys. Returns (records, extra total supply).
pub fn genesis_records(accounts: &[Vec<AccountId>]) -> (Vec<StateRecord>, Balance) {
    use near_crypto::InMemorySigner;
    use near_primitives::account::AccountContract;
    use near_primitives_core::account::Account;
    let n = accounts.len();
    let mut r = Vec::new();
    let mut supply = Balance::ZERO;
    let mut add = |r: &mut Vec<StateRecord>, a: &AccountId, code: &[u8]| {
        let amount = Balance::from_near(1_000_000);
        r.push(StateRecord::Account {
            account_id: a.clone(),
            account: Account::new(amount, Balance::ZERO, AccountContract::Local(CryptoHash::hash_bytes(code)), 0),
        });
        r.push(StateRecord::access_key(a.clone(), &InMemorySigner::test_signer(a).public_key(), AccessKey::full_access()));
        r.push(StateRecord::Contract { account_id: a.clone(), code: code.to_vec() });
        supply = supply.checked_add(amount).unwrap();
    };
    for k in 0..n {
        add(&mut r, &rich(k), crate::d3contracts::RICH);
        for i in 0..6u8 {
            r.push(StateRecord::Data { account_id: rich(k), data_key: vec![b'a' + i].into(), value: vec![i; 1 + 30 * i as usize].into() });
        }
        for two in [false, true] {
            let c = ttn(k, two);
            add(&mut r, &c, crate::d3contracts::TTN2);
            for j in 0..64u8 {
                r.push(StateRecord::Data { account_id: c.clone(), data_key: vec![b'f', j].into(), value: vec![j; j as usize + 1].into() });
            }
            for j in (0..64u8).step_by(2) {
                let vlen = [1usize, 100, 4500][(j as usize / 2) % 3];
                r.push(StateRecord::Data { account_id: c.clone(), data_key: vec![b'k', j].into(), value: vec![j; vlen].into() });
            }
        }
    }
    for (a, name) in ood_accounts(n) {
        let code = crate::d3contracts::all().into_iter().find(|x| x.0 == name).unwrap().1;
        add(&mut r, &a, &code);
    }
    add(&mut r, &hostx(n), crate::d3contracts::HOSTX);
    add(&mut r, &acct(ETH_LOCAL), crate::d3contracts::TINY);
    // the D3 delegate key of every honest account
    for sh in accounts {
        for a in sh.iter().take(HONEST) {
            r.push(StateRecord::access_key(a.clone(), &dl_signer(a).public_key(), AccessKey::full_access()));
        }
    }
    (r, supply)
}

// ---------------------------------------------------------------------------------------------
// d3rich programs
// ---------------------------------------------------------------------------------------------

pub struct Prog<'a> {
    pub b: Vec<u8>,
    pub n_shards: usize,
    pub me: &'a AccountId,
    pub ctr: &'a mut u64,
    np: u8,
}

fn pk_bytes(pk: &PublicKey) -> Vec<u8> {
    borsh::to_vec(pk).unwrap()
}

impl<'a> Prog<'a> {
    pub fn new(me: &'a AccountId, n_shards: usize, ctr: &'a mut u64) -> Self {
        Prog { b: vec![], n_shards, me, ctr, np: 0 }
    }
    fn s(&mut self, x: &[u8]) {
        self.b.push(x.len().min(255) as u8);
        self.b.extend_from_slice(&x[..x.len().min(255)]);
    }
    fn big(&mut self, x: &[u8]) {
        self.b.extend_from_slice(&(x.len() as u16).to_le_bytes());
        self.b.extend_from_slice(x);
    }
    fn fresh(&mut self) -> u64 {
        *self.ctr += 1;
        *self.ctr
    }
    fn slot(&self, rng: &mut StdRng) -> u8 {
        if self.np == 0 || rng.gen_bool(0.03) { rng.gen_range(0..80) } else { rng.gen_range(0..self.np) }
    }
    fn push_slot(&mut self) {
        self.np = self.np.saturating_add(1);
    }
    fn key(rng: &mut StdRng) -> Vec<u8> {
        let k = [b"a".as_slice(), b"b", b"c", b"d", b"e", b"f", b"k0", b"zz", b"long-key-0123456789"][rng.gen_range(0..9)];
        k.to_vec()
    }
    fn other_rich(&self, rng: &mut StdRng) -> AccountId {
        rich(rng.gen_range(0..self.n_shards))
    }
    /// a callback program (reads promise results, sometimes forwards one, writes, logs)
    fn callback(&mut self, rng: &mut StdRng) -> Vec<u8> {
        let mut c = Prog::new(self.me, self.n_shards, &mut *self.ctr);
        c.b.push(0x17);
        if rng.gen_bool(0.5) {
            c.b.push(0x18);
        }
        if rng.gen_bool(0.5) {
            c.b.push(0x01);
            c.s(b"cb");
            c.b.extend_from_slice(&(rng.gen_range(1..200u16)).to_le_bytes());
            c.b.push(rng.r#gen());
        }
        if rng.gen_bool(0.1) {
            c.b.push(0x1b); // the callback panics
        }
        c.b
    }

    /// Append `n` random operations; `depth` bounds nested programs passed to promises.
    pub fn ops(&mut self, rng: &mut StdRng, n: usize, depth: u32) {
        for _ in 0..n {
            let r = rng.gen_range(0..100);
            match r {
                0..=11 => {
                    self.b.push(0x01);
                    self.s(&Self::key(rng));
                    let len: u16 = if rng.gen_bool(0.1) { rng.gen_range(1000..6000) } else { rng.gen_range(0..120) };
                    self.b.extend_from_slice(&len.to_le_bytes());
                    self.b.push(rng.r#gen());
                }
                12..=15 => {
                    self.b.push([0x02, 0x03, 0x04][rng.gen_range(0..3)]);
                    self.s(&Self::key(rng));
                }
                16..=21 => {
                    let m: Vec<u8> = match rng.gen_range(0..10) {
                        0 => vec![0xff, 0xfe, 0x41], // invalid UTF-8: BadUTF8
                        _ => format!("log {} ü", rng.gen_range(0..1000)).into_bytes(),
                    };
                    self.b.push(0x05);
                    self.s(&m);
                }
                22..=23 => {
                    // UTF-16 (odd length: BadUTF16)
                    let l = if rng.gen_bool(0.9) { 2 * rng.gen_range(1..8) } else { 3 };
                    self.b.push(0x06);
                    let v: Vec<u8> = (0..l).map(|i| if i % 2 == 0 { b'a' + (i as u8 % 26) } else { 0 }).collect();
                    self.s(&v);
                }
                24..=26 => {
                    self.b.push(0x07);
                    let v: Vec<u8> = (0..rng.gen_range(0..40)).map(|_| rng.r#gen()).collect();
                    self.s(&v);
                }
                27..=36 => {
                    self.b.push(0x19);
                    let sub = rng.gen_range(0..18u8);
                    self.b.push(sub);
                    if sub == 16 {
                        let a = if rng.gen_bool(0.5) { format!("s{}a00", rng.gen_range(0..self.n_shards)) } else { "nobody".into() };
                        self.s(a.as_bytes());
                    }
                }
                37..=40 => {
                    self.b.push(0x1a);
                    self.b.push(rng.gen_range(0..4));
                    let v: Vec<u8> = (0..rng.gen_range(0..100)).map(|_| rng.r#gen()).collect();
                    self.s(&v);
                }
                41..=42 => {
                    self.b.push(0x22);
                    let sub = if rng.gen_bool(0.85) { 0 } else { rng.gen_range(1..3) };
                    self.b.push(sub);
                    if sub == 0 {
                        self.s(b"register data");
                    }
                }
                43..=45 => {
                    self.b.push(0x1e);
                    self.b.extend_from_slice(&(rng.gen_range(1..40u16)).to_le_bytes());
                }
                46..=47 => {
                    self.b.push(0x27);
                    self.b.push(rng.gen_range(1..12));
                }
                48 => {
                    self.b.push(0x26);
                    self.b.push(if rng.gen_bool(0.5) { 1 } else { 255 });
                }
                49 => {
                    self.b.push(0x28);
                    self.b.push(rng.gen_range(1..4));
                }
                50..=61 if depth > 0 => {
                    // cross-contract call (+ callback)
                    let t = self.other_rich(rng);
                    let mut sub = Prog::new(self.me, self.n_shards, &mut *self.ctr);
                    let k = rng.gen_range(0..4);
                    sub.ops(rng, k, depth - 1);
                    let inner = sub.b;
                    self.b.push(0x08);
                    self.s(t.as_bytes());
                    self.s(if rng.gen_bool(0.95) { b"run" } else { b"missing_method" });
                    self.big(&inner);
                    self.b.push(if rng.gen_bool(0.7) { 0 } else { rng.gen_range(1..4) });
                    self.b.push(rng.gen_range(5..40));
                    self.push_slot();
                    if rng.gen_bool(0.6) {
                        let s = self.np - 1;
                        let cb = self.callback(rng);
                        self.b.push(0x09);
                        self.b.push(s);
                        self.s(self.me.clone().as_bytes());
                        self.s(b"cb");
                        self.big(&cb);
                        self.b.push(0);
                        self.b.push(rng.gen_range(5..20));
                        self.push_slot();
                    }
                }
                62..=65 if depth > 0 => {
                    // promise_and of two calls, then a callback with two inputs
                    for _ in 0..2 {
                        let t = self.other_rich(rng);
                        let mut sub = Prog::new(self.me, self.n_shards, &mut *self.ctr);
                        let k = rng.gen_range(0..3);
                        sub.ops(rng, k, 0);
                        let inner = sub.b;
                        self.b.push(0x08);
                        self.s(t.as_bytes());
                        self.s(b"run");
                        self.big(&inner);
                        self.b.push(0);
                        self.b.push(rng.gen_range(5..15));
                        self.push_slot();
                    }
                    self.b.push(0x0a);
                    self.b.push(2);
                    self.b.push(self.np - 2);
                    self.b.push(self.np - 1);
                    self.push_slot();
                    let s = self.np - 1;
                    let cb = self.callback(rng);
                    self.b.push(0x09);
                    self.b.push(s);
                    self.s(self.me.clone().as_bytes());
                    self.s(b"cb");
                    self.big(&cb);
                    self.b.push(0);
                    self.b.push(rng.gen_range(5..20));
                    self.push_slot();
                }
                66..=72 => {
                    // a batch on a fresh sub-account of this contract (any shard)
                    let t = rng.gen_range(0..self.n_shards);
                    let n = self.fresh();
                    let sub = acct(&format!("s{t}b{n}.{}", self.me));
                    self.b.push(0x0b);
                    self.s(sub.as_bytes());
                    self.push_slot();
                    let s = self.np - 1;
                    self.b.extend_from_slice(&[0x0f, s, 0x0e, s, if rng.gen_bool(0.8) { 4 } else { 3 }]);
                    self.b.extend_from_slice(&[0x10, s]);
                    self.b.extend(pk_bytes(&key_signer(&sub, "sub").public_key()));
                    if rng.gen_bool(0.3) {
                        self.b.extend_from_slice(&[0x14, s]);
                        self.b.extend(pk_bytes(&key_signer(&sub, "subfc").public_key()));
                        self.b.push(rng.gen_range(0..5));
                        self.s(self.me.clone().as_bytes());
                        self.s(b"run,cb");
                    }
                    if rng.gen_bool(0.4) {
                        self.b.extend_from_slice(&[0x11, s]);
                        if rng.gen_bool(0.7) {
                            self.b.extend_from_slice(&[0x0d, s]);
                            self.s(b"run");
                            self.big(b"hello");
                            self.b.push(0);
                            self.b.push(rng.gen_range(3..10));
                        }
                    }
                    if rng.gen_bool(0.15) {
                        self.b.extend_from_slice(&[0x15, s]);
                        self.s(self.me.clone().as_bytes());
                    }
                }
                73..=75 => {
                    // a batch on itself: AddKey + DeleteKey, a (failing) small Stake, a transfer
                    self.b.push(0x0b);
                    self.s(self.me.clone().as_bytes());
                    self.push_slot();
                    let s = self.np - 1;
                    let n = self.fresh();
                    let pk = pk_bytes(&key_signer(self.me, &format!("ck{n}")).public_key());
                    match rng.gen_range(0..3) {
                        0 => {
                            self.b.extend_from_slice(&[0x10, s]);
                            self.b.extend(&pk);
                            self.b.extend_from_slice(&[0x12, s]);
                            self.b.extend(&pk);
                        }
                        1 => {
                            self.b.extend_from_slice(&[0x13, s, rng.gen_range(1..5)]);
                            self.b.extend(&pk);
                        }
                        _ => {
                            self.b.extend_from_slice(&[0x12, s]);
                            self.b.extend(&pk);
                        }
                    }
                }
                76..=79 => {
                    // a batch: transfer (+ FunctionCall with weight) to an honest / missing account
                    let a = if rng.gen_bool(0.85) {
                        format!("s{}a0{}", rng.gen_range(0..self.n_shards), rng.gen_range(0..5))
                    } else {
                        format!("s{}nobody{}", rng.gen_range(0..self.n_shards), self.fresh())
                    };
                    let tgt = if rng.gen_bool(0.3) { self.other_rich(rng).to_string() } else { a };
                    self.b.push(0x0b);
                    self.s(tgt.as_bytes());
                    self.push_slot();
                    let s = self.np - 1;
                    self.b.extend_from_slice(&[0x0e, s, rng.gen_range(0..4)]);
                    if tgt.ends_with("rc") && rng.gen_bool(0.7) {
                        self.b.extend_from_slice(&[0x23, s]);
                        self.s(b"run");
                        let mut sub = Prog::new(self.me, self.n_shards, &mut *self.ctr);
                        let k = rng.gen_range(0..3);
                        sub.ops(rng, k, 0);
                        let inner = sub.b;
                        self.big(&inner);
                        self.b.push(0);
                        self.b.push(rng.gen_range(0..5));
                        self.b.push(rng.gen_range(1..4));
                    }
                }
                80..=81 if self.np > 0 => {
                    self.b.push(0x16);
                    let s = self.slot(rng);
                    self.b.push(s);
                }
                82 => {
                    // yield (callback `cb` with a program) / resume
                    if rng.gen_bool(0.5) {
                        self.b.push(0x24);
                        self.s(b"cb");
                        let cb = self.callback(rng);
                        self.big(&cb);
                        self.b.push(rng.gen_range(3..10));
                        self.b.push(rng.gen_range(0..2));
                        self.push_slot();
                    } else {
                        self.b.push(0x25);
                        self.s(b"resumed");
                    }
                }
                83 => {
                    // an adversarial promise index / invalid account id
                    if rng.gen_bool(0.5) {
                        self.b.extend_from_slice(&[0x0e, 200, 1]);
                    } else {
                        self.b.push(0x0b);
                        self.s(b"Invalid..Account");
                        self.push_slot();
                    }
                }
                _ => {
                    self.b.push(0x19);
                    self.b.push(rng.gen_range(0..14));
                }
            }
        }
    }

    /// a failure at the end (with probability p)
    pub fn maybe_fail(&mut self, rng: &mut StdRng, p: f64) {
        if !rng.gen_bool(p) {
            return;
        }
        match rng.gen_range(0..8) {
            0 => self.b.push(0x1b),
            1 => {
                self.b.push(0x1c);
                self.s(b"d3 panic");
            }
            2 => self.b.push(0x1d),
            3 => self.b.push(0x1f),
            4 => self.b.push(0x20),
            5 => self.b.push(0x21),
            6 => {
                self.b.push(0x28);
                self.b.push(255);
            }
            _ => {
                self.b.push(0x1e);
                self.b.extend_from_slice(&u16::MAX.to_le_bytes());
            }
        }
    }
}

/// ttn2 input (3-byte ops, `oracle/d3-ttn/ttn2.wat`)
fn ttn_prog(rng: &mut StdRng) -> Vec<u8> {
    let n = rng.gen_range(1..12);
    let mut v = Vec::new();
    for _ in 0..n {
        let op: u8 = rng.gen_range(0..8);
        v.push(op);
        v.push(rng.r#gen());
        // promises: few args, low gas
        v.push(if op == 4 || op == 5 { rng.gen_range(0..8) } else { rng.r#gen() });
    }
    v
}

// ---------------------------------------------------------------------------------------------
// transactions
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct Created {
    pub id: AccountId,
    pub signer: Signer,
    pub code: &'static str,
}

pub struct D3World {
    pub n_shards: usize,
    pub ctr: u64,
    pub created: Vec<Created>,
    nonces: HashMap<(AccountId, PublicKey), u64>,
}

fn fc(method: &str, args: Vec<u8>, gas: Gas, dep: u128) -> Action {
    Action::FunctionCall(Box::new(FunctionCallAction { method_name: method.into(), args, gas, deposit: Balance::from_yoctonear(dep) }))
}

fn deposit(rng: &mut StdRng) -> u128 {
    match rng.gen_range(0..6) {
        0 => 1,
        1 => 10u128.pow(21),
        2 => 10u128.pow(24) * rng.gen_range(1..5),
        _ => 0,
    }
}

impl D3World {
    pub fn new(n_shards: usize) -> Self {
        D3World { n_shards, ctr: 0, created: vec![], nonces: HashMap::new() }
    }

    fn next_nonce(&mut self, s: &Setup, bh: &CryptoHash, a: &AccountId, pk: &PublicKey) -> Option<u64> {
        let key = (a.clone(), pk.clone());
        if let Some(n) = self.nonces.get_mut(&key) {
            *n += 1;
            return Some(*n);
        }
        let cur = crate::d2gen::view_key(s, bh, a, pk)?.nonce;
        self.nonces.insert(key, cur + 1);
        Some(cur + 1)
    }

    fn program(&mut self, rng: &mut StdRng, me: &AccountId) -> Vec<u8> {
        let mut ctr = self.ctr;
        let mut p = Prog::new(me, self.n_shards, &mut ctr);
        let n = rng.gen_range(1..9);
        p.ops(rng, n, 2);
        p.maybe_fail(rng, 0.12);
        let b = p.b;
        self.ctr = ctr;
        b
    }

    fn honest(&self, rng: &mut StdRng) -> AccountId {
        acct(&format!("s{}a{:02}", rng.gen_range(0..self.n_shards), rng.gen_range(0..HONEST)))
    }

    /// One honest D3 transaction: (label, tx).
    pub fn one(&mut self, w: &mut World, s: &Setup, bh: &CryptoHash, height: u64, rng: &mut StdRng) -> Option<(String, SignedTransaction)> {
        let me = self.honest(rng);
        let k = rng.gen_range(0..self.n_shards);
        let c = rich(k);
        let gas = |rng: &mut StdRng| Gas::from_teragas(rng.gen_range(20..300));
        let kind = rng.gen_range(0..100);
        let (label, receiver, actions): (&str, AccountId, Vec<Action>) = match kind {
            0..=34 => {
                let p = self.program(rng, &c);
                ("d3.call", c, vec![fc("run", p, gas(rng), deposit(rng))])
            }
            35..=42 => {
                // multi-action: FunctionCall, Transfer, FunctionCall (both run on the same account)
                let p1 = self.program(rng, &c);
                let p2 = self.program(rng, &c);
                let mut acts = vec![fc("run", p1, Gas::from_teragas(rng.gen_range(10..120)), deposit(rng))];
                if rng.gen_bool(0.5) {
                    acts.push(Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(rng.gen_range(1..10u128.pow(22))) }));
                }
                acts.push(fc(if rng.gen_bool(0.9) { "run" } else { "noop" }, p2, Gas::from_teragas(rng.gen_range(10..120)), deposit(rng)));
                ("d3.call_multi", c, acts)
            }
            43..=48 => {
                // tight gas: a burn loop with little prepaid gas
                let mut ctr = self.ctr;
                let mut p = Prog::new(&c, self.n_shards, &mut ctr);
                p.ops(rng, 2, 1);
                p.b.push(0x1e);
                p.b.extend_from_slice(&(rng.gen_range(10..400u16)).to_le_bytes());
                p.ops(rng, 1, 0);
                let b = p.b;
                self.ctr = ctr;
                ("d3.call_tight_gas", c, vec![fc("run", b, Gas::from_gigagas(rng.gen_range(500..8000)), 0)])
            }
            49..=58 => {
                let two = rng.gen_bool(0.5);
                ("d3.call_ttn2", ttn(k, two), vec![fc("run", ttn_prog(rng), Gas::from_teragas(rng.gen_range(30..200)), 0)])
            }
            59..=60 => {
                // out-of-D3α contracts (floats, curve import) and the ed25519_verify contract
                let ood = ood_accounts(self.n_shards);
                let (a, _) = ood[rng.gen_range(0..ood.len())].clone();
                let args: Vec<u8> = (0..rng.gen_range(0..140)).map(|_| rng.r#gen()).collect();
                ("d3.call_ood_contract", a, vec![fc("run", args, Gas::from_teragas(20), 0)])
            }
            61..=63 => {
                // method resolution failures and a code-less receiver
                let (m, r) = match rng.gen_range(0..4) {
                    0 => ("missing", c.clone()),
                    1 => ("bad_sig", c.clone()),
                    2 => ("noop", c.clone()),
                    _ => ("run", self.honest(rng)),
                };
                ("d3.call_method_edge", r, vec![fc(m, vec![1, 2, 3], Gas::from_teragas(10), 0)])
            }
            64..=71 => {
                // CreateAccount + Transfer + AddKey + DeployContract (+ FunctionCall): deployed and
                // called in one receipt (the code comes from the receipt, not from the state)
                let t = rng.gen_range(0..self.n_shards);
                self.ctr += 1;
                let sub = acct(&format!("s{t}k{}.{me}", self.ctr));
                let ks = key_signer(&sub, "d3sub");
                let (cname, code) = match rng.gen_range(0..3) {
                    0 => ("d3tiny", crate::d3contracts::TINY.to_vec()),
                    1 => ("ttn2", crate::d3contracts::TTN2.to_vec()),
                    _ => ("d3rich", crate::d3contracts::RICH.to_vec()),
                };
                let mut acts = vec![
                    Action::CreateAccount(CreateAccountAction {}),
                    Action::Transfer(TransferAction { deposit: Balance::from_near(rng.gen_range(5..50)) }),
                    Action::AddKey(Box::new(AddKeyAction { public_key: ks.public_key(), access_key: AccessKey::full_access() })),
                    Action::DeployContract(DeployContractAction { code }),
                ];
                if rng.gen_bool(0.7) {
                    let args = if cname == "d3rich" {
                        self.program(rng, &sub)
                    } else if cname == "ttn2" {
                        // ttn2's promises target s<k>ctr: storage ops only here
                        (0..rng.gen_range(1..6)).flat_map(|_| [rng.gen_range(0..4u8), rng.r#gen(), rng.r#gen()]).collect()
                    } else {
                        b"deployed".to_vec()
                    };
                    acts.push(fc("run", args, Gas::from_teragas(rng.gen_range(20..150)), 0));
                }
                self.created.push(Created { id: sub.clone(), signer: ks, code: cname });
                ("d3.create_deploy_call", sub, acts)
            }
            72..=79 => {
                // a call to a contract account created earlier (its code is in the state now)
                if self.created.is_empty() {
                    return None;
                }
                let x = self.created[rng.gen_range(0..self.created.len())].clone();
                let args = match x.code {
                    "d3rich" => self.program(rng, &x.id),
                    "ttn2" => (0..rng.gen_range(1..6)).flat_map(|_| [rng.gen_range(0..4u8), rng.r#gen(), rng.r#gen()]).collect(),
                    _ => b"again".to_vec(),
                };
                ("d3.call_created", x.id, vec![fc("run", args, Gas::from_teragas(rng.gen_range(20..150)), deposit(rng))])
            }
            80..=84 => {
                // a created account redeploys (another code) and calls itself in one transaction,
                // or calls itself only
                if self.created.is_empty() {
                    return None;
                }
                let i = rng.gen_range(0..self.created.len());
                let x = self.created[i].clone();
                let mut acts = Vec::new();
                let mut code_name = x.code;
                if rng.gen_bool(0.6) {
                    let (n, code) = match rng.gen_range(0..3) {
                        0 => ("d3tiny", crate::d3contracts::TINY.to_vec()),
                        1 => ("d3rich", crate::d3contracts::RICH.to_vec()),
                        _ => ("d2program", crate::d2gen::program_wasm().to_vec()),
                    };
                    code_name = n;
                    acts.push(Action::DeployContract(DeployContractAction { code }));
                }
                let args = if code_name == "d3rich" { self.program(rng, &x.id) } else { b"self".to_vec() };
                acts.push(fc("run", args, Gas::from_teragas(rng.gen_range(20..150)), 0));
                let n = self.next_nonce(s, bh, &x.id, &x.signer.public_key())?;
                let t = SignedTransaction::from_actions(n, x.id.clone(), x.id.clone(), &x.signer, acts, *bh);
                self.created[i].code = code_name;
                return Some(("d3.redeploy_call".into(), t));
            }
            85..=87 => {
                // d3hostx: an import-only call (in D3α) or a call of an excluded host function /
                // an ML-DSA-65 key action (out of D3α)
                let r = rng.gen_range(0..100);
                let (label, m, args): (&str, &str, Vec<u8>) = match r {
                    0..=39 => ("d3.hostx_import_only", "run", (0..rng.gen_range(0..64)).map(|_| rng.r#gen()).collect()),
                    40..=49 => ("d3.hostx_curve_call", "curve", vec![]),
                    50..=59 => ("d3.hostx_global_call", "glob", vec![]),
                    60..=69 => ("d3.hostx_state_init_call", "stinit", vec![]),
                    70..=79 => {
                        self.ctr += 1;
                        let pk = key_signer(&hostx(self.n_shards), &format!("gk{}", self.ctr)).public_key();
                        ("d3.hostx_gas_key_call", "gaskey", borsh::to_vec(&pk).unwrap())
                    }
                    _ => {
                        // ML-DSA-65: borsh = key type 2 ‖ 1952 bytes
                        self.ctr += 1;
                        let pk = PublicKey::from_seed(near_crypto::KeyType::MLDSA65, &format!("d3mldsa{}", self.ctr));
                        let op = rng.gen_range(0..3u8);
                        let mut a = vec![op];
                        a.extend(borsh::to_vec(&pk).unwrap());
                        (["d3.hostx_mldsa_add_key", "d3.hostx_mldsa_stake", "d3.hostx_mldsa_delete_key"][op as usize], "mlkey", a)
                    }
                };
                (label, hostx(self.n_shards), vec![fc(m, args, Gas::from_teragas(rng.gen_range(30..80)), 0)])
            }
            88 => {
                // an ETH-implicit account with a Local contract (out of D3α, P5)
                ("d3.call_eth_implicit_local", acct(ETH_LOCAL), vec![fc("run", b"eth".to_vec(), Gas::from_teragas(20), 0)])
            }
            _ => return self.delegate(w, s, bh, height, rng),
        };
        let t = w.plain_tx(s, bh, &me, &receiver, actions)?;
        Some((label.to_string(), t))
    }

    /// A Delegate meta transaction wrapping FunctionCalls (relayer: an honest account; sender:
    /// another honest account signing with its `d3dl` key).
    fn delegate(&mut self, w: &mut World, s: &Setup, bh: &CryptoHash, height: u64, rng: &mut StdRng) -> Option<(String, SignedTransaction)> {
        let relayer = self.honest(rng);
        let sender = self.honest(rng);
        let ss = dl_signer(&sender);
        let k = rng.gen_range(0..self.n_shards);
        let (receiver, label) = if !self.created.is_empty() && rng.gen_bool(0.2) {
            (self.created[rng.gen_range(0..self.created.len())].id.clone(), "d3.delegate_call_created")
        } else {
            (rich(k), "d3.delegate_call")
        };
        let mut inner = Vec::new();
        for _ in 0..rng.gen_range(1..3) {
            let p = self.program(rng, &receiver);
            inner.push(fc("run", p, Gas::from_teragas(rng.gen_range(10..100)), deposit(rng)));
        }
        if rng.gen_bool(0.3) {
            inner.push(Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(rng.gen_range(1..10u128.pow(21))) }));
        }
        let nonce = self.next_nonce(s, bh, &sender, &ss.public_key())?;
        let da = DelegateAction {
            sender_id: sender.clone(),
            receiver_id: receiver,
            actions: inner.into_iter().map(|a| NonDelegateAction::try_from(a).unwrap()).collect(),
            nonce,
            max_block_height: height + 100,
            public_key: ss.public_key(),
        };
        let sda = SignedDelegateAction::sign(&ss, da);
        let t = w.plain_tx(s, bh, &relayer, &sender, vec![Action::Delegate(Box::new(sda))])?;
        Some((label.into(), t))
    }
}
