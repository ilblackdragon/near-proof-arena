//! Deterministic case generator (valid in-domain cases and out-of-domain
//! rejection cases). All randomness comes from a SplitMix64 stream seeded by
//! (seed, case index), so a case is reproducible from its id alone.

use borsh::BorshDeserialize;
use near_crypto::PublicKey;
use near_primitives::account::{AccessKey, Account, AccountContract};
use near_primitives::hash::CryptoHash;
use near_primitives::receipt::{ActionReceipt, Receipt, ReceiptEnum, ReceiptV0};
use near_primitives::transaction::{Action, TransferAction, StakeAction};
use near_primitives::trie_key::TrieKey;
use near_primitives::types::{AccountId, Balance};
use std::collections::BTreeMap;

use crate::domain::{self, GAS_PER_TRANSFER, STORAGE_AMOUNT_PER_BYTE};
use crate::enc::Request;

pub struct Rng(u64);
impl Rng {
    pub fn new(seed: u64, idx: u64) -> Self {
        let mut r = Rng(seed ^ 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(idx.wrapping_add(1)));
        r.next();
        r
    }
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
    pub fn range(&mut self, lo: u64, hi_incl: u64) -> u64 {
        lo + self.below(hi_incl - lo + 1)
    }
    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
    pub fn u128(&mut self) -> u128 {
        ((self.next() as u128) << 64) | self.next() as u128
    }
    pub fn u128_below(&mut self, n: u128) -> u128 {
        if n == 0 { 0 } else { self.u128() % n }
    }
    pub fn bytes32(&mut self) -> [u8; 32] {
        let mut b = [0u8; 32];
        for c in b.chunks_mut(8) {
            c.copy_from_slice(&self.next().to_le_bytes());
        }
        b
    }
    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

pub(crate) const ALNUM: &[u8] = b"abcdefghijklmnopqrstuvwxyz0123456789";
pub(crate) const HEX: &[u8] = b"0123456789abcdef";
const SEP: &[u8] = b"-_.";

/// A random syntactically valid account id of exactly `len` bytes (2..=64).
pub(crate) fn raw_valid_id(rng: &mut Rng, len: usize) -> String {
    let mut s = Vec::with_capacity(len);
    let mut prev_sep = true;
    for i in 0..len {
        let last = i + 1 == len;
        let c = if !prev_sep && !last && i > 0 && rng.chance(1, 6) {
            *rng.pick(SEP)
        } else {
            *rng.pick(ALNUM)
        };
        prev_sep = SEP.contains(&c);
        s.push(c);
    }
    String::from_utf8(s).unwrap()
}

pub fn is_named(s: &str) -> bool {
    match s.parse::<AccountId>() {
        Ok(a) => a.get_account_type() == near_primitives::account::id::AccountType::NamedAccount,
        Err(_) => false,
    }
}

/// Named account ids, including adversarial near-misses of the implicit forms.
pub fn named_id(rng: &mut Rng) -> String {
    loop {
        let s = match rng.below(10) {
            0 => {
                // 64 chars, hex except one non-hex alnum (NOT near-implicit)
                let mut v: Vec<u8> = (0..64).map(|_| *rng.pick(HEX)).collect();
                let i = rng.below(64) as usize;
                v[i] = *rng.pick(b"ghijklmnopqrstuvwxyz");
                String::from_utf8(v).unwrap()
            }
            1 => {
                // "0x" + 39 or 41 hex (NOT eth-implicit), or 0x + 40 with a non-hex
                let n = *rng.pick(&[39usize, 41, 40]);
                let mut v: Vec<u8> = b"0x".to_vec();
                v.extend((0..n).map(|_| *rng.pick(HEX)));
                if n == 40 {
                    let i = 2 + rng.below(40) as usize;
                    v[i] = b'z';
                }
                String::from_utf8(v).unwrap()
            }
            2 => {
                let mut v: Vec<u8> = b"0s".to_vec();
                v.extend((0..40).map(|_| *rng.pick(HEX)));
                v[2 + rng.below(40) as usize] = b'y';
                String::from_utf8(v).unwrap()
            }
            3 => { let l = *rng.pick(&[2usize, 3, 63, 64]); raw_valid_id(rng, l) }
            4 => format!("{}.near", { let l = rng.range(2, 20) as usize; raw_valid_id(rng, l) }),
            5 => format!("{}.tg", { let l = rng.range(2, 12) as usize; raw_valid_id(rng, l) }),
            _ => {
                let len = rng.range(2, 64) as usize;
                raw_valid_id(rng, len)
            }
        };
        if is_named(&s) {
            return s;
        }
    }
}

/// A family of ids sharing a prefix; some ids are byte-prefixes of others,
/// producing branch-with-value and extension nodes.
fn prefix_family(rng: &mut Rng, n: usize) -> Vec<String> {
    let base = { let l = rng.range(2, 8) as usize; raw_valid_id(rng, l) };
    let mut out = vec![base.clone()];
    while out.len() < n {
        let p = rng.pick(&out).clone();
        let s = match rng.below(4) {
            0 => format!("{p}{}", *rng.pick(ALNUM) as char),
            1 => { let sc = *rng.pick(SEP) as char; format!("{p}{}{}", sc, { let l = rng.range(1, 4).max(2) as usize; raw_valid_id(rng, l) }) }
            2 => {
                // same prefix, differ in the last char (sibling)
                let mut v = p.clone().into_bytes();
                let l = v.len() - 1;
                v[l] = *rng.pick(ALNUM);
                String::from_utf8(v).unwrap()
            }
            _ => format!("{p}{}", { let l = rng.range(2, 6) as usize; raw_valid_id(rng, l) }),
        };
        if s.len() <= 64 && is_named(&s) && !out.contains(&s) {
            out.push(s);
        }
    }
    out
}

pub fn any_valid_id(rng: &mut Rng) -> AccountId {
    // predecessor/signer: any valid id except "system" (implicit allowed).
    loop {
        let s = match rng.below(5) {
            0 => (0..64).map(|_| *rng.pick(HEX) as char).collect::<String>(),
            1 => format!("0x{}", (0..40).map(|_| *rng.pick(HEX) as char).collect::<String>()),
            _ => named_id(rng),
        };
        if s != "system" {
            if let Ok(a) = s.parse() {
                return a;
            }
        }
    }
}

pub fn random_pk(rng: &mut Rng) -> PublicKey {
    let mut b = vec![];
    if rng.chance(3, 4) {
        b.push(0u8);
        b.extend_from_slice(&rng.bytes32());
    } else {
        b.push(1u8);
        b.extend_from_slice(&rng.bytes32());
        b.extend_from_slice(&rng.bytes32());
    }
    PublicKey::try_from_slice(&b).unwrap()
}

pub struct StateBuilder {
    pub kv: BTreeMap<Vec<u8>, Vec<u8>>,
}

impl StateBuilder {
    pub fn new() -> Self {
        StateBuilder { kv: BTreeMap::new() }
    }
    pub fn put_account(&mut self, id: &str, a: &Account) {
        self.kv.insert(domain::account_key(id), borsh::to_vec(a).unwrap());
    }
    pub fn put_raw(&mut self, k: Vec<u8>, v: Vec<u8>) {
        self.kv.insert(k, v);
    }
    pub fn account_amount(&self, id: &str) -> Option<(u128, u128)> {
        let v = self.kv.get(&domain::account_key(id))?;
        Some((
            u128::from_le_bytes(v[0..16].try_into().unwrap()),
            u128::from_le_bytes(v[16..32].try_into().unwrap()),
        ))
    }
}

/// A random AccountV1 that satisfies the storage-stake invariant.
pub(crate) fn random_account(rng: &mut Rng, boundary: bool) -> Account {
    let code = if rng.chance(1, 5) {
        AccountContract::Local(CryptoHash(rng.bytes32()))
    } else {
        AccountContract::None
    };
    let (amount, locked, su) = match rng.below(if boundary { 3 } else { 6 }) {
        0 => {
            // near u128::MAX (headroom handled by the deposit generator)
            let sh = rng.range(0, 90); let headroom = rng.u128_below(1u128 << sh);
            (u128::MAX - 1 - headroom, 0, rng.range(0, 5000))
        }
        1 => (0, 0, rng.range(0, 770)), // zero-balance account
        2 => {
            let su = rng.range(771, 100_000);
            let need = STORAGE_AMOUNT_PER_BYTE * su as u128;
            let locked = if rng.chance(1, 3) { rng.u128_below(need) } else { 0 };
            (need - locked + rng.u128_below(1u128 << 80), locked, su)
        }
        _ => {
            let su = rng.range(100, 2000);
            let need = STORAGE_AMOUNT_PER_BYTE * su as u128;
            (need + rng.u128_below(1_000_000u128 * 10u128.pow(24)), 0, su)
        }
    };
    Account::new(Balance::from_yoctonear(amount), Balance::from_yoctonear(locked), code, su)
}

pub struct Case {
    pub id: String,
    pub profile: String,
    pub request: Request,
    pub state: BTreeMap<Vec<u8>, Vec<u8>>,
    /// For out-of-domain cases: which restriction is violated (expected).
    pub invalid_kind: Option<String>,
}

pub const PROFILES: &[&str] = &["basic", "prefix", "boundary", "repeat", "prices", "large"];

pub const INVALID_KINDS: &[&str] = &[
    "receiver_missing",
    "balance_overflow",
    "sentinel_balance",
    "storage_stake",
    "implicit_receiver",
    "system_predecessor",
    "multi_action",
    "non_transfer_action",
    "gas_limit",
    "duplicate_receipt_id",
    "account_v2",
    "tokens_burnt_overflow",
    "wrong_protocol_version",
    "empty_batch",
];

pub(crate) fn transfer_receipt(
    rng: &mut Rng,
    receiver: &str,
    deposit: u128,
    gas_price: u128,
) -> Receipt {
    let pred = any_valid_id(rng);
    let signer = if rng.chance(4, 5) { pred.clone() } else { any_valid_id(rng) };
    Receipt::V0(ReceiptV0 {
        predecessor_id: pred,
        receiver_id: receiver.parse().unwrap(),
        receipt_id: CryptoHash(rng.bytes32()),
        receipt: ReceiptEnum::Action(ActionReceipt {
            signer_id: signer,
            signer_public_key: random_pk(rng),
            gas_price: Balance::from_yoctonear(gas_price),
            output_data_receivers: vec![],
            input_data_ids: vec![],
            actions: vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(deposit) })],
        }),
    })
}

fn add_noise_keys(rng: &mut Rng, sb: &mut StateBuilder, ids: &[String]) {
    // Access keys and contract data for some accounts, plus a few untouched
    // accounts, so the trie has realistic branching in other columns.
    for id in ids {
        let aid: AccountId = id.parse().unwrap();
        if rng.chance(2, 3) {
            let pk = random_pk(rng);
            let k = TrieKey::AccessKey { account_id: aid.clone(), key_handle: pk.into() }.to_vec();
            sb.put_raw(k, borsh::to_vec(&AccessKey::full_access()).unwrap());
        }
        if rng.chance(1, 4) {
            for _ in 0..rng.range(1, 3) {
                let key: Vec<u8> = (0..rng.range(1, 12)).map(|_| rng.next() as u8).collect();
                let k = TrieKey::ContractData { account_id: aid.clone(), key }.to_vec();
                let v: Vec<u8> = (0..rng.range(0, 100)).map(|_| rng.next() as u8).collect();
                sb.put_raw(k, v);
            }
        }
    }
}

const PRICE_TIERS: &[u128] = &[0, 100_000_000, 1_000_000_000, 2_000_000_000, 7, 1];

fn price(rng: &mut Rng) -> u128 {
    match rng.below(6) {
        0..=2 => *rng.pick(PRICE_TIERS),
        3 => rng.u128_below(10_000_000_000_000),
        4 => rng.u128_below(u128::MAX / GAS_PER_TRANSFER as u128 / 300),
        _ => 1_000_000_000,
    }
}

/// Generate an in-domain case. Retries internally until the Rust domain
/// check accepts (rarely needed: only tokens_burnt_total overflow).
/// When non-zero, every generated valid case has exactly this many receipts.
pub static FORCE_RECEIPTS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

pub fn gen_valid(seed: u64, idx: u64, profile: &str) -> Case {
    for attempt in 0.. {
        let mut rng = Rng::new(seed, idx.wrapping_mul(1000).wrapping_add(attempt));
        let c = gen_valid_once(&mut rng, seed, idx, profile);
        if domain::check(&c.request, &c.state, 0).is_ok() {
            return c;
        }
    }
    unreachable!()
}

fn gen_valid_once(rng: &mut Rng, seed: u64, idx: u64, profile: &str) -> Case {
    let mut sb = StateBuilder::new();
    let n_accounts = match profile {
        "large" => rng.range(20, 200),
        "prefix" => rng.range(4, 40),
        _ => rng.range(2, 40),
    } as usize;
    let mut ids: Vec<String> = if profile == "prefix" || rng.chance(1, 4) {
        let mut v = prefix_family(rng, n_accounts.min(30));
        while v.len() < n_accounts {
            let s = named_id(rng);
            if !v.contains(&s) { v.push(s); }
        }
        v
    } else {
        let mut v = vec![];
        while v.len() < n_accounts {
            let s = named_id(rng);
            if !v.contains(&s) { v.push(s); }
        }
        v
    };
    ids.sort();
    for id in &ids {
        let a = random_account(rng, profile == "boundary");
        sb.put_account(id, &a);
    }
    add_noise_keys(rng, &mut sb, &ids);
    // a few non-receiver implicit accounts (exist in state, never receive)
    for _ in 0..rng.range(0, 3) {
        let h: String = (0..64).map(|_| *rng.pick(HEX) as char).collect();
        sb.put_account(&h, &random_account(rng, false));
    }

    let mut n = match profile {
        "large" => rng.range(64, domain::MAX_BATCH as u64),
        "repeat" => rng.range(4, 40),
        _ => rng.range(1, 16),
    } as usize;
    let forced = FORCE_RECEIPTS.load(std::sync::atomic::Ordering::Relaxed);
    if forced > 0 {
        n = forced; // workload classes with a fixed receipt count (--receipts N)
    }
    let block_gas_price = match profile {
        "prices" => price(rng),
        _ => *rng.pick(&[100_000_000u128, 1_000_000_000, 1_000_000_000, 500_000_000]),
    };
    let receivers: Vec<String> = if profile == "repeat" {
        let k = rng.range(1, 3) as usize;
        let hot: Vec<String> = (0..k).map(|_| rng.pick(&ids).clone()).collect();
        (0..n).map(|_| if rng.chance(4, 5) { rng.pick(&hot).clone() } else { rng.pick(&ids).clone() }).collect()
    } else {
        (0..n).map(|_| rng.pick(&ids).clone()).collect()
    };
    // pending balances to keep deposits inside the overflow headroom
    let mut cur: BTreeMap<String, (u128, u128)> = BTreeMap::new();
    let mut receipts = vec![];
    for recv in &receivers {
        let (amt, locked) = *cur.entry(recv.clone()).or_insert_with(|| sb.account_amount(recv).unwrap());
        // new amount must be <= MAX-1 and amount+locked <= MAX
        let headroom = (u128::MAX - 1 - amt).min(u128::MAX - amt - locked);
        let deposit = match rng.below(if profile == "boundary" { 3 } else { 8 }) {
            0 => 0,
            1 => headroom.min(rng.u128_below(headroom.saturating_add(1)) / 2),
            2 => {
                // max deposit, but leave room for later receipts to the same receiver
                let later = receivers.iter().filter(|r| *r == recv).count() as u128;
                if later <= 1 { headroom } else { headroom / (2 * later) }
            }
            _ => rng.u128_below(headroom.min(1_000u128 * 10u128.pow(24)).saturating_add(1)),
        };
        cur.insert(recv.clone(), (amt + deposit, locked));
        let gp = match profile {
            "prices" => price(rng),
            _ => *rng.pick(&[1_000_000_000u128, 1_000_000_000, 100_000_000, 2_000_000_000]),
        };
        receipts.push(transfer_receipt(rng, recv, deposit, gp));
    }
    let request = Request {
        protocol_version: domain::PROTOCOL_VERSION,
        chain_id: domain::CHAIN_ID.into(),
        shard_id: 0,
        block_height: { let sh = rng.range(1, 60); rng.range(1, u64::MAX >> sh) },
        block_gas_price,
        gas_limit: if profile == "boundary" && rng.chance(1, 2) {
            // tightest in-domain compute limit: (n-1)*G < gas_limit
            (n as u64 - 1) * GAS_PER_TRANSFER + 1
        } else {
            1_000_000_000_000_000
        },
        pre_state_root: CryptoHash::default(), // filled in by exec
        receipts,
    };
    let id = match FORCE_RECEIPTS.load(std::sync::atomic::Ordering::Relaxed) {
        0 => format!("s{seed}-v{idx}"),
        r => format!("s{seed}-r{r}-v{idx}"),
    };
    Case { id, profile: profile.into(), request, state: sb.kv, invalid_kind: None }
}

/// Generate an out-of-domain case of the given kind, starting from a valid case.
pub fn gen_invalid(seed: u64, idx: u64, kind: &str) -> Case {
    let base_profile = PROFILES[(idx as usize) % 5];
    let mut c = gen_valid(seed, idx, base_profile);
    let mut rng = Rng::new(seed ^ 0xDEAD_BEEF, idx);
    c.id = format!("s{seed}-x{idx}-{kind}");
    c.invalid_kind = Some(kind.into());
    let n = c.request.receipts.len();
    let j = rng.below(n as u64) as usize;
    let recv = c.request.receipts[j].receiver_id().to_string();
    let set_deposit = |r: &mut Receipt, d: u128| {
        let Receipt::V0(v0) = r;
        let ReceiptEnum::Action(a) = &mut v0.receipt else { unreachable!() };
        a.actions[0] = Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(d) });
    };
    match kind {
        "receiver_missing" => {
            let mut s = named_id(&mut rng);
            while c.state.contains_key(&domain::account_key(&s)) { s = named_id(&mut rng); }
            let Receipt::V0(v0) = &mut c.request.receipts[j];
            v0.receiver_id = s.parse().unwrap();
        }
        "balance_overflow" | "sentinel_balance" | "storage_stake" | "tokens_burnt_overflow" => {
            // make receipt j the only receipt to its receiver to control the arithmetic
            let key = domain::account_key(&recv);
            let mut v = c.state[&key].clone();
            let locked = u128::from_le_bytes(v[16..32].try_into().unwrap());
            match kind {
                "balance_overflow" => {
                    v[0..16].copy_from_slice(&(u128::MAX - 5).to_le_bytes());
                    c.state.insert(key, v);
                    set_deposit(&mut c.request.receipts[j], 10);
                }
                "sentinel_balance" => {
                    v[0..16].copy_from_slice(&(u128::MAX - 5).to_le_bytes());
                    v[16..32].copy_from_slice(&0u128.to_le_bytes());
                    c.state.insert(key, v);
                    set_deposit(&mut c.request.receipts[j], 5);
                    // only one receipt may hit this receiver
                    let rid = *c.request.receipts[j].receipt_id();
                    c.request.receipts.retain(|r| r.receiver_id().as_str() != recv || *r.receipt_id() == rid);
                    let _ = locked;
                }
                "storage_stake" => {
                    v[0..16].copy_from_slice(&0u128.to_le_bytes());
                    v[16..32].copy_from_slice(&0u128.to_le_bytes());
                    v[64..72].copy_from_slice(&5000u64.to_le_bytes());
                    c.state.insert(key, v);
                    let rid = *c.request.receipts[j].receipt_id();
                    c.request.receipts.retain(|r| r.receiver_id().as_str() != recv || *r.receipt_id() == rid);
                    let jj = c.request.receipts.iter().position(|r| *r.receipt_id() == rid).unwrap();
                    set_deposit(&mut c.request.receipts[jj], 1);
                }
                _ => {
                    // tokens_burnt_total overflow: two receipts each burning ~MAX/2+
                    let p = u128::MAX / GAS_PER_TRANSFER as u128;
                    c.request.block_gas_price = p;
                    for r in c.request.receipts.iter_mut() {
                        let Receipt::V0(v0) = r;
                        let ReceiptEnum::Action(a) = &mut v0.receipt else { unreachable!() };
                        a.gas_price = Balance::from_yoctonear(p);
                    }
                    if c.request.receipts.len() < 2 {
                        let mut r2 = c.request.receipts[0].clone();
                        let Receipt::V0(v0) = &mut r2;
                        v0.receipt_id = CryptoHash(rng.bytes32());
                        set_deposit(&mut r2, 0);
                        c.request.receipts.push(r2);
                    }
                }
            }
        }
        "implicit_receiver" => {
            let h: String = match rng.below(3) {
                0 => (0..64).map(|_| *rng.pick(HEX) as char).collect(),
                1 => format!("0x{}", (0..40).map(|_| *rng.pick(HEX) as char).collect::<String>()),
                _ => format!("0s{}", (0..40).map(|_| *rng.pick(HEX) as char).collect::<String>()),
            };
            let a = Account::new(Balance::from_yoctonear(10u128.pow(24)), Balance::ZERO, AccountContract::None, 182);
            c.state.insert(domain::account_key(&h), borsh::to_vec(&a).unwrap());
            let Receipt::V0(v0) = &mut c.request.receipts[j];
            v0.receiver_id = h.parse().unwrap();
        }
        "system_predecessor" => {
            let Receipt::V0(v0) = &mut c.request.receipts[j];
            v0.predecessor_id = "system".parse().unwrap();
        }
        "multi_action" => {
            let Receipt::V0(v0) = &mut c.request.receipts[j];
            let ReceiptEnum::Action(a) = &mut v0.receipt else { unreachable!() };
            a.actions.push(Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(1) }));
        }
        "non_transfer_action" => {
            let Receipt::V0(v0) = &mut c.request.receipts[j];
            let ReceiptEnum::Action(a) = &mut v0.receipt else { unreachable!() };
            a.actions[0] = Action::Stake(Box::new(StakeAction {
                stake: Balance::ZERO,
                public_key: random_pk(&mut rng),
            }));
        }
        "gas_limit" => {
            while c.request.receipts.len() < 3 {
                let mut r2 = c.request.receipts[0].clone();
                let Receipt::V0(v0) = &mut r2;
                v0.receipt_id = CryptoHash(rng.bytes32());
                set_deposit(&mut r2, 0);
                c.request.receipts.push(r2);
            }
            let n = c.request.receipts.len() as u64;
            c.request.gas_limit = (n - 1) * GAS_PER_TRANSFER - rng.below(GAS_PER_TRANSFER);
        }
        "duplicate_receipt_id" => {
            let mut r2 = c.request.receipts[j].clone();
            set_deposit(&mut r2, 0);
            c.request.receipts.push(r2);
        }
        "account_v2" => {
            let a = Account::new(
                Balance::from_yoctonear(10u128.pow(24)),
                Balance::ZERO,
                AccountContract::GlobalByAccount(recv.parse().unwrap()),
                182,
            );
            c.state.insert(domain::account_key(&recv), borsh::to_vec(&a).unwrap());
        }
        "wrong_protocol_version" => c.request.protocol_version = 85,
        "empty_batch" => c.request.receipts.clear(),
        other => panic!("unknown invalid kind {other}"),
    }
    let _ = n;
    c
}

/// The worked example of docs/research/first-slice.md §6 (alice/bob/carol),
/// `tier` = "A" (block price == receipt price, no refunds) or "B" (block price
/// 1e8 < receipt price 1e9, one gas refund per receipt).
pub fn example_case(tier: &str) -> Case {
    use near_primitives::hash::hash;
    let pk: PublicKey = "ed25519:6E8sCci9badyRkXb3JoRpBj5p8C6Tw41ELDZoiihKEtp".parse().unwrap();
    let mut sb = StateBuilder::new();
    let near = 10u128.pow(24);
    for (name, amt) in [("alice.near", 100u128), ("bob.near", 50), ("carol.near", 7)] {
        let a = Account::new(Balance::from_yoctonear(amt * near), Balance::ZERO, AccountContract::None, 182);
        sb.put_account(name, &a);
        let k = TrieKey::AccessKey { account_id: name.parse().unwrap(), key_handle: (&pk).into() }.to_vec();
        sb.put_raw(k, borsh::to_vec(&AccessKey::full_access()).unwrap());
    }
    let mk = |seed: &str, from: &str, to: &str, dep: u128| {
        Receipt::V0(ReceiptV0 {
            predecessor_id: from.parse().unwrap(),
            receiver_id: to.parse().unwrap(),
            receipt_id: hash(seed.as_bytes()),
            receipt: ReceiptEnum::Action(ActionReceipt {
                signer_id: from.parse().unwrap(),
                signer_public_key: pk.clone(),
                gas_price: Balance::from_yoctonear(1_000_000_000),
                output_data_receivers: vec![],
                input_data_ids: vec![],
                actions: vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(dep) })],
            }),
        })
    };
    let receipts = vec![
        mk("r1", "alice.near", "bob.near", 3 * near),
        mk("r2", "bob.near", "carol.near", 1500 * 10u128.pow(21)),
    ];
    let request = Request {
        protocol_version: domain::PROTOCOL_VERSION,
        chain_id: domain::CHAIN_ID.into(),
        shard_id: 0,
        block_height: 10,
        block_gas_price: if tier == "A" { 1_000_000_000 } else { 100_000_000 },
        gas_limit: 1_000_000_000_000_000,
        pre_state_root: CryptoHash::default(),
        receipts,
    };
    Case { id: format!("example-tier{tier}"), profile: "example".into(), request, state: sb.kv, invalid_kind: None }
}
