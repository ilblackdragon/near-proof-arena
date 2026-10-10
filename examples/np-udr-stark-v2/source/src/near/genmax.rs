//! Maximum-size in-domain workload generator (`npudr gen-max`).
//!
//! Synthesizes a valid `request.bin` / `witness.bin` (`spec/claim-v1.md`)
//! whose honest `nearAir` trace is as tall as the domain allows, plus the
//! expected `claim.bin` from an independent derivation (this module's own
//! tree, `spec::{outcome_root, refunds_commitment, …}`), cross-checked against
//! the reexec engine (`deriveClaim`).
//!
//! # Shape (why it is the worst case)
//!
//! The honest trace prunes the witness to the touched paths, so every revealed
//! node is hashed twice by the `sha` table (pre and post), costing
//! `2·(1 + 17·⌈(L+9)/64⌉)` rows for serialization length `L`, and `L` rows of
//! the `node` table, against `revealedBytes ≤ 3,000,000`.
//!
//! * `n = 256` receivers with 64-character ids (130-nibble keys) that diverge
//!   in their first two characters, so ~124 of each path's 130 branch nodes
//!   are private to that path;
//! * every branch on a private path has its path child plus `kids − 1`
//!   unrevealed siblings (hash stubs). Default `kids = 2`: `L = 75`, two SHA
//!   blocks, `70/75 ≈ 0.93` SHA rows per revealed byte, the best ratio a
//!   nibble-consuming node reaches (the 56-byte nodes of NEAR-AIR.md §6 are
//!   extensions with 20-nibble keys, at most 6 per path, so they cannot fill
//!   the budget; a 16-child branch is `L = 523`, only `0.59` rows/byte);
//! * the account sits in a leaf with an empty key (`L = 50`, `+72` value);
//! * the remaining budget is spent on empty-key extensions directly above the
//!   leaves (`L = 46`, `36/46 ≈ 0.78` rows/byte; accepted by `deriveClaim`,
//!   skipped by the walk via `res`), spread over the paths (`--eps 0`
//!   disables them; the budget then goes to extra stub kids instead).
//!
//! For targets below the maximum, `n` shrinks proportionally (each path costs
//! ~9.4 kB) and the extensions fill the rest, so the trace scales linearly.
use std::collections::BTreeSet;

use super::reexec::sha256;
use super::reexec::spec as rx;
use super::spec::{self, Receipt, params};

/// Generator options.
#[derive(Clone, Debug)]
pub struct Opts {
    /// target `revealedBytes` (≤ 3,000,000)
    pub target_bytes: u64,
    /// receipts (= distinct receivers); `None`: derived from the target
    pub n: Option<usize>,
    /// children per private branch (path child + stubs), 1..=16
    pub kids: usize,
    /// use empty-key extensions to fill the budget
    pub eps: bool,
}

impl Default for Opts {
    fn default() -> Self {
        Opts {
            target_bytes: params::MAX_WITNESS_BYTES,
            n: None,
            kids: 2,
            eps: true,
        }
    }
}

/// A generated case.
pub struct Case {
    pub request: Vec<u8>,
    pub witness: Vec<u8>,
    /// `claim.bin` (own derivation; equal to the reexec engine's)
    pub claim: Vec<u8>,
    /// `revealedBytes` of the witness trie (own count; equal to the reexec engine's)
    pub revealed: u64,
    pub n: usize,
    /// revealed nodes: branches, empty-key extensions, leaves
    pub branches: usize,
    pub exts: usize,
    pub leaves: usize,
}

const KEY_NIBS: usize = 130;
const BLOCK_GAS_PRICE: u128 = 100_000_000;
const GAS_PRICE: u128 = 300_000_000; // > block price: every receipt refunds
const HEIGHT: u64 = 140_000_000;

/// 64-character named account id number `i` (first two characters encode
/// `i`, the rest pseudo-random `[a-z0-9]`, ending in `z`: not implicit).
fn account_id(i: usize) -> Vec<u8> {
    const A: &[u8] = b"0123456789abcdefghijklmnopqrstuvwxyz";
    let h = sha256(format!("np-udr-stark genmax id {i}").as_bytes());
    let mut v = vec![
        b"0123456789abcdef"[(i / 16) % 16],
        b"0123456789abcdef"[i % 16],
    ];
    let mut s = 0usize;
    while v.len() < 63 {
        let b = h[s % 32] as usize + s;
        v.push(A[b % A.len()]);
        s += 1;
    }
    v.push(b'z');
    v
}

fn account_value(i: usize, deposit_total: u128) -> Vec<u8> {
    let mut v = (1_000_000_000_000_000_000_000_000u128 + i as u128 + deposit_total)
        .to_le_bytes()
        .to_vec();
    v.extend(0u128.to_le_bytes()); // locked
    v.extend([0u8; 32]); // code hash
    v.extend(182u64.to_le_bytes()); // storage usage
    v
}

const DEPOSIT: u128 = 1_000_000_000_000_000_000_000;

struct Gen<'a> {
    keys: &'a [Vec<u8>],
    eps: &'a [usize],
    extra: &'a [usize],
    kids: usize,
    post: bool,
    values: BTreeSet<Vec<u8>>,
    revealed: u64,
    branches: usize,
    exts: usize,
    leaves: usize,
}

impl Gen<'_> {
    fn emit(&mut self, ser: Vec<u8>) -> [u8; 32] {
        let h = sha256(&ser);
        if !self.post {
            self.values.insert(ser);
        }
        h
    }

    /// Root hash of the subtrie of `idx` (sorted receiver indices sharing
    /// the key prefix of length `d`).
    fn build(&mut self, d: usize, idx: &[usize]) -> [u8; 32] {
        if d == KEY_NIBS {
            let i = idx[0];
            let val = account_value(i, if self.post { DEPOSIT } else { 0 });
            let vh = sha256(&val);
            if !self.post {
                self.values.insert(val);
            }
            // leaf with an empty key: tag 0, hp [0x20]
            let mut s = vec![0u8];
            s.extend(1u32.to_le_bytes());
            s.push(0x20);
            s.extend(72u32.to_le_bytes());
            s.extend(vh);
            s.extend(250u64.to_le_bytes());
            self.revealed += s.len() as u64 + 72;
            self.leaves += 1;
            let mut h = self.emit(s);
            for e in 0..self.eps[i] {
                // empty-key extension: tag 3, hp [0x00], child
                let mut s = vec![3u8];
                s.extend(1u32.to_le_bytes());
                s.push(0);
                s.extend(h);
                s.extend((300 + e as u64).to_le_bytes());
                self.revealed += s.len() as u64;
                self.exts += 1;
                h = self.emit(s);
            }
            return h;
        }
        let mut kids: [Option<[u8; 32]>; 16] = [None; 16];
        let mut j = 0;
        while j < idx.len() {
            let nib = self.keys[idx[j]][d];
            let mut k = j;
            while k < idx.len() && self.keys[idx[k]][d] == nib {
                k += 1;
            }
            kids[nib as usize] = Some(self.build(d + 1, &idx[j..k]));
            j = k;
        }
        let private = idx.len() == 1;
        let want = if private {
            self.kids
                + self.extra[idx[0]] / KEY_NIBS
                + usize::from(d < self.extra[idx[0]] % KEY_NIBS)
        } else {
            0
        };
        let mut s = 0;
        while kids.iter().flatten().count() < want.min(16) {
            if kids[s].is_none() {
                // stable stub (same pre and post)
                kids[s] = Some(sha256(
                    format!("np-udr-stark genmax stub {} {d} {s}", idx[0]).as_bytes(),
                ));
            }
            s += 1;
        }
        let mut ser = vec![1u8];
        let bm: u16 = kids
            .iter()
            .enumerate()
            .map(|(i, k)| if k.is_some() { 1u16 << i } else { 0 })
            .sum();
        ser.extend(bm.to_le_bytes());
        for k in kids.iter().flatten() {
            ser.extend(k);
        }
        ser.extend((1000 + d as u64).to_le_bytes());
        self.revealed += ser.len() as u64;
        self.branches += 1;
        self.emit(ser)
    }
}

/// Nibbles of `0 ‖ id`.
fn key_of(id: &[u8]) -> Vec<u8> {
    spec::account_key_path(id)
}

fn receipts(n: usize) -> Vec<Receipt> {
    (0..n)
        .map(|i| Receipt {
            predecessor_id: format!("sender-{i}.near").into_bytes(),
            receiver_id: account_id(i),
            receipt_id: sha256(format!("np-udr-stark genmax receipt {i}").as_bytes()).to_vec(),
            signer_id: format!("signer-{}.near", i % 7).into_bytes(),
            signer_pk: spec::PublicKey {
                tag: 0,
                data: sha256(format!("pk {i}").as_bytes()).to_vec(),
            },
            gas_price: GAS_PRICE,
            deposit: DEPOSIT,
        })
        .collect()
}

/// What a build produced (the values are collected for the pre-state only).
struct Built {
    root: [u8; 32],
    values: BTreeSet<Vec<u8>>,
    revealed: u64,
    branches: usize,
    exts: usize,
    leaves: usize,
}

/// Build the trie for the receivers' `keys` with `eps[i]` empty extensions
/// and `extra[i]` extra stub kids on path `i`; `post`: accounts after the batch.
fn build_root(keys: &[Vec<u8>], eps: &[usize], extra: &[usize], kids: usize, post: bool) -> Built {
    let mut g = Gen {
        keys,
        eps,
        extra,
        kids,
        post,
        values: BTreeSet::new(),
        revealed: 0,
        branches: 0,
        exts: 0,
        leaves: 0,
    };
    let mut idx: Vec<usize> = (0..keys.len()).collect();
    idx.sort_by(|&a, &b| keys[a].cmp(&keys[b]));
    let root = g.build(0, &idx);
    Built {
        root,
        values: g.values,
        revealed: g.revealed,
        branches: g.branches,
        exts: g.exts,
        leaves: g.leaves,
    }
}

fn le(w: &mut Vec<u8>, b: &[u8]) {
    w.extend((b.len() as u32).to_le_bytes());
    w.extend(b);
}

/// Encode `request.bin` (`spec/claim-v1.md`; inverse of `decode_request`).
pub fn encode_request(
    shard: u64,
    height: u64,
    bgp: u128,
    gas_limit: u64,
    root: &[u8; 32],
    rs: &[Receipt],
) -> Vec<u8> {
    let mut w = vec![];
    le(&mut w, rx::REQUEST_FORMAT);
    le(&mut w, rx::STATEMENT_ID);
    w.extend(rx::PROTOCOL_VERSION.to_le_bytes());
    le(&mut w, rx::CHAIN_ID);
    w.extend(shard.to_le_bytes());
    w.extend(height.to_le_bytes());
    w.extend(bgp.to_le_bytes());
    w.extend(gas_limit.to_le_bytes());
    w.extend(root);
    w.extend(spec::encode_receipts(rs));
    w
}

/// Encode `witness.bin` (inverse of `decode_witness`; values sorted, unique).
pub fn encode_witness(root: &[u8; 32], values: &BTreeSet<Vec<u8>>) -> Vec<u8> {
    let mut w = vec![];
    le(&mut w, rx::WITNESS_FORMAT);
    w.extend(root);
    w.push(0);
    w.extend((values.len() as u32).to_le_bytes());
    for v in values {
        le(&mut w, v);
    }
    w
}

/// Per-path fixed cost estimate (bytes) for `kids` children per branch.
fn path_cost(kids: usize) -> u64 {
    (KEY_NIBS as u64 - 6) * (11 + 32 * kids as u64) + 122
}

/// Generate a case.
pub fn gen_max(o: &Opts) -> Result<Case, String> {
    if o.target_bytes > params::MAX_WITNESS_BYTES {
        return Err(format!(
            "target {} > {}",
            o.target_bytes,
            params::MAX_WITNESS_BYTES
        ));
    }
    if !(1..=16).contains(&o.kids) {
        return Err("kids must be in 1..=16".into());
    }
    let n = o.n.unwrap_or_else(|| {
        ((o.target_bytes / (path_cost(o.kids) + 200)) as usize).clamp(1, params::MAX_BATCH)
    });
    if !(1..=params::MAX_BATCH).contains(&n) {
        return Err(format!("n = {n} not in 1..=256"));
    }
    let rs = receipts(n);
    let keys: Vec<Vec<u8>> = rs.iter().map(|r| key_of(&r.receiver_id)).collect();
    // base trie, then fill the remaining budget
    let zero = vec![0usize; n];
    let base = build_root(&keys, &zero, &zero, o.kids, false);
    if base.revealed > o.target_bytes {
        return Err(format!(
            "n = {n}, kids = {}: base trie already has {} revealed bytes > target",
            o.kids, base.revealed
        ));
    }
    let rest = o.target_bytes - base.revealed;
    let (mut eps, mut extra) = (zero.clone(), zero.clone());
    let spread = |total: usize, v: &mut Vec<usize>| {
        for (i, x) in v.iter_mut().enumerate() {
            *x = total / n + usize::from(i < total % n);
        }
    };
    if o.eps {
        spread((rest / 46) as usize, &mut eps);
    } else {
        // extra stub kids on private branches (each +32 bytes); capped at 16 kids
        let cap = (16 - o.kids) * (KEY_NIBS - 8);
        spread(((rest / 32) as usize).min(cap * n), &mut extra);
    }
    let pre = build_root(&keys, &eps, &extra, o.kids, false);
    let post_root = build_root(&keys, &eps, &extra, o.kids, true).root;
    let pre_root = pre.root;
    if pre.revealed > params::MAX_WITNESS_BYTES {
        return Err(format!("internal: revealed {} > max", pre.revealed));
    }
    let gas_limit: u64 = 1_000_000_000_000_000;
    let request = encode_request(0, HEIGHT, BLOCK_GAS_PRICE, gas_limit, &pre_root, &rs);
    let witness = encode_witness(&pre_root, &pre.values);
    // own claim derivation
    let outcomes: Vec<spec::Outcome> = rs
        .iter()
        .map(|r| {
            let p = r.gas_price.min(BLOCK_GAS_PRICE);
            let surplus = params::G * (r.gas_price - p);
            let refunds = if surplus == 0 {
                vec![]
            } else {
                vec![spec::receipt_id_from(&r.receipt_id, HEIGHT as u128, 0)]
            };
            spec::Outcome {
                id: r.receipt_id.clone(),
                receipt_ids: refunds,
                gas_burnt: params::G,
                tokens_burnt: params::G * p,
                executor_id: r.receiver_id.clone(),
            }
        })
        .collect();
    let refunds: Vec<Receipt> = rs
        .iter()
        .filter_map(|r| {
            let s = params::G * (r.gas_price - r.gas_price.min(BLOCK_GAS_PRICE));
            (s != 0).then(|| spec::gas_refund_receipt(r, HEIGHT as u128, s))
        })
        .collect();
    let arr = |v: Vec<u8>| -> [u8; 32] { v.try_into().expect("32-byte digest") };
    let claim = rx::Claim {
        protocol_version: rx::PROTOCOL_VERSION,
        chain_id: rx::CHAIN_ID.to_vec(),
        shard_id: 0,
        block_height: HEIGHT,
        block_gas_price: BLOCK_GAS_PRICE,
        gas_limit,
        pre_state_root: pre_root,
        receipt_count: n as u32,
        receipts_commitment: arr(spec::receipts_commitment(0, &rs)),
        slice_post_root: post_root,
        outcome_root: arr(spec::outcome_root(&outcomes)),
        refund_count: refunds.len() as u32,
        refunds_commitment: arr(spec::refunds_commitment(&refunds)),
        gas_burnt_total: (params::G * n as u128) as u64,
        tokens_burnt_total: outcomes.iter().map(|o| o.tokens_burnt).sum(),
    };
    // cross-check with the reexec engine (incl. its domain checks)
    let rx_claim = super::reexec::engine::derive_claim(&request, &witness)?;
    if rx_claim != claim {
        return Err(format!(
            "claim mismatch: own {claim:?} vs reexec {rx_claim:?}"
        ));
    }
    let rx_revealed = {
        let req = rx::decode_request(&request).map_err(|e| e.to_string())?;
        let (_, vals) = rx::decode_witness(&witness).map_err(|e| e.to_string())?;
        let store: super::reexec::trie::Store<'_> = vals.iter().map(|v| (sha256(v), *v)).collect();
        let ks: Vec<Vec<u8>> = req
            .receipts
            .iter()
            .map(|r| super::reexec::trie::nibbles_of(0, r.receiver))
            .collect();
        let kr: Vec<&[u8]> = ks.iter().map(|k| k.as_slice()).collect();
        super::reexec::trie::PTrie::build(&store, pre_root, &kr)?.revealed_bytes()
    };
    if rx_revealed != pre.revealed {
        return Err(format!(
            "revealed bytes: own {} vs reexec {rx_revealed}",
            pre.revealed
        ));
    }
    Ok(Case {
        request,
        witness,
        claim: claim.encode(),
        revealed: pre.revealed,
        n,
        branches: pre.branches,
        exts: pre.exts,
        leaves: pre.leaves,
    })
}
