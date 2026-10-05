//! `max_witness` generator profile: a maximal in-domain slice witness.
//!
//! Adversarial worst-case prover input: `n` receipts (256 unless
//! `--receipts N`) to distinct 64-character receivers whose recorded slice
//! witness (nearcore's own `TrieRecorder`, so a canonical nearcore trie) is as
//! close to the domain cap `witness_size ≤ 3 000 000` as 32-byte granularity
//! allows. Port of the candidate-side `npudr gen-max --eps 0`
//! (`examples/np-udr-stark/source/src/near/genmax.rs`) onto a real state: the
//! oracle builds a key/value pre-state, nearcore builds the trie, and every
//! case still goes through `Runtime::apply` and the domain check like any
//! other class.
//!
//! Shape (all choices deterministic from `(seed, index)`):
//! * receivers: 64-character named ids (130-nibble keys `0x00 ‖ id`) with
//!   pairwise distinct 2-character prefixes, so every path is private below
//!   nibble 6 at the latest (~124 private nodes per path);
//! * for every private nibble depth `d ≥ 4` of a receiver's key, one
//!   untouched sibling account whose key leaves the path exactly at `d`
//!   (`key[..d/2] ‖ c`, `c` a valid id character differing in nibble `d`):
//!   every private node is a 2-child branch (75 bytes, 2 SHA-256 blocks), the
//!   account sits in a leaf with an empty key, and there is no extension to
//!   compress the path (the siblings are hash stubs: never revealed);
//! * the remaining budget is spent 32 bytes at a time on further siblings,
//!   two at a time on odd-depth branches first (a 4-child branch is 139 bytes,
//!   3 SHA blocks: each pair adds a block), then singly anywhere still free;
//!   the count is calibrated against nearcore's recorder, so the witness is
//!   `3 000 000 − r` bytes with `0 ≤ r < 32` (for n = 256).
//! * every receipt pays more than the block gas price (one gas refund
//!   receipt each), predecessors/signers are 64-character ids with SECP256K1
//!   keys (largest receipts; the request stays far below 128 KiB).
//!
//! Empty-key extensions (the default fill of `npudr gen-max`) do not occur in
//! nearcore tries, so they are not used: this class is canonical state only.

use near_crypto::PublicKey;
use near_primitives::account::{Account, AccountContract};
use near_primitives::hash::CryptoHash;
use near_primitives::receipt::{ActionReceipt, Receipt, ReceiptEnum, ReceiptV0};
use near_primitives::transaction::{Action, TransferAction};
use near_primitives::types::Balance;
use borsh::BorshDeserialize;
use std::collections::{BTreeMap, BTreeSet};

use crate::casegen::{self, ALNUM, Case, Rng};
use crate::domain::{self, MAX_WITNESS_BYTES};
use crate::enc::Request;

pub const PROFILE: &str = "max_witness";
/// Nibbles of an Account key `0x00 ‖ id` for a 64-character id.
const KEY_NIBS: usize = 130;
const ID_LEN: usize = 64;
/// Each extra sibling adds exactly one child hash to an existing branch.
const SIBLING_BYTES: usize = 32;
const BLOCK_GAS_PRICE: u128 = 100_000_000;

/// What the generator built (reported on stderr; the authoritative sizes are
/// in each case's diagnostics.json).
#[derive(Debug, Default)]
#[allow(dead_code)] // read through Debug
pub struct Stats {
    pub receipts: usize,
    pub base_siblings: usize,
    pub fill_siblings: usize,
    pub witness_bytes: usize,
}

fn nibble(key: &[u8], d: usize) -> u8 {
    if d % 2 == 0 { key[d / 2] >> 4 } else { key[d / 2] & 15 }
}

fn lcp_nibbles(a: &[u8], b: &[u8]) -> usize {
    (0..a.len().min(b.len()) * 2).take_while(|&d| nibble(a, d) == nibble(b, d)).count()
}

/// Valid id characters that leave a key whose character is `c` at nibble
/// depth parity `hi` (high nibble) / low nibble, one per distinct child slot.
fn alternatives(rng: &mut Rng, c: u8, hi: bool) -> Vec<u8> {
    let mut seen = BTreeSet::new();
    let mut v: Vec<u8> = ALNUM.to_vec();
    shuffle(rng, &mut v);
    v.into_iter()
        .filter(|&x| if hi { x >> 4 != c >> 4 && seen.insert(x >> 4) } else { x >> 4 == c >> 4 && x != c })
        .collect()
}

fn shuffle<T>(rng: &mut Rng, v: &mut [T]) {
    for i in (1..v.len()).rev() {
        v.swap(i, rng.below(i as u64 + 1) as usize);
    }
}

fn long_id(rng: &mut Rng) -> String {
    loop {
        let s = casegen::raw_valid_id(rng, ID_LEN);
        if casegen::is_named(&s) {
            return s;
        }
    }
}

fn secp_pk(rng: &mut Rng) -> PublicKey {
    let mut b = vec![1u8];
    b.extend_from_slice(&rng.bytes32());
    b.extend_from_slice(&rng.bytes32());
    PublicKey::try_from_slice(&b).unwrap()
}

fn sibling_account(rng: &mut Rng) -> Vec<u8> {
    let a = casegen::random_account(rng, false);
    borsh::to_vec(&a).unwrap()
}

/// Generate a `max_witness` case with `n` receipts. `extra_state` is added to
/// the pre-state and `extra_reads` to the recorded reads (scope v2: the
/// bandwidth-scheduler key `0x0f`), so the calibration measures exactly the
/// witness the scope records.
pub fn generate(
    seed: u64,
    idx: u64,
    n: usize,
    extra_state: &[(Vec<u8>, Vec<u8>)],
    extra_reads: &[Vec<u8>],
) -> (Case, Stats) {
    assert!((1..=domain::MAX_BATCH).contains(&n), "max_witness: receipts must be in 1..=256");
    let mut rng = Rng::new(seed ^ 0x4D41_5857_4954_0001, idx);

    // ---- receivers: distinct 2-character prefixes, 64 characters, named
    let mut prefixes = BTreeSet::new();
    let mut ids: Vec<String> = vec![];
    while ids.len() < n {
        let p = [*rng.pick(ALNUM), *rng.pick(ALNUM)];
        if !prefixes.insert(p) {
            continue;
        }
        let mut v = p.to_vec();
        // a non-hex character early: neither the id nor any sibling id built
        // from its prefixes can be an implicit (hex / 0x / 0s) account
        v.push(*rng.pick(b"ghijklmnopqrstuvwxyz"));
        while v.len() < ID_LEN {
            v.push(*rng.pick(ALNUM));
        }
        let s = String::from_utf8(v).unwrap();
        assert!(casegen::is_named(&s), "max_witness receiver {s} not a named account");
        ids.push(s);
    }
    let keys: Vec<Vec<u8>> = ids.iter().map(|s| domain::account_key(s)).collect();

    let mut state: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();
    for k in &keys {
        let amount = 10u128.pow(24) * rng.range(1, 1000) as u128 + rng.u128_below(10u128.pow(24));
        let a = Account::new(Balance::from_yoctonear(amount), Balance::ZERO, AccountContract::None, 182);
        state.insert(k.clone(), borsh::to_vec(&a).unwrap());
    }
    for (k, v) in extra_state {
        state.insert(k.clone(), v.clone());
    }

    // ---- private depth of every path: one past the longest shared prefix
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| keys[a].cmp(&keys[b]));
    let mut shared = vec![0usize; n];
    for w in order.windows(2) {
        let l = lcp_nibbles(&keys[w[0]], &keys[w[1]]);
        shared[w[0]] = shared[w[0]].max(l);
        shared[w[1]] = shared[w[1]].max(l);
    }

    // ---- one sibling per private depth; the rest of each depth's
    // alternatives are kept for the fill
    let sib = |k: &[u8], d: usize, c: u8| -> Vec<u8> {
        let mut s = k[..d / 2].to_vec();
        s.push(c);
        s
    };
    let mut spare: Vec<Vec<(usize, Vec<u8>)>> = vec![vec![]; n];
    let mut base_siblings = 0;
    for i in 0..n {
        let k = &keys[i];
        for d in (shared[i] + 1).max(4)..KEY_NIBS {
            let mut alts = alternatives(&mut rng, k[d / 2], d % 2 == 0);
            let first = alts.remove(0);
            state.insert(sib(k, d, first), sibling_account(&mut rng));
            base_siblings += 1;
            spare[i].push((d, alts));
        }
    }

    // ---- fill order: pairs on odd-depth branches (round-robin over depths and
    // paths), then single siblings wherever a slot is left
    let mut fill: Vec<Vec<u8>> = vec![];
    loop {
        let mut any = false;
        for di in 0..KEY_NIBS {
            for i in 0..n {
                if let Some((d, alts)) = spare[i].get_mut(di) {
                    if *d % 2 == 1 && alts.len() >= 2 {
                        for _ in 0..2 {
                            let c = alts.remove(0);
                            fill.push(sib(&keys[i], *d, c));
                        }
                        any = true;
                    }
                }
            }
        }
        if !any {
            break;
        }
    }
    for i in 0..n {
        for (d, alts) in &spare[i] {
            for &c in alts {
                fill.push(sib(&keys[i], *d, c));
            }
        }
    }

    // ---- calibrate against nearcore's recorder
    let mut reads = keys.clone();
    reads.extend(extra_reads.iter().cloned());
    let b0 = crate::exec::recorded_read_bytes(&state, &reads);
    assert!(b0 <= MAX_WITNESS_BYTES, "max_witness: base trie already records {b0} bytes > {MAX_WITNESS_BYTES}");
    let mut k = ((MAX_WITNESS_BYTES - b0) / SIBLING_BYTES).min(fill.len());
    let fill_values: Vec<Vec<u8>> = (0..k).map(|_| sibling_account(&mut rng)).collect();
    let witness_bytes = loop {
        let mut s = state.clone();
        for (key, v) in fill[..k].iter().zip(&fill_values) {
            s.insert(key.clone(), v.clone());
        }
        let b = crate::exec::recorded_read_bytes(&s, &reads);
        if b <= MAX_WITNESS_BYTES {
            state = s;
            break b;
        }
        // not expected (each sibling is exactly one more child hash); stay in domain
        let over = (b - MAX_WITNESS_BYTES).div_ceil(SIBLING_BYTES);
        k = k.saturating_sub(over.max(1));
    };

    // ---- receipts: one per receiver, every one refunds
    let mut receipts = vec![];
    for id in &ids {
        let pred: near_primitives::types::AccountId = long_id(&mut rng).parse().unwrap();
        let signer = if rng.chance(4, 5) { pred.clone() } else { long_id(&mut rng).parse().unwrap() };
        let gas_price = *rng.pick(&[1_000_000_000u128, 2_000_000_000, 300_000_000]);
        receipts.push(Receipt::V0(ReceiptV0 {
            predecessor_id: pred,
            receiver_id: id.parse().unwrap(),
            receipt_id: CryptoHash(rng.bytes32()),
            receipt: ReceiptEnum::Action(ActionReceipt {
                signer_id: signer,
                signer_public_key: secp_pk(&mut rng),
                gas_price: Balance::from_yoctonear(gas_price),
                output_data_receivers: vec![],
                input_data_ids: vec![],
                actions: vec![Action::Transfer(TransferAction {
                    deposit: Balance::from_yoctonear(1 + rng.u128_below(10u128.pow(25))),
                })],
            }),
        }));
    }
    let request = Request {
        protocol_version: domain::PROTOCOL_VERSION,
        chain_id: domain::CHAIN_ID.into(),
        shard_id: 0,
        block_height: rng.range(1, 1 << 40),
        block_gas_price: BLOCK_GAS_PRICE,
        gas_limit: 1_000_000_000_000_000,
        pre_state_root: CryptoHash::default(), // filled in by exec
        receipts,
    };
    let stats = Stats { receipts: n, base_siblings, fill_siblings: k, witness_bytes };
    let case = Case {
        id: format!("s{seed}-mw{n}-v{idx}"),
        profile: PROFILE.into(),
        request,
        state,
        invalid_kind: None,
    };
    (case, stats)
}

/// Receipt count of the class: `--receipts N` if given, else the domain maximum.
pub fn receipts() -> usize {
    match casegen::FORCE_RECEIPTS.load(std::sync::atomic::Ordering::Relaxed) {
        0 => domain::MAX_BATCH,
        r => r,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alternatives_leave_the_path_at_the_right_nibble() {
        let mut rng = Rng::new(7, 0);
        for &c in ALNUM {
            let hi = alternatives(&mut rng, c, true);
            assert!(hi.iter().all(|x| x >> 4 != c >> 4 && ALNUM.contains(x)));
            assert_eq!(hi.iter().map(|x| x >> 4).collect::<BTreeSet<_>>().len(), hi.len());
            assert_eq!(hi.len(), 2); // high nibbles of [a-z0-9]: 3, 6, 7
            let lo = alternatives(&mut rng, c, false);
            assert!(lo.iter().all(|x| x >> 4 == c >> 4 && *x != c && ALNUM.contains(x)));
            assert!(lo.len() >= 9);
        }
    }

    /// Small instance end to end: in-domain, nearcore-clean, deterministic,
    /// witness exactly base + 32 per fill sibling.
    #[test]
    fn small_max_witness_case_is_in_domain_and_deterministic() {
        let (c, st) = generate(5, 0, 3, &[], &[]);
        let (c2, _) = generate(5, 0, 3, &[], &[]);
        assert_eq!(c.state, c2.state);
        assert_eq!(c.request.encode(), c2.request.encode());
        assert_eq!(c.request.receipts.len(), 3);
        // n = 3 cannot reach the cap: every fill slot is used
        assert!(st.fill_siblings > 0 && st.witness_bytes < MAX_WITNESS_BYTES);
        let ex = crate::exec::run(c.request.clone(), &c.state);
        assert!(ex.clean, "{:?}", ex.problems);
        let wb: usize = ex.witness_values.iter().map(|v| v.len()).sum();
        assert_eq!(wb, st.witness_bytes);
        let sim = domain::check(&ex.request, &c.state, wb).unwrap();
        assert_eq!(sim.refunds, 3);
    }
}
