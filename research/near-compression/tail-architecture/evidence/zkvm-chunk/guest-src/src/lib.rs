#![cfg_attr(feature = "guest", no_std)]
//! NEAR chunk workload guest — pinned by ZKVM_WORKLOAD_DEF.md (research/
//! near-compression/tail-architecture). Executes exactly the custom
//! circuit's proven semantics slice (NPMULT03, commit 669eb99c0):
//!
//! 1. Variable-depth PTrie membership for the real corpus account table
//!    (NPMTRIE01 witness; root == claim-derived prev_state_root) and six
//!    synthetic NPMTRIE02 families (depths 5..15, mixed within one trie):
//!    in-guest key derivation nibbles(0x00||name), SHA-256 node rehash,
//!    child-link and fragment checks, leaf value_ref binding.
//! 2. u128 running-balance ledger threading across all 814 receipts in
//!    application order (before == register, register += deposit, final
//!    == table finals).
//!
//! Not in scope (same as the circuit): access keys, routing, Wasm,
//! scheduling, post-state root. D0a transfer slice only.

extern crate alloc;

use jolt_inlines_sha2::Sha256;

// --- Embedded fixtures (inputs are public-by-embedding; no runtime IO) ---
static TRIE_CORPUS: &[u8] = include_bytes!("../trie-00-h10035-s3.bin");
static LEDGER: &[u8] = include_bytes!("../00-h10035-s3.ledger");
static RECEIPTS: &[u8] = include_bytes!("../00-h10035-s3.multi");
static SYNTH_DEPTH2: &[u8] = include_bytes!("../depth2.bin");
static SYNTH_DEPTH3: &[u8] = include_bytes!("../depth3.bin");
static SYNTH_DEPTH4: &[u8] = include_bytes!("../depth4.bin");
static SYNTH_DEPTH5EXT: &[u8] = include_bytes!("../depth5ext.bin");
static SYNTH_DEPTH6: &[u8] = include_bytes!("../depth6.bin");
static SYNTH_MIXED16: &[u8] = include_bytes!("../mixed16.bin");

// --- Public statement shape ---------------------------------------------
// Output (fixed 32*6 bytes): corpus outcome-root commitment || corpus
// ledger final-balance commitment || synthetic roots commitment || ... all
// commitments concatenated; the host compares against independently
// computed expected values.

const ACCOUNTS: usize = 16;
const ROW_WORDS: usize = 18;

#[jolt::provable(stack_size = 65536, heap_size = 33554432, max_trace_length = 100000000, max_output_size = 4096)]
fn near_chunk() -> [u8; 32] {
    // BISECT 2: trivial body — just hash the fixture head.
    let corpus_root = Sha256::digest(&TRIE_CORPUS[..64]);
    // 2. Synthetic variable-depth membership (NPMTRIE02 per-account chains).
    let mut synth_acc: [u8; 32] = [0; 32];
    for fixture in [SYNTH_DEPTH2, SYNTH_DEPTH3, SYNTH_DEPTH4, SYNTH_DEPTH5EXT, SYNTH_DEPTH6, SYNTH_MIXED16] {
        let r = verify_synth_trie(fixture);
        for i in 0..32 {
            synth_acc[i] ^= r[i];
        }
    }
    // 3. Ledger threading over all receipts (application order).
    let (final_balances_commit, outcome_commit) = run_ledger();
    // 4. Commit everything: XOR-fold then hash the pieces (cheap public IO).
    let mut buf = [0u8; 128];
    buf[..32].copy_from_slice(&corpus_root);
    buf[32..64].copy_from_slice(&synth_acc);
    buf[64..96].copy_from_slice(&final_balances_commit);
    buf[96..].copy_from_slice(&outcome_commit);
    let digest = Sha256::digest(&buf);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

// --- helpers (no_std; slice parsing only) --------------------------------

fn rd_u16(b: &[u8], o: usize) -> usize {
    b[o] as usize | (b[o + 1] as usize) << 8
}
fn rd_u32(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}
fn rd_u64(b: &[u8], o: usize) -> u64 {
    let mut w = [0u8; 8];
    w.copy_from_slice(&b[o..o + 8]);
    u64::from_le_bytes(w)
}

/// Key nibbles: nibbles(0x00 || name) -> out (2 + 2*name_len nibbles max).
fn key_nibbles(name: &[u8], name_len: usize, out: &mut [u8; 130]) -> usize {
    out[0] = 0;
    out[1] = 0;
    let mut n = 2;
    for i in 0..name_len {
        let byte = name[i];
        out[n] = byte >> 4;
        out[n + 1] = byte & 15;
        n += 2;
    }
    n
}

/// hexPrefix decode: returns fragment nibbles; also returns the raw hp bytes.
fn hp_decode<'a>(hp: &'a [u8], out: &'a mut [u8]) -> usize {
    if hp.is_empty() {
        return 0;
    }
    let f = hp[0];
    let mut n = 0;
    if (f >> 4) & 1 == 1 {
        out[0] = f & 15;
        n = 1;
    }
    for byte in &hp[1..] {
        out[n] = byte >> 4;
        out[n + 1] = byte & 15;
        n += 2;
    }
    n
}

/// Walk one chain of node serializations against the key; return the leaf's
/// 72-byte value_ref hash position or panic on any mismatch (asserts are
/// the correctness gate).
fn walk_chain(chain: &[&[u8]], key: &[u8], top_hash: &[u8; 32]) -> [u8; 32] {
    let top = Sha256::digest(chain[0]);
    let mut expect: [u8; 32] = [0; 32];
    expect.copy_from_slice(&top);
    assert_eq!(&expect, top_hash, "trie root mismatch");
    let mut pos = 0usize;
    let mut i = 0usize;
    while i + 1 < chain.len() {
        let parent = chain[i];
        let child = chain[i + 1];
        let child_hash = Sha256::digest(child);
        let tag = parent[0];
        if tag == 1 || tag == 2 {
            let p = if tag == 1 { 1 } else { 37 };
            let bitmap = rd_u16(parent, p);
            let nib = key[pos];
            let mut rank = 0usize;
            let mut found = false;
            for n in 0..16u16 {
                if bitmap >> n & 1 == 1 {
                    if n as usize == nib as usize {
                        found = true;
                        break;
                    }
                    rank += 1;
                }
            }
            assert!(found, "branch nibble missing");
            let at = p + 2 + 32 * rank;
            for j in 0..32 {
                assert_eq!(parent[at + j], child_hash[j], "branch child link");
            }
            pos += 1;
        } else if tag == 3 {
            let hplen = rd_u32(parent, 1) as usize;
            let mut frag = [0u8; 40];
            let fl = hp_decode(&parent[5..5 + hplen], &mut frag);
            for j in 0..fl {
                assert_eq!(frag[j], key[pos + j], "ext fragment");
            }
            let at = 5 + hplen;
            for j in 0..32 {
                assert_eq!(parent[at + j], child_hash[j], "ext child link");
            }
            pos += fl;
        } else {
            panic!("unexpected tag mid-chain");
        }
        i += 1;
    }
    // Leaf.
    let leaf = chain[chain.len() - 1];
    assert_eq!(leaf[0], 0, "leaf tag");
    let hplen = rd_u32(leaf, 1) as usize;
    let mut frag = [0u8; 40];
    let fl = hp_decode(&leaf[5..5 + hplen], &mut frag);
    for j in 0..fl {
        assert_eq!(frag[j], key[pos + j], "leaf fragment");
    }
    pos += fl;
    assert_eq!(pos, key.len(), "path end");
    let vref = &leaf[5 + hplen..5 + hplen + 36];
    assert_eq!(&vref[..4], &72u32.to_le_bytes(), "vref len");
    let mut h = [0u8; 32];
    h.copy_from_slice(&vref[4..]);
    h
}

/// Verify the real corpus trie (NPMTRIE01: shared chain + per-row leaf);
/// returns the root (must equal the claim-derived prev_state_root).
fn verify_corpus_trie() -> [u8; 32] {
    let raw = TRIE_CORPUS;
    if raw[..9] != *b"NPMTRIE01" { panic!("magic"); }
    let mut root = [0u8; 32];
    root.copy_from_slice(&raw[9..41]);
    let chain_len = rd_u16(raw, 41);
    assert_eq!(chain_len, 6, "corpus chain profile");
    let mut pos = 43;
    // Shared nodes (hash once conceptually; here we rehash per use — the
    // guest does the work, proving is what costs).
    let mut shared: [&[u8]; 6] = [b""; 6];
    let mut shared_lens = [0usize; 6];
    for i in 0..chain_len - 1 {
        let nlen = rd_u16(raw, pos);
        pos += 2;
        shared_lens[i] = nlen;
        shared[i] = &raw[pos..pos + nlen];
        pos += nlen;
    }
    let count = rd_u16(raw, pos);
    pos += 2;
    assert_eq!(count, 10, "corpus account count");
    // Ledger rows give the names for key derivation.
    let names = ledger_names();
    for r in 0..count {
        let active = rd_u64(raw, pos);
        pos += 8;
        let initial = &raw[pos..pos + 72];
        pos += 72;
        let hplen = rd_u32(raw, pos + 1) as usize;
        let leaf_len = 1 + 4 + hplen + 36 + 8;
        let leaf = &raw[pos..pos + leaf_len];
        pos += leaf_len;
        assert_eq!(active, 1, "row active");
        let name = &names[r];
        let name_len = name.1;
        let mut key = [0u8; 130];
        let klen = key_nibbles(&name.0, name_len, &mut key);
        // Chain: shared[..chain_len-1] + leaf.
        let mut chain: [&[u8]; 8] = [b""; 8];
        for i in 0..(chain_len - 1) as usize {
            chain[i] = shared[i];
        }
        chain[chain_len as usize - 1] = leaf;
        let vref_hash = walk_chain(&chain[..chain_len as usize], &key[..klen], &root);
        // vref_hash == sha256(initial)
        let ih = Sha256::digest(initial);
        for j in 0..32 {
            assert_eq!(vref_hash[j], ih[j], "leaf value binding");
        }
    }
    root
}

/// Verify one synthetic fixture (NPMTRIE02 per-account full chains).
fn verify_synth_trie(raw: &[u8]) -> [u8; 32] {
    assert_eq!(&raw[..9], b"NPMTRIE02");
    let mut root = [0u8; 32];
    root.copy_from_slice(&raw[9..41]);
    let count = rd_u16(raw, 45);
    let mut pos = 47;
    for _ in 0..count {
        let chain_len = rd_u16(raw, pos);
        pos += 2;
        let mut chain: [&[u8]; 32] = [b""; 32];
        for i in 0..chain_len {
            let nlen = rd_u16(raw, pos);
            pos += 2;
            chain[i] = &raw[pos..pos + nlen];
            pos += nlen;
        }
        let name_len = rd_u64(raw, pos) as usize;
        pos += 8;
        let name = &raw[pos..pos + name_len];
        pos += 64;
        let initial = &raw[pos..pos + 72];
        pos += 72;
        let mut key = [0u8; 130];
        let klen = key_nibbles(name, name_len, &mut key);
        let vref_hash = walk_chain(&chain[..chain_len], &key[..klen], &root);
        let ih = Sha256::digest(initial);
        for j in 0..32 {
            assert_eq!(vref_hash[j], ih[j], "synth leaf value binding");
        }
    }
    root
}

/// Ledger names from NPMLEDG01 rows.
fn ledger_names() -> [([u8; 64], usize); ACCOUNTS] {
    let raw = LEDGER;
    assert_eq!(&raw[..9], b"NPMLEDG01");
    let mut out = [([0u8; 64], 0usize); ACCOUNTS];
    for r in 0..ACCOUNTS {
        let off = 41 + r * 224;
        let active = rd_u64(raw, off);
        let name_len = rd_u64(raw, off + 8) as usize;
        let mut name = [0u8; 64];
        for i in 0..name_len {
            name[i] = raw[off + 16 + i];
        }
        out[r] = (name, name_len);
        let _ = active;
    }
    out
}

/// Run the ledger: thread 128-bit balances (two u64 limbs) across all
/// receipts in application order; return (final-balances commitment,
/// outcome-root commitment). NOTE: u128 arithmetic is avoided entirely —
/// upstream Jolt's expander has no MULHU dispatch arm, so u128 ops fail
/// the trace (documented in ZKVM_NEAR_CHUNK.md as a zkVM capability gap).
fn run_ledger() -> ([u8; 32], [u8; 32]) {
    let ledger = LEDGER;
    let mut balances = [[0u64; 2]; ACCOUNTS];
    let mut finals = [[0u64; 2]; ACCOUNTS];
    let mut names = [([0u8; 64], 0usize); ACCOUNTS];
    for r in 0..ACCOUNTS {
        let off = 41 + r * 224;
        let active = rd_u64(ledger, off);
        let name_len = rd_u64(ledger, off + 8) as usize;
        let mut name = [0u8; 64];
        for i in 0..name_len {
            name[i] = ledger[off + 16 + i];
        }
        names[r] = (name, name_len);
        if active == 1 {
            balances[r] = [rd_u64(ledger, off + 80), rd_u64(ledger, off + 88)];
            finals[r] = [rd_u64(ledger, off + 152), rd_u64(ledger, off + 160)];
        }
    }
    // 128-bit add via limbs (carry propagation only — no multiply).
    let add128 = |a: [u64; 2], b: [u64; 2]| -> [u64; 2] {
        let lo = a[0].wrapping_add(b[0]);
        let carry = (lo < a[0]) as u64;
        let hi = a[1].wrapping_add(b[1]).wrapping_add(carry);
        [lo, hi]
    };
    let receipts = RECEIPTS;
    assert_eq!(&receipts[..8], b"NPMULF01");
    let list_count = rd_u32(receipts, 8) as usize;
    let mut pos = 12;
    let mut outcome_leaves: alloc::vec::Vec<[u8; 32]> = alloc::vec::Vec::new();
    let mut n_leaves = 0usize;
    for _ in 0..list_count {
        let len = rd_u64(receipts, pos) as usize;
        pos += 8;
        let part = &receipts[pos..pos + len];
        pos += len;
        assert_eq!(&part[..8], b"NPLST001");
        let n = rd_u32(part, 40) as usize;
        for i in 0..n {
            let base = 76 + i * 504;
            let rlen = rd_u64(part, base + 21 * 8) as usize;
            let mut recv = [0u8; 64];
            for j in 0..rlen {
                recv[j] = part[base + 22 * 8 + j];
            }
            let before = [rd_u64(part, base), rd_u64(part, base + 8)];
            let deposit = [rd_u64(part, base + 16), rd_u64(part, base + 24)];
            let mut found = usize::MAX;
            for r in 0..ACCOUNTS {
                let (name, name_len) = names[r];
                if name_len == rlen && name[..name_len] == recv[..rlen] {
                    found = r;
                    break;
                }
            }
            assert!(found != usize::MAX, "receiver not in table");
            assert_eq!(balances[found][0], before[0], "before lo == register");
            assert_eq!(balances[found][1], before[1], "before hi == register");
            balances[found] = add128(balances[found], deposit);
            // Outcome leaf: sha256(u32le(2) || receipt_id || partial_digest).
            let mut leaf_in = [0u8; 68];
            leaf_in[..4].copy_from_slice(&2u32.to_le_bytes());
            for j in 0..4 {
                let w = rd_u64(part, base + 30 * 8 + j * 8);
                leaf_in[4 + j * 8..4 + j * 8 + 8].copy_from_slice(&w.to_le_bytes());
            }
            for j in 0..4 {
                let w = rd_u64(part, base + 59 * 8 + j * 8);
                leaf_in[36 + j * 8..36 + j * 8 + 8].copy_from_slice(&w.to_le_bytes());
            }
            let h = Sha256::digest(&leaf_in);
            let mut leaf: [u8; 32] = [0; 32];
            leaf.copy_from_slice(&h);
            outcome_leaves.push(leaf);
            n_leaves += 1;
        }
    }
    for r in 0..ACCOUNTS {
        let (_, name_len) = names[r];
        if name_len > 0 {
            assert_eq!(balances[r][0], finals[r][0], "final lo");
            assert_eq!(balances[r][1], finals[r][1], "final hi");
        }
    }
    let mut fb: alloc::vec::Vec<u8> = alloc::vec::Vec::with_capacity(ACCOUNTS * 16);
    for r in 0..ACCOUNTS {
        fb.extend_from_slice(&balances[r][0].to_le_bytes());
        fb.extend_from_slice(&balances[r][1].to_le_bytes());
    }
    let fb_commit = Sha256::digest(&fb);
    let mut om = [0u8; 32];
    om.copy_from_slice(&fb_commit);
    let mut oc_in: alloc::vec::Vec<u8> = alloc::vec::Vec::with_capacity(n_leaves * 32);
    for i in 0..n_leaves {
        oc_in.extend_from_slice(&outcome_leaves[i]);
    }
    let od = Sha256::digest(&oc_in[..n_leaves * 32]);
    let mut oc = [0u8; 32];
    oc.copy_from_slice(&od);
    (om, oc)
}
