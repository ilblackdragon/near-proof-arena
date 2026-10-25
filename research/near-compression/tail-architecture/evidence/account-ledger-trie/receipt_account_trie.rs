//! In-circuit PTrie membership for the account table (fixed profile).
//!
//! Profile (explicit, corpus-shaped; not a universal bound): a shared chain
//! of 5 nodes with roles [Branch, Branch, Branch, Ext, Branch] — the exporter
//! asserts these roles and that nodes 0..4 are byte-identical across all
//! accounts. Every table row descends the shared chain; rows differ only in
//! the nibble consumed at the LAST shared branch (the account's final key
//! nibble) and the leaf fragment. Key = nibbles(0x00 || name); the shared
//! prefix consumes key[0..2] (constants 0,0 and the first name nibble), the
//! ext fragment consumes F_ext nibbles, the last branch one more, the leaf
//! fragment the tail: 4 + F_ext + F_leaf == 2*(1+name_len).
//!
//! Node serializations (native PTrie.node_ser — the sha256 preimage):
//!   Branch: 1 || u16le(bitmap) || 32B hash per set bit in nibble order || u64le(mem)
//!   Ext:    3 || u32le(hp_len) || hp || 32B child hash || u64le(mem)
//!   Leaf:   0 || u32le(hp_len) || hp || value_ref(4LE+32BE) || u64le(mem)
//!
//! Constraints (all in-circuit; witnesses are trusted-local exports, their
//! VERIFICATION is not trusted):
//! - Each shared node's node_ser is reconstructed from decoded witness
//!   fields and hashed (tight_sha); the top hash must equal the public
//!   prev_state_root words — a lying witness breaks the root.
//! - Chain links: branch0 child@nib0 == hash(branch1); branch1 child@nib0 ==
//!   hash(branch2); branch2 child@row-key[2] == hash(ext) (per row); ext
//!   child == hash(branch3); branch3 child@row-final-nibble == row leaf hash
//!   (per row). All walked nibbles must be set bitmap bits.
//! - Per row: leaf value_ref == u32le(72) || sha256(72B account value),
//!   where the value = PUBLIC table balance/locked/storage words + 4 witness
//!   code words (the code hash is authenticated only through the trie leaf).
//!   The table storage high word must be zero (72B value has 8 storage bytes).
//! - Key-path correspondence (the binding the old host audit lacked): the
//!   ext fragment nibbles must equal key[3..3+F_ext]; the leaf fragment
//!   nibbles must equal the key tail; the consumed total must equal
//!   2*(1+name_len) exactly.
//! - hexPrefix decode: the odd flag is bit 4 of hp[0] (the leaf bit 0x20
//!   lives at bit 5 and never aliases it); even fragments start at hp[1].
//!
//! Corpus shape: branches [75,139,107,331]B (bitmaps {0,1},{0,2,13,15},
//! {3,6,7},{0..9}), ext 50B (hp 5B even, 8 nibbles), leaves 50B (hp 1B even,
//! 0 nibbles), all names 's0a0X' — key[2]=7.
use binius_frontend::{CircuitBuilder, Wire};
use binius_circuits::fixed_byte_vec::ByteVec;
use crate::ledger::{Ledger, ACCOUNT_SLOTS};
use crate::tight_sha;

/// Shared chain length (corpus: 5).
pub const NODES: usize = 5;

/// Branch byte budget: 3 + 32*10 + 8 = 331 max, padded to a word multiple.
pub const BRANCH_BYTES: usize = 336;
/// Ext: 5 + 8 + 32 + 8 = 53 max.
pub const EXT_BYTES: usize = 56;
/// Leaf: 5 + 2 + 36 + 8 = 51 max.
pub const LEAF_BYTES: usize = 56;
pub const EXT_HP_MAX: usize = 8;
pub const LEAF_HP_MAX: usize = 2;
pub const EXT_FRAG_NIBS: usize = 15;
pub const LEAF_FRAG_NIBS: usize = 3;
pub const CODE_WORDS: usize = 4;

pub struct BranchNode {
    pub bitmap: Wire,
    /// Child hash per nibble slot (four big-endian words); unset slots are
    /// never placed (bit gate) and can be zero.
    pub kids: [[Wire; 4]; 16],
    pub mem: Wire,
}

pub struct ExtNode {
    pub hp_len: Wire,
    pub hp: [Wire; EXT_HP_MAX],
    pub child: [Wire; 4],
    pub mem: Wire,
}

pub struct LeafWitness {
    pub hp_len: Wire,
    pub hp: [Wire; LEAF_HP_MAX],
    pub vref_len: Wire,
    pub vref_hash: [Wire; 4],
    pub mem: Wire,
    pub code: [Wire; CODE_WORDS],
}

pub struct TrieWitness {
    /// Fixed roles: indices [0,1,2,3] are the four branches in walk order
    /// (node0, node1, node2, node4 of the chain); the ext is node3.
    pub branches: [BranchNode; 4],
    pub ext: ExtNode,
    pub rows: Vec<LeafWitness>,
    /// Public prev_state_root (four big-endian words) — statement head.
    pub root: [Wire; 4],
}

fn le_byte(b: &CircuitBuilder, w: Wire, i: u32) -> Wire {
    b.band(b.shr(w, 8 * i), b.add_constant_64(255))
}
fn be_byte(b: &CircuitBuilder, w: Wire, j: u32) -> Wire {
    b.band(b.shr(w, 56 - 8 * j), b.add_constant_64(255))
}
fn pack_bytes(b: &CircuitBuilder, bytes: &[Wire]) -> Vec<Wire> {
    bytes
        .chunks(8)
        .map(|chunk| {
            let mut w = b.add_constant_64(0);
            for (i, x) in chunk.iter().enumerate() {
                w = b.bor(w, b.shl(*x, (8 * i) as u32));
            }
            w
        })
        .collect()
}
/// A 32B digest as 32 byte wires (big-endian per word).
fn digest_bytes(b: &CircuitBuilder, hash: &[Wire; 4]) -> Vec<Wire> {
    let mut out = Vec::with_capacity(32);
    for w in 0..4 {
        for j in 0..8 {
            out.push(be_byte(b, hash[w], j));
        }
    }
    out
}
fn mux16(b: &CircuitBuilder, idx: Wire, vals: &[Wire]) -> Wire {
    let mut out = b.add_constant_64(0);
    for (j, v) in vals.iter().enumerate() {
        out = b.select(b.icmp_eq(idx, b.add_constant_64(j as u64)), *v, out);
    }
    out
}
/// Bitmap bit j (constant) as an LSB 0/1 (for arithmetic like popcounts).
fn bit01(b: &CircuitBuilder, bitmap: Wire, j: u32) -> Wire {
    b.band(b.shr(bitmap, j), b.add_constant_64(1))
}
/// Bitmap bit j (constant) as an MSB-bool. NOTE: framework booleans are
/// MSB-bools (select/assert_true read bit 63); a bare `band(shr,1)` yields an
/// LSB 0/1 that silently ANDs to zero — normalize with shl(..,63).
fn bit(b: &CircuitBuilder, bitmap: Wire, j: u32) -> Wire {
    b.shl(bit01(b, bitmap, j), 63)
}
/// Bitmap bit at a wire nibble (MSB-bool).
fn bit_at(b: &CircuitBuilder, bitmap: Wire, nib: Wire) -> Wire {
    let bits: Vec<Wire> = (0..16u32).map(|j| bit(b, bitmap, j)).collect();
    mux16(b, nib, &bits)
}
fn band_bit(b: &CircuitBuilder, byte: Wire, i: u32) -> Wire {
    b.shl(b.band(b.shr(byte, i), b.add_constant_64(1)), 63)
}

/// Key nibble at constant position k: k<2 -> 0 (the 0x00 prefix), else
/// nibble (k-2) of the name bytes (high nibble first per byte).
fn key_nibble(b: &CircuitBuilder, name: &[Wire; 8], k: usize) -> Wire {
    if k < 2 {
        return b.add_constant_64(0);
    }
    let n = k - 2;
    let word = name[(n / 2) / 8];
    let byt = le_byte(b, word, ((n / 2) % 8) as u32);
    if n % 2 == 0 {
        b.shr(byt, 4)
    } else {
        b.band(byt, b.add_constant_64(15))
    }
}
/// Key nibble at a WIRE position (>= 2).
fn key_nibble_at(b: &CircuitBuilder, name: &[Wire; 8], pos: Wire) -> Wire {
    let (n, _) = b.isub_bin_bout(pos, b.add_constant_64(2), b.add_constant_64(0));
    let byte_idx = b.shr(n, 1);
    let hi = b.band(n, b.add_constant_64(1));
    let mut word = b.add_constant_64(0);
    for w in 0..8usize {
        word = b.select(b.icmp_eq(b.shr(byte_idx, 3), b.add_constant_64(w as u64)), name[w], word);
    }
    let mut byt = b.add_constant_64(0);
    for t in 0..8u32 {
        byt = b.select(
            b.icmp_eq(b.band(byte_idx, b.add_constant_64(7)), b.add_constant_64(t as u64)),
            le_byte(b, word, t),
            byt,
        );
    }
    b.select(hi, b.shr(byt, 4), b.band(byt, b.add_constant_64(15)))
}

/// Reconstruct + hash one branch node's node_ser; returns its sha256 words.
/// `has` gates the pure-shape asserts (an empty table witnesses a zeroed
/// chain; those constraints are vacuous then).
fn hash_branch(b: &CircuitBuilder, node: &BranchNode, name: &str, has: Wire) -> [Wire; 4] {
    let zero = b.add_constant_64(0);
    // ranks[j] = popcount of bits below j (prefix sums).
    let mut ranks = vec![zero];
    let mut acc = zero;
    for j in 0..16u32 {
        acc = b.iadd(acc, bit01(b, node.bitmap, j)).0;
        ranks.push(acc);
    }
    let k = acc;
    let mem_base = b.iadd(b.add_constant_64(3), b.shl(k, 5)).0;
    let len = b.iadd(mem_base, b.add_constant_64(8)).0;
    b.assert_false(format!("{name}-kids-overflow"), b.icmp_ugt(k, b.add_constant_64(10)));
    b.assert_true(format!("{name}-kids-nonempty"), b.bor(b.icmp_uge(k, b.add_constant_64(1)), b.bnot(has)));
    // Hoist all child digest bytes once.
    let kid_digests: Vec<Vec<Wire>> = node.kids.iter().map(|h| digest_bytes(b, h)).collect();
    let mem_bytes: Vec<Wire> = (0..8u32).map(|i| le_byte(b, node.mem, i)).collect();
    let mut bytes: Vec<Wire> = vec![
        b.add_constant_64(1),
        le_byte(b, node.bitmap, 0),
        le_byte(b, node.bitmap, 1),
    ];
    for p in 3..BRANCH_BYTES {
        let pw = b.add_constant_64(p as u64);
        let q = (p - 3) / 32;
        let m = (p - 3) % 32;
        // Child byte: the set-bit kid whose rank == q places its digest byte m.
        let mut child_byte = zero;
        for j in 0..16usize {
            let placed = b.band(
                b.icmp_eq(ranks[j], b.add_constant_64(q as u64)),
                bit(b, node.bitmap, j as u32),
            );
            child_byte = b.select(placed, kid_digests[j][m], child_byte);
        }
        // Mem byte: offset = p - (3+32k) in 0..8, else zero.
        let (offset, _) = b.isub_bin_bout(pw, mem_base, b.add_constant_64(0));
        let mut mem_byte = zero;
        for mm in 0..8usize {
            mem_byte = b.select(b.icmp_eq(offset, b.add_constant_64(mm as u64)), mem_bytes[mm], mem_byte);
        }
        bytes.push(b.select(b.icmp_ult(pw, mem_base), child_byte, mem_byte));
    }
    let vec = ByteVec::new_with_len_range(pack_bytes(b, &bytes), len, 0..=BRANCH_BYTES);
    tight_sha::sha256_tight(&b.subcircuit(format!("hash-{name}")), &vec, BRANCH_BYTES)
}

/// Reconstruct + hash the ext node.
fn hash_ext(b: &CircuitBuilder, node: &ExtNode, has: Wire) -> [Wire; 4] {
    let zero = b.add_constant_64(0);
    b.assert_true("ext-hp-len-range", b.bor(b.band(
        b.icmp_uge(node.hp_len, b.add_constant_64(1)),
        b.icmp_ule(node.hp_len, b.add_constant_64(EXT_HP_MAX as u64)),
    ), b.bnot(has)));
    let len = b.iadd(b.iadd(b.add_constant_64(5), node.hp_len).0, b.add_constant_64(40)).0;
    let child_digest = digest_bytes(b, &node.child);
    let mem_bytes: Vec<Wire> = (0..8u32).map(|i| le_byte(b, node.mem, i)).collect();
    let mut bytes: Vec<Wire> = vec![b.add_constant_64(3)];
    for i in 0..4u32 {
        bytes.push(le_byte(b, node.hp_len, i));
    }
    for p in 5..EXT_BYTES {
        let pw = b.add_constant_64(p as u64);
        let (off, _) = b.isub_bin_bout(pw, b.add_constant_64(5), b.add_constant_64(0));
        let mut hp_byte = zero;
        for q in 0..EXT_HP_MAX {
            hp_byte = b.select(b.icmp_eq(off, b.add_constant_64(q as u64)), node.hp[q], hp_byte);
        }
        let in_hp = b.icmp_ult(off, node.hp_len);
        let (coff, _) = b.isub_bin_bout(off, node.hp_len, b.add_constant_64(0));
        let mut mid_byte = zero;
        for c in 0..32usize {
            mid_byte = b.select(b.icmp_eq(coff, b.add_constant_64(c as u64)), child_digest[c], mid_byte);
        }
        let (moff, _) = b.isub_bin_bout(coff, b.add_constant_64(32), b.add_constant_64(0));
        let mut mem_byte = zero;
        for mm in 0..8usize {
            mem_byte = b.select(b.icmp_eq(moff, b.add_constant_64(mm as u64)), mem_bytes[mm], mem_byte);
        }
        let after_hp = b.select(b.icmp_ult(coff, b.add_constant_64(32)), mid_byte, mem_byte);
        bytes.push(b.select(in_hp, hp_byte, after_hp));
    }
    let vec = ByteVec::new_with_len_range(pack_bytes(b, &bytes), len, 0..=EXT_BYTES);
    tight_sha::sha256_tight(&b.subcircuit("hash-ext"), &vec, EXT_BYTES)
}

/// Reconstruct + hash one row's leaf (range asserts gated on active).
fn hash_leaf(b: &CircuitBuilder, w: &LeafWitness, r: usize, act: Wire) -> [Wire; 4] {
    let zero = b.add_constant_64(0);
    let inactive = b.bnot(act);
    let range_ok = b.band(
        b.icmp_uge(w.hp_len, b.add_constant_64(1)),
        b.icmp_ule(w.hp_len, b.add_constant_64(LEAF_HP_MAX as u64)),
    );
    b.assert_true(format!("leaf{r}-hp-len-range"), b.bor(range_ok, inactive));
    let len = b.iadd(b.iadd(b.add_constant_64(5), w.hp_len).0, b.add_constant_64(44)).0;
    let digest = digest_bytes(b, &w.vref_hash);
    let mem_bytes: Vec<Wire> = (0..8u32).map(|i| le_byte(b, w.mem, i)).collect();
    let mut bytes: Vec<Wire> = vec![zero]; // leaf tag 0
    for i in 0..4u32 {
        bytes.push(le_byte(b, w.hp_len, i));
    }
    for p in 5..LEAF_BYTES {
        let pw = b.add_constant_64(p as u64);
        let (off, _) = b.isub_bin_bout(pw, b.add_constant_64(5), b.add_constant_64(0));
        let mut hp_byte = zero;
        for q in 0..LEAF_HP_MAX {
            hp_byte = b.select(b.icmp_eq(off, b.add_constant_64(q as u64)), w.hp[q], hp_byte);
        }
        let in_hp = b.icmp_ult(off, w.hp_len);
        let (coff, _) = b.isub_bin_bout(off, w.hp_len, b.add_constant_64(0));
        let mut vref_byte = zero;
        for c in 0..4usize {
            vref_byte = b.select(b.icmp_eq(coff, b.add_constant_64(c as u64)), le_byte(b, w.vref_len, c as u32), vref_byte);
        }
        for c in 0..32usize {
            vref_byte = b.select(b.icmp_eq(coff, b.add_constant_64((4 + c) as u64)), digest[c], vref_byte);
        }
        let (moff, _) = b.isub_bin_bout(coff, b.add_constant_64(36), b.add_constant_64(0));
        let mut mem_byte = zero;
        for mm in 0..8usize {
            mem_byte = b.select(b.icmp_eq(moff, b.add_constant_64(mm as u64)), mem_bytes[mm], mem_byte);
        }
        let after_hp = b.select(b.icmp_ult(coff, b.add_constant_64(36)), vref_byte, mem_byte);
        bytes.push(b.select(in_hp, hp_byte, after_hp));
    }
    let vec = ByteVec::new_with_len_range(pack_bytes(b, &bytes), len, 0..=LEAF_BYTES);
    tight_sha::sha256_tight(&b.subcircuit(format!("hash-leaf-{r}")), &vec, LEAF_BYTES)
}

/// hexPrefix fragment nibble count: even -> 2*hp_len-2; odd -> 2*hp_len-1.
/// (hp_len >= 1 is range-checked, so the subtraction never underflows.)
fn frag_nibs(b: &CircuitBuilder, hp_len: Wire, hp0: Wire) -> Wire {
    let odd = band_bit(b, hp0, 4);
    let dbl = b.shl(hp_len, 1);
    let (even, _) = b.isub_bin_bout(dbl, b.add_constant_64(2), b.add_constant_64(0));
    let (oddc, _) = b.isub_bin_bout(dbl, b.add_constant_64(1), b.add_constant_64(0));
    b.select(odd, oddc, even)
}

/// Fragment nibble i decoded from hexPrefix bytes (odd flag from hp[0] bit 4).
fn frag_nibble(b: &CircuitBuilder, hp: &[Wire], i: u32, odd: Wire) -> Wire {
    let pick = |byte: Wire, hi: bool| if hi { b.shr(byte, 4) } else { b.band(byte, b.add_constant_64(15)) };
    // even: nib i lives in byte 1 + i/2 (hi if i even)
    let ebyte = hp.get(1 + i as usize / 2).copied().unwrap_or_else(|| b.add_constant_64(0));
    let e = pick(ebyte, i % 2 == 0);
    // odd: nib 0 = hp[0] low; nib i>=1 in byte (i+1)/2 (hi if i odd)
    let o = if i == 0 {
        b.band(hp[0], b.add_constant_64(15))
    } else {
        let obyte = hp.get((i as usize + 1) / 2).copied().unwrap_or_else(|| b.add_constant_64(0));
        pick(obyte, i % 2 == 1)
    };
    b.select(odd, o, e)
}

/// Witness wires. Call FIRST so the root words lead the public statement.
pub fn build(b: &CircuitBuilder) -> TrieWitness {
    let root: [Wire; 4] = core::array::from_fn(|_| b.add_inout());
    let branches: [BranchNode; 4] = core::array::from_fn(|i| {
        let s = b.subcircuit(format!("branch-{i}"));
        BranchNode {
            bitmap: s.add_witness(),
            kids: core::array::from_fn(|_| core::array::from_fn(|_| s.add_witness())),
            mem: s.add_witness(),
        }
    });
    let ext = {
        let s = b.subcircuit("ext");
        ExtNode {
            hp_len: s.add_witness(),
            hp: core::array::from_fn(|_| s.add_witness()),
            child: core::array::from_fn(|_| s.add_witness()),
            mem: s.add_witness(),
        }
    };
    let mut rows = Vec::with_capacity(ACCOUNT_SLOTS);
    for r in 0..ACCOUNT_SLOTS {
        let s = b.subcircuit(format!("trie-row-{r}"));
        rows.push(LeafWitness {
            hp_len: s.add_witness(),
            hp: core::array::from_fn(|_| s.add_witness()),
            vref_len: s.add_witness(),
            vref_hash: core::array::from_fn(|_| s.add_witness()),
            mem: s.add_witness(),
            code: core::array::from_fn(|_| s.add_witness()),
        });
    }
    TrieWitness { branches, ext, rows, root }
}

/// All trie constraints. The ledger must be built (row wires exist).
///
/// Empty-table case: with no active rows there is no chain to witness (the
/// exporter emits a zeroed chain). The root binding and chain-structure
/// constraints are gated on the has-accounts bit; for an empty table the
/// public root is checked host-side only (documented trust boundary) — the
/// proof makes no trie claim because the table makes no value claims.
pub fn constrain(b: &CircuitBuilder, ledger: &Ledger, wit: &TrieWitness) {
    let zero = b.add_constant_64(0);
    // has-accounts: OR of row active bits (MSB-bool).
    let mut has = b.add_constant_64(0);
    for r in 0..ACCOUNT_SLOTS {
        has = b.bor(has, b.shl(ledger.rows[r].active, 63));
    }
    let no_has = b.bnot(has);
    // Shared hashes.
    let bh: Vec<[Wire; 4]> = wit.branches.iter().enumerate().map(|(i, n)| hash_branch(b, n, &format!("branch-{i}"), has)).collect();
    let eh = hash_ext(b, &wit.ext, has);
    // Root binding (has=1): hash(chain top) == public prev_state_root.
    for j in 0..4 {
        b.assert_eq_cond(format!("trie-root-{j}"), wit.root[j], bh[0][j], has);
    }
    // Fixed-prefix links (has=1): branch0@nib0 -> branch1, branch1@nib0 ->
    // branch2, ext child -> branch3. (Account keys start 0x00: key[0]=key[1]=0.)
    b.assert_true("b0-bit0", b.bor(bit(b, wit.branches[0].bitmap, 0), no_has));
    b.assert_true("b1-bit0", b.bor(bit(b, wit.branches[1].bitmap, 0), no_has));
    for j in 0..4 {
        b.assert_eq_cond(format!("link-b0-{j}"), wit.branches[0].kids[0][j], bh[1][j], has);
        b.assert_eq_cond(format!("link-b1-{j}"), wit.branches[1].kids[0][j], bh[2][j], has);
        b.assert_eq_cond(format!("link-ext-{j}"), wit.ext.child[j], bh[3][j], has);
    }
    // Shared witness must be zero when the table is empty.
    let mut shared_words: Vec<Wire> = vec![];
    for n in &wit.branches {
        shared_words.push(n.bitmap);
        shared_words.extend(n.kids.iter().flat_map(|h| h.iter().copied()));
        shared_words.push(n.mem);
    }
    shared_words.push(wit.ext.hp_len);
    shared_words.extend(wit.ext.hp.iter().copied());
    shared_words.extend(wit.ext.child.iter().copied());
    shared_words.push(wit.ext.mem);
    for (i, w) in shared_words.iter().enumerate() {
        b.assert_eq_cond(format!("shared-zero-{i}"), *w, zero, no_has);
    }
    let ext_odd = band_bit(b, wit.ext.hp[0], 4);
    let f_ext = frag_nibs(b, wit.ext.hp_len, wit.ext.hp[0]);
    for r in 0..ACCOUNT_SLOTS {
        let row = &ledger.rows[r];
        let w = &wit.rows[r];
        let act = b.shl(row.active, 63);
        let inactive = b.bnot(act);
        let lh = hash_leaf(b, w, r, act);
        // branch2: row's key[2] must be set; its child == ext hash (active rows).
        let nib2 = key_nibble(b, &row.name, 2);
        b.assert_true(
            format!("r{r}-b2-bit"),
            b.bor(b.band(bit_at(b, wit.branches[2].bitmap, nib2), act), inactive),
        );
        for j in 0..4 {
            let sel = mux16(b, nib2, &wit.branches[2].kids.iter().map(|k| k[j]).collect::<Vec<_>>());
            b.assert_eq_cond(format!("r{r}-b2-link-{j}"), sel, eh[j], act);
        }
        // branch3: the row's final nibble (position 3+F_ext) must be set;
        // its child == the row's leaf hash (active rows).
        let nib_pos = b.iadd(b.add_constant_64(3), f_ext).0;
        let nib = key_nibble_at(b, &row.name, nib_pos);
        b.assert_true(
            format!("r{r}-b3-bit"),
            b.bor(b.band(bit_at(b, wit.branches[3].bitmap, nib), act), inactive),
        );
        for j in 0..4 {
            let sel = mux16(b, nib, &wit.branches[3].kids.iter().map(|k| k[j]).collect::<Vec<_>>());
            b.assert_eq_cond(format!("r{r}-leaf-link-{j}"), sel, lh[j], act);
        }
        // Value binding: 72B value = table balance/locked + witness code +
        // table storage (low word). vref == u32le(72) || sha256(value).
        let value_words = [
            row.balance[0], row.balance[1],
            row.locked[0], row.locked[1],
            w.code[0], w.code[1], w.code[2], w.code[3],
            row.storage[0],
        ];
        let mut vb: Vec<Wire> = Vec::with_capacity(72);
        for word in &value_words {
            for i in 0..8u32 {
                vb.push(le_byte(b, *word, i));
            }
        }
        let vvec = ByteVec::new_const_len(b, pack_bytes(b, &vb), 72);
        let vh = tight_sha::sha256_tight(&b.subcircuit(format!("r{r}-value-hash")), &vvec, 72);
        b.assert_eq_cond(format!("r{r}-vref-len"), w.vref_len, b.add_constant_64(72), act);
        b.assert_eq_cond(format!("r{r}-storage-hi"), row.storage[1], zero, act);
        for j in 0..4 {
            b.assert_eq_cond(format!("r{r}-vref-hash-{j}"), w.vref_hash[j], vh[j], act);
        }
        // Ext fragment correspondence: frag nibble i == key[3+i].
        for i in 0..EXT_FRAG_NIBS {
            let frag = frag_nibble(b, &wit.ext.hp, i as u32, ext_odd);
            let in_frag = b.band(b.icmp_ult(b.add_constant_64(i as u64), f_ext), act);
            b.assert_eq_cond(format!("r{r}-ext-frag-{i}"), frag, key_nibble(b, &row.name, 3 + i), in_frag);
        }
        // Leaf fragment correspondence: frag nibble i == key[4+F_ext+i].
        let leaf_odd = band_bit(b, w.hp[0], 4);
        let f_leaf = frag_nibs(b, w.hp_len, w.hp[0]);
        for i in 0..LEAF_FRAG_NIBS {
            let pos = b.iadd(b.iadd(b.add_constant_64(4), f_ext).0, b.add_constant_64(i as u64)).0;
            let frag = frag_nibble(b, &w.hp, i as u32, leaf_odd);
            let in_frag = b.band(b.icmp_ult(b.add_constant_64(i as u64), f_leaf), act);
            b.assert_eq_cond(format!("r{r}-leaf-frag-{i}"), frag, key_nibble_at(b, &row.name, pos), in_frag);
        }
        // Path end: 4 + F_ext + F_leaf == 2*(1+name_len).
        let consumed = b.iadd(b.iadd(b.add_constant_64(4), f_ext).0, f_leaf).0;
        let key_len = b.shl(b.iadd(row.name_len, b.add_constant_64(1)).0, 1);
        b.assert_eq_cond(format!("r{r}-path-end"), consumed, key_len, act);
        // Inactive rows: leaf witness words all zero.
        let fields: Vec<Wire> = std::iter::once(w.hp_len)
            .chain(w.hp.iter().copied())
            .chain(std::iter::once(w.vref_len))
            .chain(w.vref_hash.iter().copied())
            .chain(std::iter::once(w.mem))
            .chain(w.code.iter().copied())
            .collect();
        for (i, f) in fields.iter().enumerate() {
            b.assert_eq_cond(format!("r{r}-leaf-inactive-{i}"), *f, zero, inactive);
        }
    }
}
