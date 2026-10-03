//! Proof format `reexec-npai-v1` (normative definition:
//! `formal/ReexecNpai/Codec.lean`, `encodeProof`).
//!
//! ```text
//! proof = u32 n ‖ Receipt × n                (nearcore borsh = NearSpec.encodeReceipts)
//!         ‖ u32 N ‖ rec × N                   (revealed trie nodes, post-order; root last)
//! rec   = 1 ‖ u32 |v| ‖ v ‖ pre(leaf)               leaf, revealed value
//!       | 2 ‖ pre(leaf)                              leaf, value by reference
//!       | 3 ‖ u8 e ‖ pre(ext)                        extension; e = 1 iff the child is revealed
//!       | 4 ‖ u16 ex ‖ pre(branch)                   branch without value
//!       | 5 ‖ u32 |v| ‖ v ‖ u16 ex ‖ pre(branch')    branch, revealed value
//!       | 6 ‖ u16 ex ‖ pre(branch')                  branch, value by reference
//! pre(leaf)    = 0 ‖ u32 |hp| ‖ hp ‖ u32 len ‖ h32 ‖ u64 mem
//! pre(ext)     = 3 ‖ u32 |hp| ‖ hp ‖ h32 ‖ u64 mem
//! pre(branch)  = 1 ‖ u16 bm ‖ h32 × popcount bm ‖ u64 mem
//! pre(branch') = 2 ‖ u32 len ‖ h32 ‖ u16 bm ‖ h32 × popcount bm ‖ u64 mem
//! ```
//!
//! `pre(·)` is nearcore's `RawTrieNodeWithSize` serialization except at
//! placeholders (the hash of a revealed value or of a revealed child), which
//! the honest prover writes as zeros and the verifier overwrites.

use crate::trie::{hex_prefix, Kind, PTrie, Slot, NONE};
use crate::wire::Writer;

const ZERO32: [u8; 32] = [0; 32];

fn revealed(t: &PTrie<'_>, i: u32) -> bool {
    !matches!(t.nodes[i as usize].kind, Kind::Hash)
}

fn count(t: &PTrie<'_>, i: u32) -> u32 {
    match &t.nodes[i as usize].kind {
        Kind::Hash => 0,
        Kind::Leaf { .. } => 1,
        Kind::Ext { child, .. } => count(t, *child) + 1,
        Kind::Branch { kids, .. } => kids.iter().filter(|&&c| c != NONE).map(|&c| count(t, c)).sum::<u32>() + 1,
    }
}

/// The 32-byte slot a child occupies in its parent's preimage.
fn slot_of(t: &PTrie<'_>, c: u32) -> [u8; 32] {
    if revealed(t, c) {
        ZERO32
    } else {
        t.nodes[c as usize].hash
    }
}

/// `u32 len ‖ h32` of a value slot (placeholder hash for a revealed value).
fn ref_part(w: &mut Writer, s: &Slot<'_>) {
    match s {
        Slot::Val { orig, .. } => {
            w.u32(orig.len() as u32).raw(&ZERO32);
        }
        Slot::Ref { len, hash } => {
            w.u32(*len).raw(hash);
        }
    }
}

fn write_post(w: &mut Writer, t: &PTrie<'_>, i: u32) {
    let n = &t.nodes[i as usize];
    match &n.kind {
        Kind::Hash => {}
        Kind::Leaf { key, slot } => {
            match slot {
                Slot::Val { orig, .. } => {
                    w.u8(1).bytes(orig);
                }
                Slot::Ref { .. } => {
                    w.u8(2);
                }
            }
            w.u8(0);
            hex_prefix(key, true, w);
            ref_part(w, slot);
            w.u64(n.mem);
        }
        Kind::Ext { key, child } => {
            write_post(w, t, *child);
            w.u8(3).u8(revealed(t, *child) as u8).u8(3);
            hex_prefix(key, false, w);
            w.raw(&slot_of(t, *child));
            w.u64(n.mem);
        }
        Kind::Branch { value, kids } => {
            let (mut bm, mut ex) = (0u16, 0u16);
            for (j, &c) in kids.iter().enumerate() {
                if c != NONE {
                    bm |= 1 << j;
                    if revealed(t, c) {
                        ex |= 1 << j;
                        write_post(w, t, c);
                    }
                }
            }
            match value {
                None => {
                    w.u8(4);
                }
                Some(Slot::Val { orig, .. }) => {
                    w.u8(5).bytes(orig);
                }
                Some(Slot::Ref { .. }) => {
                    w.u8(6);
                }
            }
            w.u16(ex);
            match value {
                None => {
                    w.u8(1);
                }
                Some(s) => {
                    w.u8(2);
                    ref_part(w, s);
                }
            }
            w.u16(bm);
            for &c in kids {
                if c != NONE {
                    w.raw(&slot_of(t, c));
                }
            }
            w.u64(n.mem);
        }
    }
}

/// `encTrie`: `u32 N ‖ records` of the partial trie rooted at `root`.
pub fn write_trie(w: &mut Writer, t: &PTrie<'_>, root: u32) {
    w.u32(count(t, root));
    write_post(w, t, root);
}
