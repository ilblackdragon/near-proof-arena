//! Proof format `reexec-witness-v1` (normative definition:
//! `formal/ReexecWitness/ProofCodec.lean`, `encodeProof`).
//!
//! ```text
//! proof   = u32 n ‖ Receipt × n          (nearcore borsh = NearSpec.encodeReceipts)
//!           ‖ node                        (partial pre-state trie)
//! node    = 0 ‖ hash32                                    -- unrevealed subtree
//!         | 1 ‖ key ‖ u32 len ‖ value ‖ u64 mem          -- leaf, revealed value
//!         | 2 ‖ key ‖ u32 len ‖ hash32 ‖ u64 mem         -- leaf, value by ref
//!         | 3 ‖ key ‖ node ‖ u64 mem                     -- extension
//!         | 4 ‖ u16 bitmap ‖ node × popcount ‖ u64 mem   -- branch, no value
//!         | 5 ‖ u32 len ‖ value ‖ u16 bitmap ‖ node × popcount ‖ u64 mem
//!         | 6 ‖ u32 len ‖ hash32 ‖ u16 bitmap ‖ node × popcount ‖ u64 mem
//! key     = u32 k ‖ ceil(k/2) bytes, nibbles high-first; an odd last nibble
//!           is the high half of the last byte, whose low half must be 0
//! ```
//! Every value is little endian; decoding is strict (no trailing bytes, all
//! nibbles < 16, canonical padding, children in index order).

use crate::trie::{Kind, PTrie, Slot, NONE};
use crate::wire::{Reader, WResult, WireError, Writer};

pub fn write_key(w: &mut Writer, nibs: &[u8]) {
    w.u32(nibs.len() as u32);
    let mut it = nibs.chunks(2);
    for p in &mut it {
        w.u8(if p.len() == 2 { p[0] * 16 + p[1] } else { p[0] * 16 });
    }
}

pub fn read_key(r: &mut Reader<'_>) -> WResult<Vec<u8>> {
    let k = r.u32("key len")? as usize;
    let packed = r.take(k.div_ceil(2), "key")?;
    let mut v = Vec::with_capacity(k + 1);
    for &b in packed {
        v.push(b >> 4);
        v.push(b & 15);
    }
    if k % 2 == 1 {
        if v.pop() != Some(0) {
            return Err(WireError("non-canonical key padding"));
        }
    }
    Ok(v)
}

/// Encode the *pre-state* partial trie rooted at `i`.
pub fn write_node(w: &mut Writer, t: &PTrie<'_>, i: u32) {
    let n = &t.nodes[i as usize];
    match &n.kind {
        Kind::Hash => {
            w.u8(0).raw(&n.hash);
            return;
        }
        Kind::Leaf { key, slot } => {
            match slot {
                Slot::Val { orig, .. } => {
                    w.u8(1);
                    write_key(w, key);
                    w.bytes(orig);
                }
                Slot::Ref { len, hash } => {
                    w.u8(2);
                    write_key(w, key);
                    w.u32(*len).raw(hash);
                }
            }
        }
        Kind::Ext { key, child } => {
            w.u8(3);
            write_key(w, key);
            write_node(w, t, *child);
        }
        Kind::Branch { value, kids } => {
            match value {
                None => {
                    w.u8(4);
                }
                Some(Slot::Val { orig, .. }) => {
                    w.u8(5).bytes(orig);
                }
                Some(Slot::Ref { len, hash }) => {
                    w.u8(6).u32(*len).raw(hash);
                }
            }
            let mut bm = 0u16;
            for (j, &c) in kids.iter().enumerate() {
                if c != NONE {
                    bm |= 1 << j;
                }
            }
            w.u16(bm);
            for &c in kids {
                if c != NONE {
                    write_node(w, t, c);
                }
            }
        }
    }
    w.u64(n.mem);
}
