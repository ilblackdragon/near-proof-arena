//! Constants shared by the AIRs, the trace generator and the verifier.

use crate::spec::G;

/// Message kinds. A SHA-256 message is identified on the buses by the field
/// element `msg = kind * 2^20 + index` (index < 2^20 is guaranteed by the
/// trace-height caps the verifier enforces, see `verifier.rs`).
pub const MSG_SHIFT: u32 = 1 << 20;
pub const K_RC: u32 = 1; // receipts commitment message (index 0)
pub const K_PEO: u32 = 2; // PartialExecutionOutcome of receipt r
pub const K_LEAF: u32 = 3; // outcome merkle leaf of receipt r
pub const K_RID: u32 = 4; // refund-id preimage of receipt r
pub const K_MRK: u32 = 5; // outcome merkle inner node (MRK row index)
pub const K_RF: u32 = 6; // refunds commitment message (index 0)
pub const K_NPRE: u32 = 7; // trie node N, pre-state serialization
pub const K_NPOST: u32 = 8; // trie node N, post-state serialization
pub const K_VPRE: u32 = 9; // account k value, pre-state (72 bytes)
pub const K_VPOST: u32 = 10; // account k value, post-state (72 bytes)

pub const fn msg_id(kind: u32, idx: u32) -> u32 {
    kind * MSG_SHIFT + idx
}

/// Public values = the 232 fixed-width bytes at the end of `claim.bin`
/// (shard_id .. tokens_burnt_total), one field element per byte.
pub const PV_SHARD: usize = 0;
pub const PV_HEIGHT: usize = 8;
pub const PV_BGP: usize = 16;
pub const PV_GASLIM: usize = 32;
pub const PV_PRE: usize = 40;
pub const PV_N: usize = 72;
pub const PV_RC: usize = 76;
pub const PV_POST: usize = 108;
pub const PV_OUT: usize = 140;
pub const PV_NREF: usize = 172;
pub const PV_RFC: usize = 176;
pub const PV_GAS: usize = 208;
pub const PV_TOK: usize = 216;
pub const NUM_PV: usize = 232;

/// Bus names. "perm" buses are multiset equalities (both sides weight 1);
/// "lookup" buses are table lookups (provider multiplicities are free).
pub const BUS_BYTES: &str = "np/bytes"; // perm   (msg, pos, byte)
pub const BUS_CHAIN: &str = "np/chain"; // perm   (msg, blk, cnt, seen, h[16])
pub const BUS_DIGEST: &str = "np/digest"; // lookup (msg, limb[16])
pub const BUS_RANGE8: &str = "np/range8"; // lookup (x)          x < 2^8
pub const BUS_RANGE16: &str = "np/range16"; // lookup (x)        x < 2^16
pub const BUS_CLASS: &str = "np/class"; // lookup (c, class)
pub const BUS_NIB: &str = "np/nib"; // lookup (c, hi, lo)
pub const BUS_ACCT: &str = "np/acct"; // lookup (k, len, packed[22], locked[16], storage[8])
pub const BUS_MEM: &str = "np/mem"; // perm   (k, t, amount[16])
pub const BUS_RIDS: &str = "np/rids"; // perm   (rid[32])
pub const BUS_MPOS: &str = "np/mpos"; // lookup (level, index, msg)
pub const BUS_KEYNIB: &str = "np/keynib"; // perm (k, t, nib)
pub const BUS_EDGE: &str = "np/edge"; // lookup (N, i, nib, N', i')
pub const BUS_EPS: &str = "np/eps"; // lookup (N, i, N', i')
pub const BUS_FINAL: &str = "np/final"; // perm  (k, N, i)
pub const BUS_VSLOT: &str = "np/vslot"; // perm  (N, i, k)

pub const PERM_BUSES: &[&str] =
    &[BUS_BYTES, BUS_CHAIN, BUS_MEM, BUS_RIDS, BUS_KEYNIB, BUS_FINAL, BUS_VSLOT];
pub const LOOKUP_BUSES: &[&str] = &[
    BUS_DIGEST, BUS_RANGE8, BUS_RANGE16, BUS_CLASS, BUS_NIB, BUS_ACCT, BUS_MPOS, BUS_EDGE, BUS_EPS,
];

/// `G` as little-endian bytes (G < 2^40).
pub const G_BYTES: [u8; 5] = {
    let b = (G as u64).to_le_bytes();
    [b[0], b[1], b[2], b[3], b[4]]
};
/// 10^19 (storage_amount_per_byte) as little-endian bytes.
pub const STORAGE_PRICE_BYTES: [u8; 8] = 10_000_000_000_000_000_000u64.to_le_bytes();
pub const MAX_ACCOUNT_LEN: usize = 64;
/// Packed account id: 22 limbs of 3 bytes.
pub const PACK_LIMBS: usize = 22;
/// HP key bytes after the flag byte (keys are <= 130 nibbles).
pub const MAX_KEY_BYTES: usize = 65;
pub const MAX_WITNESS_BYTES: u32 = 3_000_000;

/// Character classes for account ids (`BUS_CLASS`): 0 = alnum not hex
/// (g-z), 1 = hex digit (0-9, a-f), 2 = separator (- _ .), 3 = invalid.
pub const fn char_class(c: u8) -> u8 {
    match c {
        b'0'..=b'9' | b'a'..=b'f' => 1,
        b'g'..=b'z' => 0,
        b'-' | b'_' | b'.' => 2,
        _ => 3,
    }
}
