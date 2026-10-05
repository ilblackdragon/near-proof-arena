//! Message kinds, buses, walk symbols and public-input offsets of `nearAir`
//! (`ZkFormal/Near/Ids.lean`, `Near/Air.lean`).

pub const K_RC: usize = 1;
pub const K_RF: usize = 2;
pub const K_PEO: usize = 3;
pub const K_LEAF: usize = 4;
pub const K_RID: usize = 5;
pub const K_MRK: usize = 6;
pub const K_NPRE: usize = 7;
pub const K_NPOST: usize = 8;
pub const K_VPRE: usize = 9;
pub const K_VPOST: usize = 10;

/// `msgId kind idx = kind + 16·idx`.
pub fn msg_id(kind: usize, idx: usize) -> usize { kind + 16 * idx }

pub const B_BYTES: usize = 0;
pub const B_DIGEST: usize = 1;
pub const B_PARENT: usize = 2;
pub const B_VSLOT: usize = 3;
pub const B_EDGE: usize = 4;
pub const B_KEYNIB: usize = 5;
pub const B_FINAL: usize = 6;
pub const B_MEM: usize = 7;
pub const B_RIDS: usize = 8;
pub const B_MPOS: usize = 9;
pub const NUM_BUSES: usize = 10;

/// Key exhausted: the walk enters the value slot.
pub const SYM_END: usize = 16;
/// Extension end → child (spec-level walks only).
pub const SYM_EPS: usize = 17;
/// The walk's first step, root → its walk target.
pub const SYM_START: usize = 18;

pub const PV_FMT: usize = 0;
pub const PV_STMT: usize = 23;
pub const PV_PV: usize = 62;
pub const PV_CHAIN: usize = 66;
pub const PV_SHARD: usize = 77;
pub const PV_HEIGHT: usize = 85;
pub const PV_BGP: usize = 93;
pub const PV_GASLIM: usize = 109;
pub const PV_PRE: usize = 117;
pub const PV_N: usize = 149;
pub const PV_RC: usize = 153;
pub const PV_POST: usize = 185;
pub const PV_OUT: usize = 217;
pub const PV_NREF: usize = 249;
pub const PV_RFC: usize = 253;
pub const PV_GAS: usize = 285;
pub const PV_TOK: usize = 293;
pub const NUM_PUB: usize = 309;

/// Table indices in `nearAir`.
pub const T_SHA: usize = 0;
pub const T_NODE: usize = 1;
pub const T_WALK: usize = 2;
pub const T_RCPT: usize = 3;
pub const T_ACCT: usize = 4;
pub const T_MRK: usize = 5;
pub const T_SORT: usize = 6;
