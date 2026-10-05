//! NEAR-side helpers of the `rcpt` table (`ZkFormal/Near/Render/RcptSim.lean`):
//! the bytes of the messages `rcpt` emits.  `leaf_bytes` is also used by `mrk`.

use super::ids::*;
use super::info::*;
use super::spec::*;

/// `peoBytes I r = (outcomeOf c r).partialEncode`.
pub fn peo_bytes(i: &Info, r: usize) -> Bytes { i.e.outcome_of(&i.c, r).partial_encode() }

/// `leafBytes I r = u32 2 ‖ receiptId ‖ sha256 (peoBytes r)`.
pub fn leaf_bytes(i: &Info, r: usize) -> Bytes {
    [le_bytes(4, 2), i.e.rc(r).receipt_id, sha_n(&peo_bytes(i, r))].concat()
}

/// `hasRefund I r`.
pub fn has_refund(i: &Info, r: usize) -> bool { !i.e.refund_of(&i.c, r).is_empty() }

/// `ridBytes I r = receiptId ‖ u64 height ‖ u64 0`.
pub fn rid_bytes(i: &Info, r: usize) -> Bytes {
    [i.e.rc(r).receipt_id, le_bytes(8, i.c.block_height as u128), le_bytes(8, 0)].concat()
}

/// `rcBytes I = u64 shard ‖ encodeReceipts rs`.
pub fn rc_bytes(i: &Info) -> Bytes { [u64b(i.c.shard_id as u128), encode_receipts(&i.e.rs)].concat() }

/// `rfBytes I = encodeReceipts (refunds c)`.
pub fn rf_bytes(i: &Info) -> Bytes { encode_receipts(&i.e.refunds(&i.c)) }

/// `rcptMsgs I` as in `RcptSim.lean`: `RC`, `RF`, then per receipt `PEO(r)`,
/// `LEAF(r)` and (refund) `RID(r)`.
pub fn rcpt_msgs_sim(i: &Info) -> Vec<Msg> {
    let mut v = vec![
        Msg { id: msg_id(K_RC, 0) as u32, bytes: rc_bytes(i) },
        Msg { id: msg_id(K_RF, 0) as u32, bytes: rf_bytes(i) },
    ];
    for r in 0..i.n_rcpt() {
        v.push(Msg { id: msg_id(K_PEO, r) as u32, bytes: peo_bytes(i, r) });
        v.push(Msg { id: msg_id(K_LEAF, r) as u32, bytes: leaf_bytes(i, r) });
        if has_refund(i, r) {
            v.push(Msg { id: msg_id(K_RID, r) as u32, bytes: rid_bytes(i, r) });
        }
    }
    v
}

