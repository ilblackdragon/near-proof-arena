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


/// One bus message of a simulated table (`RcptSim.BusMsg`, multiplicity 1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BusMsg {
    pub bus: usize,
    pub send: bool,
    pub msg: Vec<u32>,
}

/// `rcptBus I`: traffic of `rcpt` except its `BYTES` sends.
pub fn rcpt_bus_sim(i: &Info) -> Vec<BusMsg> {
    let e = &i.e;
    let mut v: Vec<BusMsg> = rcpt_msgs_sim(i)
        .iter()
        .filter(|m| m.id as usize % 16 != K_LEAF)
        .map(|m| {
            let mut msg = vec![m.id, m.bytes.len() as u32];
            msg.extend(sha_n(&m.bytes).iter().map(|&x| x as u32));
            BusMsg { bus: B_DIGEST, send: false, msg }
        })
        .collect();
    for r in 0..i.n_rcpt() {
        let rc = e.rc(r);
        let k = e.slot(r);
        let a0 = e.acc0(k);
        let bef = le_bytes(16, e.amt_at(k, r));
        let aft = le_bytes(16, e.amt_at(k, r) + rc.deposit);
        let lk = le_bytes(16, a0.locked);
        let st = le_bytes(8, a0.storage_usage);
        let g = |b: &Bytes, j: usize| b.get(j).copied().unwrap_or(0) as u32;
        for (t, s) in key_syms(&rc).into_iter().enumerate() {
            v.push(BusMsg { bus: B_KEYNIB, send: true, msg: vec![r as u32, t as u32, s as u32, (s == SYM_END) as u32] });
        }
        v.push(BusMsg { bus: B_FINAL, send: false, msg: vec![r as u32, k as u32] });
        let tp = tprev_of(e, r) as u32;
        for j in 0..16 {
            v.push(BusMsg { bus: B_MEM, send: false, msg: vec![k as u32, tp, j as u32, g(&bef, j), g(&lk, j), g(&st, j)] });
            v.push(BusMsg { bus: B_MEM, send: true, msg: vec![k as u32, r as u32 + 1, j as u32, g(&aft, j), g(&lk, j), g(&st, j)] });
        }
        for j in 0..32 {
            v.push(BusMsg { bus: B_RIDS, send: true, msg: vec![r as u32, j as u32, g(&rc.receipt_id, j)] });
        }
        v.push(BusMsg { bus: B_MPOS, send: true, msg: vec![0, r as u32, msg_id(K_LEAF, r) as u32, 68] });
    }
    v
}

/// `bytesSends ms`.
pub fn bytes_sends(ms: &[Msg]) -> Vec<BusMsg> {
    ms.iter()
        .flat_map(|m| m.bytes.iter().enumerate().map(move |(p, &b)| BusMsg { bus: B_BYTES, send: true, msg: vec![m.id, p as u32, b as u32] }))
        .collect()
}
