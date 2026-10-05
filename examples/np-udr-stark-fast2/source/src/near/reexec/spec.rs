//! Formats and constants of `near-arena-claim-v1` (`spec/claim-v1.md`) and
//! the per-receipt domain predicates of `NearSpec` (`Primitives.lean`,
//! `AccountId.lean`).

use super::wire::{Reader, WResult, WireError, Writer};

pub const CLAIM_FORMAT: &[u8] = b"near-arena-claim-v1";
pub const REQUEST_FORMAT: &[u8] = b"near-arena-request-v1";
pub const WITNESS_FORMAT: &[u8] = b"near-arena-witness-v1";
pub const PARAMS_FORMAT: &[u8] = b"near-arena-params-v1";
pub const STATEMENT_ID: &[u8] = b"near/pv86/receipt-transfer-batch/v0";
pub const CHAIN_ID: &[u8] = b"mainnet";
pub const PROTOCOL_VERSION: u32 = 86;
/// `new_action_receipt` exec + `transfer` exec (named receiver).
pub const G: u64 = 108_059_500_000 + 115_123_062_500;
pub const STORAGE_AMOUNT_PER_BYTE: u128 = 10_000_000_000_000_000_000;
pub const ZERO_BALANCE_STORAGE_LIMIT: u64 = 770;
pub const MAX_BATCH: usize = 256;
pub const MAX_WITNESS_BYTES: u64 = 3_000_000;
pub const SYSTEM: &[u8] = b"system";

/// A single-Transfer action receipt (the only shape in the slice).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receipt<'a> {
    pub predecessor: &'a [u8],
    pub receiver: &'a [u8],
    pub receipt_id: [u8; 32],
    pub signer: &'a [u8],
    /// Borsh `PublicKey` bytes (tag ‖ data), 33 or 65 bytes.
    pub signer_pk: &'a [u8],
    pub gas_price: u128,
    pub deposit: u128,
}

/// Strict decoder of one nearcore-borsh receipt of the slice shape.
pub fn read_receipt<'a>(r: &mut Reader<'a>) -> WResult<Receipt<'a>> {
    let predecessor = r.bytes("predecessor_id")?;
    let receiver = r.bytes("receiver_id")?;
    let receipt_id = r.hash("receipt_id")?;
    if r.u8("receipt enum")? != 0 {
        return Err(WireError("out of slice: ReceiptEnum is not Action"));
    }
    let signer = r.bytes("signer_id")?;
    let pk_start = r.pos;
    let klen = match r.u8("key type")? {
        0 => 32,
        1 => 64,
        _ => return Err(WireError("out of slice: signer key type")),
    };
    r.take(klen, "public key")?;
    let signer_pk = &r.buf[pk_start..r.pos];
    let gas_price = r.u128("gas_price")?;
    if r.u32("output_data_receivers")? != 0 {
        return Err(WireError("out of slice: output data receivers"));
    }
    if r.u32("input_data_ids")? != 0 {
        return Err(WireError("out of slice: input data ids"));
    }
    if r.u32("actions")? != 1 {
        return Err(WireError("out of slice: action count"));
    }
    if r.u8("action tag")? != 3 {
        return Err(WireError("out of slice: action is not Transfer"));
    }
    let deposit = r.u128("deposit")?;
    Ok(Receipt { predecessor, receiver, receipt_id, signer, signer_pk, gas_price, deposit })
}

/// Exact nearcore borsh of a receipt (inverse of [`read_receipt`]).
pub fn write_receipt(w: &mut Writer, r: &Receipt<'_>) {
    w.bytes(r.predecessor).bytes(r.receiver).raw(&r.receipt_id).u8(0).bytes(r.signer).raw(r.signer_pk);
    w.u128(r.gas_price).u32(0).u32(0).u32(1).u8(3).u128(r.deposit);
}

/// Gas-refund receipt bytes (`Receipt::new_gas_refund`), written directly.
pub fn write_refund(w: &mut Writer, parent: &Receipt<'_>, refund_id: &[u8; 32], amount: u128) {
    w.bytes(SYSTEM).bytes(parent.signer).raw(refund_id).u8(0).bytes(parent.signer).raw(parent.signer_pk);
    w.u128(0).u32(0).u32(0).u32(1).u8(3).u128(amount);
}

pub struct Request<'a> {
    pub protocol_version: u32,
    pub chain_id: &'a [u8],
    pub shard_id: u64,
    pub block_height: u64,
    pub block_gas_price: u128,
    pub gas_limit: u64,
    pub pre_state_root: [u8; 32],
    pub receipts: Vec<Receipt<'a>>,
    /// `u32 n ‖ receipts` exactly as in `request.bin` (= `encodeReceipts`).
    pub receipts_bytes: &'a [u8],
}

pub fn chain_id_ok(b: &[u8]) -> bool {
    (1..=64).contains(&b.len()) && b.iter().all(|&x| (33..=126).contains(&x))
}

pub fn decode_request(buf: &[u8]) -> WResult<Request<'_>> {
    let mut r = Reader::new(buf);
    r.expect_tag(REQUEST_FORMAT, "request format")?;
    r.expect_tag(STATEMENT_ID, "statement id")?;
    let protocol_version = r.u32("protocol_version")?;
    let chain_id = r.bytes("chain_id")?;
    if !chain_id_ok(chain_id) {
        return Err(WireError("bad chain_id"));
    }
    let shard_id = r.u64("shard_id")?;
    let block_height = r.u64("block_height")?;
    let block_gas_price = r.u128("block_gas_price")?;
    let gas_limit = r.u64("gas_limit")?;
    let pre_state_root = r.hash("pre_state_root")?;
    let start = r.pos;
    let n = r.u32("receipt count")? as usize;
    let mut receipts = Vec::with_capacity(n.min(MAX_BATCH));
    for _ in 0..n {
        receipts.push(read_receipt(&mut r)?);
    }
    let receipts_bytes = &buf[start..r.pos];
    r.finish()?;
    Ok(Request {
        protocol_version,
        chain_id,
        shard_id,
        block_height,
        block_gas_price,
        gas_limit,
        pre_state_root,
        receipts,
        receipts_bytes,
    })
}

/// `witness.bin` → (pre_state_root, sorted PartialState values).
pub fn decode_witness(buf: &[u8]) -> WResult<([u8; 32], Vec<&[u8]>)> {
    let mut r = Reader::new(buf);
    r.expect_tag(WITNESS_FORMAT, "witness format")?;
    let root = r.hash("pre_state_root")?;
    if r.u8("PartialState tag")? != 0 {
        return Err(WireError("PartialState tag"));
    }
    let m = r.u32("value count")? as usize;
    let mut vals: Vec<&[u8]> = Vec::with_capacity(m.min(1 << 20));
    for _ in 0..m {
        let v = r.bytes("value")?;
        if let Some(prev) = vals.last() {
            if *prev >= v {
                return Err(WireError("witness values not strictly ascending"));
            }
        }
        vals.push(v);
    }
    r.finish()?;
    Ok((root, vals))
}

/// The public claim (`spec/claim-v1.md` §3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub protocol_version: u32,
    pub chain_id: Vec<u8>,
    pub shard_id: u64,
    pub block_height: u64,
    pub block_gas_price: u128,
    pub gas_limit: u64,
    pub pre_state_root: [u8; 32],
    pub receipt_count: u32,
    pub receipts_commitment: [u8; 32],
    pub slice_post_root: [u8; 32],
    pub outcome_root: [u8; 32],
    pub refund_count: u32,
    pub refunds_commitment: [u8; 32],
    pub gas_burnt_total: u64,
    pub tokens_burnt_total: u128,
}

impl Claim {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::with_capacity(320);
        w.bytes(CLAIM_FORMAT).bytes(STATEMENT_ID).u32(self.protocol_version).bytes(&self.chain_id);
        w.u64(self.shard_id).u64(self.block_height).u128(self.block_gas_price).u64(self.gas_limit);
        w.raw(&self.pre_state_root).u32(self.receipt_count).raw(&self.receipts_commitment);
        w.raw(&self.slice_post_root).raw(&self.outcome_root).u32(self.refund_count);
        w.raw(&self.refunds_commitment).u64(self.gas_burnt_total).u128(self.tokens_burnt_total);
        w.0
    }

    /// Strict decoder (`TransferV1.decodeClaim`).
    pub fn decode(buf: &[u8]) -> WResult<Claim> {
        let mut r = Reader::new(buf);
        r.expect_tag(CLAIM_FORMAT, "claim format")?;
        r.expect_tag(STATEMENT_ID, "statement id")?;
        let protocol_version = r.u32("pv")?;
        let chain_id = r.bytes("chain")?.to_vec();
        if !chain_id_ok(&chain_id) {
            return Err(WireError("bad chain_id"));
        }
        let c = Claim {
            protocol_version,
            chain_id,
            shard_id: r.u64("shard")?,
            block_height: r.u64("height")?,
            block_gas_price: r.u128("gas price")?,
            gas_limit: r.u64("gas limit")?,
            pre_state_root: r.hash("pre root")?,
            receipt_count: r.u32("n")?,
            receipts_commitment: r.hash("rc")?,
            slice_post_root: r.hash("post")?,
            outcome_root: r.hash("outcome")?,
            refund_count: r.u32("nr")?,
            refunds_commitment: r.hash("rfc")?,
            gas_burnt_total: r.u64("gas")?,
            tokens_burnt_total: r.u128("tokens")?,
        };
        r.finish()?;
        Ok(c)
    }
}

// ---- account ids (near-account-id 2.0.0) -------------------------------

#[inline]
fn is_alnum(c: u8) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_digit()
}
#[inline]
fn is_sep(c: u8) -> bool {
    c == b'-' || c == b'_' || c == b'.'
}
#[inline]
fn is_hex(c: u8) -> bool {
    (b'a'..=b'f').contains(&c) || c.is_ascii_digit()
}

pub fn account_id_valid(s: &[u8]) -> bool {
    if !(2..=64).contains(&s.len()) {
        return false;
    }
    let mut last_sep = true;
    for &c in s {
        if is_alnum(c) {
            last_sep = false;
        } else if is_sep(c) {
            if last_sep {
                return false;
            }
            last_sep = true;
        } else {
            return false;
        }
    }
    !last_sep
}

pub fn is_named(s: &[u8]) -> bool {
    let all_hex = |b: &[u8]| b.iter().all(|&c| is_hex(c));
    let eth = s.len() == 42 && &s[..2] == b"0x" && all_hex(&s[2..]);
    let near = s.len() == 64 && all_hex(s);
    let det = s.len() == 42 && &s[..2] == b"0s" && all_hex(&s[2..]);
    !(eth || near || det)
}

/// `Receipt.inSlice` (the parser already enforces the key shape and widths).
pub fn receipt_in_slice(r: &Receipt<'_>) -> bool {
    account_id_valid(r.predecessor)
        && account_id_valid(r.receiver)
        && account_id_valid(r.signer)
        && r.predecessor != SYSTEM
        && is_named(r.receiver)
}
