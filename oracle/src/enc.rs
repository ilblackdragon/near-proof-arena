//! Canonical byte encodings of `spec/claim-v1.md` (request.bin, witness.bin,
//! claim.bin, state.bin). Writer + strict reader. Receipts inside request.bin
//! are nearcore's own borsh (`Receipt`), produced by nearcore's serializer.

use near_primitives::hash::CryptoHash;
use near_primitives::receipt::Receipt;

pub const REQUEST_FORMAT: &str = "near-arena-request-v1";
pub const WITNESS_FORMAT: &str = "near-arena-witness-v1";
pub const CLAIM_FORMAT: &str = "near-arena-claim-v1";
pub const STATE_FORMAT: &str = "near-arena-state-v1";
pub const STATEMENT_ID: &str = "near/pv86/receipt-transfer-batch/v0";

pub const MAX_CHAIN_ID_LEN: usize = 64;

#[derive(Default)]
pub struct W(pub Vec<u8>);
impl W {
    pub fn u8(&mut self, x: u8) -> &mut Self {
        self.0.push(x);
        self
    }
    pub fn u32(&mut self, x: u32) -> &mut Self {
        self.0.extend_from_slice(&x.to_le_bytes());
        self
    }
    pub fn u64(&mut self, x: u64) -> &mut Self {
        self.0.extend_from_slice(&x.to_le_bytes());
        self
    }
    pub fn u128(&mut self, x: u128) -> &mut Self {
        self.0.extend_from_slice(&x.to_le_bytes());
        self
    }
    pub fn raw(&mut self, b: &[u8]) -> &mut Self {
        self.0.extend_from_slice(b);
        self
    }
    pub fn bytes(&mut self, b: &[u8]) -> &mut Self {
        self.u32(b.len().try_into().unwrap());
        self.raw(b)
    }
    pub fn str(&mut self, s: &str) -> &mut Self {
        self.bytes(s.as_bytes())
    }
}

pub struct R<'a> {
    b: &'a [u8],
}
impl<'a> R<'a> {
    pub fn new(b: &'a [u8]) -> Self {
        R { b }
    }
    pub fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        if self.b.len() < n {
            return Err(format!("truncated: need {n} have {}", self.b.len()));
        }
        let (h, t) = self.b.split_at(n);
        self.b = t;
        Ok(h)
    }
    pub fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }
    pub fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    pub fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    pub fn u128(&mut self) -> Result<u128, String> {
        Ok(u128::from_le_bytes(self.take(16)?.try_into().unwrap()))
    }
    pub fn h32(&mut self) -> Result<[u8; 32], String> {
        Ok(self.take(32)?.try_into().unwrap())
    }
    pub fn bytes(&mut self) -> Result<&'a [u8], String> {
        let n = self.u32()? as usize;
        self.take(n)
    }
    pub fn expect_str(&mut self, s: &str) -> Result<(), String> {
        let got = self.bytes()?;
        if got != s.as_bytes() {
            return Err(format!("expected tag {s:?}, got {:?}", String::from_utf8_lossy(got)));
        }
        Ok(())
    }
    pub fn rest(&self) -> &'a [u8] {
        self.b
    }
    pub fn end(&self) -> Result<(), String> {
        if !self.b.is_empty() {
            return Err(format!("{} trailing bytes", self.b.len()));
        }
        Ok(())
    }
}

pub fn chain_id_ok(s: &[u8]) -> bool {
    !s.is_empty() && s.len() <= MAX_CHAIN_ID_LEN && s.iter().all(|&c| (0x21..=0x7e).contains(&c))
}

#[derive(Clone, Debug)]
pub struct Request {
    pub protocol_version: u32,
    pub chain_id: String,
    pub shard_id: u64,
    pub block_height: u64,
    pub block_gas_price: u128,
    pub gas_limit: u64,
    pub pre_state_root: CryptoHash,
    pub receipts: Vec<Receipt>,
}

impl Request {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = W::default();
        w.str(REQUEST_FORMAT)
            .str(STATEMENT_ID)
            .u32(self.protocol_version)
            .str(&self.chain_id)
            .u64(self.shard_id)
            .u64(self.block_height)
            .u128(self.block_gas_price)
            .u64(self.gas_limit)
            .raw(self.pre_state_root.as_ref())
            .u32(self.receipts.len().try_into().unwrap());
        for r in &self.receipts {
            w.raw(&borsh::to_vec(r).unwrap());
        }
        w.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub protocol_version: u32,
    pub chain_id: String,
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
    pub refund_receipts_commitment: [u8; 32],
    pub gas_burnt_total: u64,
    pub tokens_burnt_total: u128,
}

impl Claim {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = W::default();
        w.str(CLAIM_FORMAT)
            .str(STATEMENT_ID)
            .u32(self.protocol_version)
            .str(&self.chain_id)
            .u64(self.shard_id)
            .u64(self.block_height)
            .u128(self.block_gas_price)
            .u64(self.gas_limit)
            .raw(&self.pre_state_root)
            .u32(self.receipt_count)
            .raw(&self.receipts_commitment)
            .raw(&self.slice_post_root)
            .raw(&self.outcome_root)
            .u32(self.refund_count)
            .raw(&self.refund_receipts_commitment)
            .u64(self.gas_burnt_total)
            .u128(self.tokens_burnt_total);
        w.0
    }

    pub fn decode(b: &[u8]) -> Result<Claim, String> {
        let mut r = R::new(b);
        r.expect_str(CLAIM_FORMAT)?;
        r.expect_str(STATEMENT_ID)?;
        let protocol_version = r.u32()?;
        let chain = r.bytes()?;
        if !chain_id_ok(chain) {
            return Err("bad chain id".into());
        }
        let c = Claim {
            protocol_version,
            chain_id: String::from_utf8(chain.to_vec()).unwrap(),
            shard_id: r.u64()?,
            block_height: r.u64()?,
            block_gas_price: r.u128()?,
            gas_limit: r.u64()?,
            pre_state_root: r.h32()?,
            receipt_count: r.u32()?,
            receipts_commitment: r.h32()?,
            slice_post_root: r.h32()?,
            outcome_root: r.h32()?,
            refund_count: r.u32()?,
            refund_receipts_commitment: r.h32()?,
            gas_burnt_total: r.u64()?,
            tokens_burnt_total: r.u128()?,
        };
        r.end()?;
        Ok(c)
    }

    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "protocol_version": self.protocol_version,
            "chain_id": self.chain_id,
            "shard_id": self.shard_id,
            "block_height": self.block_height,
            "block_gas_price": self.block_gas_price.to_string(),
            "gas_limit": self.gas_limit,
            "pre_state_root": hex::encode(self.pre_state_root),
            "receipt_count": self.receipt_count,
            "receipts_commitment": hex::encode(self.receipts_commitment),
            "slice_post_root": hex::encode(self.slice_post_root),
            "outcome_root": hex::encode(self.outcome_root),
            "refund_count": self.refund_count,
            "refund_receipts_commitment": hex::encode(self.refund_receipts_commitment),
            "gas_burnt_total": self.gas_burnt_total,
            "tokens_burnt_total": self.tokens_burnt_total.to_string(),
        })
    }
}

/// witness.bin: format tag, pre-state root, then nearcore's own
/// `borsh(PartialState::TrieValues(values))` with values strictly ascending.
pub fn encode_witness(pre_root: &CryptoHash, values: &[Vec<u8>]) -> Vec<u8> {
    let mut sorted = values.to_vec();
    sorted.sort();
    sorted.dedup();
    let mut w = W::default();
    w.str(WITNESS_FORMAT).raw(pre_root.as_ref()).u8(0).u32(sorted.len().try_into().unwrap());
    for v in &sorted {
        w.bytes(v);
    }
    w.0
}

/// state.bin (judge-only): the full synthetic pre-state as raw trie key/values.
pub fn encode_state(kv: &[(Vec<u8>, Vec<u8>)]) -> Vec<u8> {
    let mut w = W::default();
    w.str(STATE_FORMAT).u32(kv.len().try_into().unwrap());
    for (k, v) in kv {
        w.bytes(k).bytes(v);
    }
    w.0
}

pub fn decode_state(b: &[u8]) -> Result<Vec<(Vec<u8>, Vec<u8>)>, String> {
    let mut r = R::new(b);
    r.expect_str(STATE_FORMAT)?;
    let n = r.u32()?;
    let mut out: Vec<(Vec<u8>, Vec<u8>)> = vec![];
    for _ in 0..n {
        let k = r.bytes()?.to_vec();
        let v = r.bytes()?.to_vec();
        if let Some((pk, _)) = out.last() {
            if *pk >= k {
                return Err("state keys not strictly ascending".into());
            }
        }
        out.push((k, v));
    }
    r.end()?;
    Ok(out)
}

pub fn decode_request(b: &[u8]) -> Result<Request, String> {
    use borsh::BorshDeserialize;
    let mut r = R::new(b);
    r.expect_str(REQUEST_FORMAT)?;
    r.expect_str(STATEMENT_ID)?;
    let protocol_version = r.u32()?;
    let chain = r.bytes()?;
    if !chain_id_ok(chain) {
        return Err("bad chain id".into());
    }
    let shard_id = r.u64()?;
    let block_height = r.u64()?;
    let block_gas_price = r.u128()?;
    let gas_limit = r.u64()?;
    let pre_state_root = CryptoHash(r.h32()?);
    let n = r.u32()?;
    let mut rest = r.rest();
    let mut receipts = vec![];
    for _ in 0..n {
        let rc = Receipt::deserialize(&mut rest).map_err(|e| format!("receipt: {e}"))?;
        receipts.push(rc);
    }
    if !rest.is_empty() {
        return Err("trailing bytes after receipts".into());
    }
    Ok(Request {
        protocol_version,
        chain_id: String::from_utf8(chain.to_vec()).unwrap(),
        shard_id,
        block_height,
        block_gas_price,
        gas_limit,
        pre_state_root,
        receipts,
    })
}
