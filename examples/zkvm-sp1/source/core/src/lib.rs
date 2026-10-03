//! `transfer-core`: the relation check for `near/pv86/receipt-transfer-batch/v0`
//! as one deterministic function `derive_claim(request.bin, witness.bin) -> claim.bin`.
//!
//! This is the code that runs INSIDE the SP1 zkVM guest (and, unchanged, natively
//! in the host as a fail-fast pre-check). It is written from `spec/claim-v1.md`
//! and `spec/near-transfer-receipt-v1.md` only. In the guest, `sha2` is patched
//! to SP1's SHA-256 precompile; natively it is the RustCrypto implementation.
//!
//! Soundness-relevant structure (what a proof of this program attests):
//! * request.bin and witness.bin are decoded strictly (tags, widths, no trailing
//!   bytes);
//! * every receiver's `TrieKey::Account` value is resolved by walking trie nodes
//!   whose SHA-256 chains to `request.pre_state_root` (nodes are looked up BY
//!   HASH, so an unrevealed or forged node cannot be used);
//! * the slice domain (spec §3) is checked; any violation aborts (no claim);
//! * transfers, outcomes, refunds and burns are applied per spec §2 and the
//!   post root is recomputed by in-place value replacement along the revealed
//!   paths (spec §4: shape and memory_usage unchanged in the domain);
//! * the claim bytes are produced by the canonical encoder (spec claim-v1 §3).
#![no_std]
extern crate alloc;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use sha2::{Digest, Sha256};

pub const REQUEST_FORMAT: &[u8] = b"near-arena-request-v1";
pub const WITNESS_FORMAT: &[u8] = b"near-arena-witness-v1";
pub const CLAIM_FORMAT: &[u8] = b"near-arena-claim-v1";
pub const PARAMS_FORMAT: &[u8] = b"near-arena-params-v1";
pub const STATEMENT_ID: &[u8] = b"near/pv86/receipt-transfer-batch/v0";

pub const PROTOCOL_VERSION: u32 = 86;
pub const CHAIN_ID: &[u8] = b"mainnet";
/// exec(new_action_receipt) + exec(transfer, named receiver), PV86 mainnet params.
pub const G: u128 = 108_059_500_000 + 115_123_062_500;
pub const MAX_BATCH: usize = 256;
pub const MAX_WITNESS_BYTES: usize = 3_000_000;
pub const STORAGE_AMOUNT_PER_BYTE: u128 = 10_000_000_000_000_000_000;
pub const ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT: u64 = 770;
pub const MAX_CLAIM_BYTES: usize = 302 + 64;
/// `runtime_config_digest` of the challenge (spec/challenge-inputs/near-transfer-receipt-v1.json).
pub const RUNTIME_CONFIG_DIGEST: [u8; 32] =
    hex32(b"ae2d1af88031a30bb09d17fd0d514503de26ed83d642ff497618e9f3320eebf1");

const fn hex32(s: &[u8; 64]) -> [u8; 32] {
    const fn nib(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            _ => panic!("bad hex"),
        }
    }
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = nib(s[2 * i]) << 4 | nib(s[2 * i + 1]);
        i += 1;
    }
    out
}

/// Why no claim was produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The bytes are not a well-formed request/witness encoding.
    Malformed(&'static str),
    /// Well-formed, but outside the slice domain (spec §3) or the witness does
    /// not open the receivers' paths.
    OutOfDomain(&'static str),
}

impl Error {
    pub fn reason(&self) -> &'static str {
        match self {
            Error::Malformed(s) | Error::OutOfDomain(s) => s,
        }
    }
}

type Res<T> = Result<T, Error>;
type H = [u8; 32];

pub fn sha256(b: &[u8]) -> H {
    Sha256::digest(b).into()
}

fn sha256_2(a: &[u8], b: &[u8]) -> H {
    let mut h = Sha256::new();
    h.update(a);
    h.update(b);
    h.finalize().into()
}

// ---------------------------------------------------------------- reader

struct R<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> R<'a> {
    fn new(b: &'a [u8]) -> Self {
        R { b, i: 0 }
    }
    fn take(&mut self, n: usize) -> Res<&'a [u8]> {
        let end = self.i.checked_add(n).ok_or(Error::Malformed("length overflow"))?;
        if end > self.b.len() {
            return Err(Error::Malformed("truncated"));
        }
        let r = &self.b[self.i..end];
        self.i = end;
        Ok(r)
    }
    fn u8(&mut self) -> Res<u8> {
        Ok(self.take(1)?[0])
    }
    fn u16(&mut self) -> Res<u16> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u32(&mut self) -> Res<u32> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Res<u64> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn u128(&mut self) -> Res<u128> {
        Ok(u128::from_le_bytes(self.take(16)?.try_into().unwrap()))
    }
    fn h32(&mut self) -> Res<H> {
        Ok(self.take(32)?.try_into().unwrap())
    }
    fn bytes(&mut self) -> Res<&'a [u8]> {
        let n = self.u32()? as usize;
        self.take(n)
    }
    fn tag(&mut self, want: &[u8]) -> Res<()> {
        if self.bytes()? != want {
            return Err(Error::Malformed("bad format tag / statement id"));
        }
        Ok(())
    }
    fn end(&self) -> Res<()> {
        if self.i != self.b.len() {
            return Err(Error::Malformed("trailing bytes"));
        }
        Ok(())
    }
}

// ---------------------------------------------------------------- writer

#[derive(Default)]
struct W(Vec<u8>);
impl W {
    fn raw(&mut self, b: &[u8]) -> &mut Self {
        self.0.extend_from_slice(b);
        self
    }
    fn u8(&mut self, x: u8) -> &mut Self {
        self.0.push(x);
        self
    }
    fn u32(&mut self, x: u32) -> &mut Self {
        self.raw(&x.to_le_bytes())
    }
    fn u64(&mut self, x: u64) -> &mut Self {
        self.raw(&x.to_le_bytes())
    }
    fn u128(&mut self, x: u128) -> &mut Self {
        self.raw(&x.to_le_bytes())
    }
    fn bytes(&mut self, b: &[u8]) -> &mut Self {
        self.u32(b.len() as u32).raw(b)
    }
}

// ---------------------------------------------------------------- request

pub struct Receipt<'a> {
    pub predecessor: &'a [u8],
    pub receiver: &'a [u8],
    pub receipt_id: H,
    pub signer: &'a [u8],
    /// borsh PublicKey: tag byte ‖ 32 (ED25519) or 64 (SECP256K1) bytes.
    pub signer_key: &'a [u8],
    pub gas_price: u128,
    pub deposit: u128,
}

pub struct Request<'a> {
    pub protocol_version: u32,
    pub chain_id: &'a [u8],
    pub shard_id: u64,
    pub block_height: u64,
    pub block_gas_price: u128,
    pub gas_limit: u64,
    pub pre_state_root: H,
    /// Exact borsh bytes of `Vec<Receipt>` (u32 n ‖ receipts), as in request.bin.
    pub receipts_vec_bytes: &'a [u8],
    pub receipts: Vec<Receipt<'a>>,
}

fn chain_id_ok(c: &[u8]) -> bool {
    !c.is_empty() && c.len() <= 64 && c.iter().all(|&x| (0x21..=0x7e).contains(&x))
}

fn parse_receipt<'a>(r: &mut R<'a>) -> Res<Receipt<'a>> {
    let predecessor = r.bytes()?;
    let receiver = r.bytes()?;
    let receipt_id = r.h32()?;
    if r.u8()? != 0 {
        return Err(Error::OutOfDomain("ReceiptEnum is not Action"));
    }
    let signer = r.bytes()?;
    let kstart = r.i;
    let klen = match r.u8()? {
        0 => 32,
        1 => 64,
        _ => return Err(Error::OutOfDomain("signer key type not ED25519/SECP256K1")),
    };
    r.take(klen)?;
    let signer_key = &r.b[kstart..r.i];
    let gas_price = r.u128()?;
    if r.u32()? != 0 {
        return Err(Error::OutOfDomain("output_data_receivers not empty"));
    }
    if r.u32()? != 0 {
        return Err(Error::OutOfDomain("input_data_ids not empty"));
    }
    if r.u32()? != 1 {
        return Err(Error::OutOfDomain("not exactly one action"));
    }
    if r.u8()? != 3 {
        return Err(Error::OutOfDomain("action is not Transfer"));
    }
    let deposit = r.u128()?;
    Ok(Receipt { predecessor, receiver, receipt_id, signer, signer_key, gas_price, deposit })
}

pub fn parse_request(b: &[u8]) -> Res<Request<'_>> {
    let mut r = R::new(b);
    r.tag(REQUEST_FORMAT)?;
    r.tag(STATEMENT_ID)?;
    let protocol_version = r.u32()?;
    let chain_id = r.bytes()?;
    if !chain_id_ok(chain_id) {
        return Err(Error::Malformed("chain id"));
    }
    let shard_id = r.u64()?;
    let block_height = r.u64()?;
    let block_gas_price = r.u128()?;
    let gas_limit = r.u64()?;
    let pre_state_root = r.h32()?;
    let vstart = r.i;
    let n = r.u32()? as usize;
    // Bound before allocating: the domain caps n at 256; a larger count is
    // out of domain whatever follows.
    if n == 0 || n > MAX_BATCH {
        return Err(Error::OutOfDomain("batch size not in 1..=256"));
    }
    let mut receipts = Vec::with_capacity(n);
    for _ in 0..n {
        receipts.push(parse_receipt(&mut r)?);
    }
    r.end()?;
    Ok(Request {
        protocol_version,
        chain_id,
        shard_id,
        block_height,
        block_gas_price,
        gas_limit,
        pre_state_root,
        receipts_vec_bytes: &b[vstart..],
        receipts,
    })
}

// ---------------------------------------------------------------- account ids

/// near-account-id 2.0 validity.
pub fn valid_account_id(s: &[u8]) -> bool {
    if !(2..=64).contains(&s.len()) {
        return false;
    }
    let mut last_sep = true;
    for &c in s {
        let sep = match c {
            b'a'..=b'z' | b'0'..=b'9' => false,
            b'-' | b'_' | b'.' => true,
            _ => return false,
        };
        if sep && last_sep {
            return false;
        }
        last_sep = sep;
    }
    !last_sep
}

fn is_lower_hex(s: &[u8]) -> bool {
    s.iter().all(|c| matches!(c, b'0'..=b'9' | b'a'..=b'f'))
}

/// `AccountType::NamedAccount` (not NEAR-implicit, ETH-implicit, or deterministic).
pub fn is_named(s: &[u8]) -> bool {
    if s.len() == 64 && is_lower_hex(s) {
        return false;
    }
    if s.len() == 42 && (s.starts_with(b"0x") || s.starts_with(b"0s")) && is_lower_hex(&s[2..]) {
        return false;
    }
    true
}

// ---------------------------------------------------------------- trie

/// Witness: trie nodes / values addressed by sha256(entry).
pub struct Witness<'a> {
    pub nodes: BTreeMap<H, &'a [u8]>,
    pub total_bytes: usize,
}

pub fn parse_witness<'a>(b: &'a [u8], pre_state_root: &H) -> Res<Witness<'a>> {
    let mut r = R::new(b);
    r.tag(WITNESS_FORMAT)?;
    if &r.h32()? != pre_state_root {
        return Err(Error::Malformed("witness pre_state_root != request pre_state_root"));
    }
    if r.u8()? != 0 {
        return Err(Error::Malformed("PartialState tag"));
    }
    let m = r.u32()? as usize;
    let mut nodes = BTreeMap::new();
    let mut total = 0usize;
    let mut prev: Option<&[u8]> = None;
    for _ in 0..m {
        let v = r.bytes()?;
        if let Some(p) = prev {
            if p >= v {
                return Err(Error::Malformed("witness values not strictly ascending"));
            }
        }
        prev = Some(v);
        total += v.len();
        nodes.insert(sha256(v), v);
    }
    r.end()?;
    Ok(Witness { nodes, total_bytes: total })
}

fn nibbles(key: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(key.len() * 2);
    for &b in key {
        out.push(b >> 4);
        out.push(b & 15);
    }
    out
}

/// Strict hex-prefix decoding (nearcore `NibbleSlice::from_encoded`).
fn decode_hp(e: &[u8], want_leaf: bool) -> Res<Vec<u8>> {
    let Some(&first) = e.first() else { return Err(Error::Malformed("empty node key")) };
    if first & 0xc0 != 0 || ((first & 0x20) != 0) != want_leaf {
        return Err(Error::Malformed("node key flags"));
    }
    let mut out = Vec::with_capacity(e.len() * 2);
    if first & 0x10 != 0 {
        out.push(first & 0x0f);
    } else if first & 0x0f != 0 {
        return Err(Error::Malformed("non-canonical even key prefix"));
    }
    for &b in &e[1..] {
        out.push(b >> 4);
        out.push(b & 15);
    }
    Ok(out)
}

/// Parsed `RawTrieNodeWithSize`, with byte offsets of the hash fields so that
/// a node can be re-serialized by patching (all other bytes are kept).
enum Node {
    /// key nibbles, offset of ValueRef (u32 len ‖ hash)
    Leaf { key: Vec<u8>, vref_at: usize, vlen: u32, vhash: H },
    /// optional (offset, len, hash) of the value; child slots (offset, hash)
    Branch { value: Option<(usize, u32, H)>, children: [Option<(usize, H)>; 16] },
    Extension { key: Vec<u8>, child_at: usize, child: H },
}

fn parse_node(n: &[u8]) -> Res<Node> {
    if n.len() < 9 {
        return Err(Error::Malformed("trie node too short"));
    }
    let body = &n[..n.len() - 8];
    let mut r = R::new(body);
    let node = match r.u8()? {
        0 => {
            let key = decode_hp(r.bytes()?, true)?;
            let vref_at = r.i;
            let vlen = r.u32()?;
            let vhash = r.h32()?;
            Node::Leaf { key, vref_at, vlen, vhash }
        }
        t @ (1 | 2) => {
            let value = if t == 2 {
                let at = r.i;
                let l = r.u32()?;
                Some((at, l, r.h32()?))
            } else {
                None
            };
            let bitmap = r.u16()?;
            let mut children = [None; 16];
            for (i, c) in children.iter_mut().enumerate() {
                if bitmap >> i & 1 == 1 {
                    let at = r.i;
                    *c = Some((at, r.h32()?));
                }
            }
            Node::Branch { value, children }
        }
        3 => {
            let key = decode_hp(r.bytes()?, false)?;
            let child_at = r.i;
            Node::Extension { key, child_at, child: r.h32()? }
        }
        _ => return Err(Error::Malformed("unknown trie node tag")),
    };
    r.end()?;
    Ok(node)
}

impl<'a> Witness<'a> {
    fn get(&self, h: &H) -> Res<&'a [u8]> {
        self.nodes.get(h).copied().ok_or(Error::OutOfDomain("witness missing node on receiver path"))
    }

    /// Resolve `key` from root `root`; `Ok(None)` if the key is provably absent.
    fn lookup(&self, root: &H, key: &[u8]) -> Res<Option<&'a [u8]>> {
        let nib = nibbles(key);
        let mut rest: &[u8] = &nib;
        let mut h = *root;
        let (vlen, vhash) = loop {
            match parse_node(self.get(&h)?)? {
                Node::Leaf { key, vlen, vhash, .. } => {
                    if key.as_slice() != rest {
                        return Ok(None);
                    }
                    break (vlen, vhash);
                }
                Node::Extension { key, child, .. } => {
                    if !rest.starts_with(&key) {
                        return Ok(None);
                    }
                    rest = &rest[key.len()..];
                    h = child;
                }
                Node::Branch { value, children } => {
                    if rest.is_empty() {
                        match value {
                            Some((_, l, vh)) => break (l, vh),
                            None => return Ok(None),
                        }
                    }
                    match children[rest[0] as usize] {
                        Some((_, ch)) => {
                            h = ch;
                            rest = &rest[1..];
                        }
                        None => return Ok(None),
                    }
                }
            }
        };
        let v = self.get(&vhash).map_err(|_| Error::OutOfDomain("witness missing value"))?;
        if v.len() as u64 != vlen as u64 {
            return Err(Error::Malformed("value length != ValueRef length"));
        }
        Ok(Some(v))
    }

    /// New hash of the subtree at `h` after replacing the values of `upd`
    /// (nibble paths relative to this node, sorted, each resolved before).
    /// Value lengths are unchanged (72 bytes), so every memory_usage and the
    /// trie shape are unchanged (spec §4): only hash fields are patched.
    fn rehash(&self, h: &H, upd: &[(&[u8], &H, u32)]) -> Res<H> {
        if upd.is_empty() {
            return Ok(*h);
        }
        let raw = self.get(h)?;
        let mut out = raw.to_vec();
        let put = |out: &mut Vec<u8>, at: usize, len: Option<u32>, hash: &H| {
            let mut at = at;
            if let Some(l) = len {
                out[at..at + 4].copy_from_slice(&l.to_le_bytes());
                at += 4;
            }
            out[at..at + 32].copy_from_slice(hash);
        };
        match parse_node(raw)? {
            Node::Leaf { key, vref_at, vlen, .. } => {
                if upd.len() != 1 || upd[0].0 != key.as_slice() || upd[0].2 != vlen {
                    return Err(Error::Malformed("rehash: leaf mismatch"));
                }
                put(&mut out, vref_at, Some(upd[0].2), upd[0].1);
            }
            Node::Extension { key, child_at, child } => {
                let mut sub = Vec::with_capacity(upd.len());
                for (p, vh, l) in upd {
                    if !p.starts_with(&key) {
                        return Err(Error::Malformed("rehash: extension mismatch"));
                    }
                    sub.push((&p[key.len()..], *vh, *l));
                }
                let nh = self.rehash(&child, &sub)?;
                put(&mut out, child_at, None, &nh);
            }
            Node::Branch { value, children } => {
                let mut i = 0;
                if upd[0].0.is_empty() {
                    let Some((at, l, _)) = value else {
                        return Err(Error::Malformed("rehash: branch has no value"));
                    };
                    if l != upd[0].2 {
                        return Err(Error::Malformed("rehash: value length changed"));
                    }
                    put(&mut out, at, Some(l), upd[0].1);
                    i = 1;
                }
                while i < upd.len() {
                    let c = upd[i].0[0];
                    let mut j = i;
                    let mut sub = Vec::new();
                    while j < upd.len() && upd[j].0[0] == c {
                        sub.push((&upd[j].0[1..], upd[j].1, upd[j].2));
                        j += 1;
                    }
                    let Some((at, ch)) = children[c as usize] else {
                        return Err(Error::Malformed("rehash: missing child"));
                    };
                    let nh = self.rehash(&ch, &sub)?;
                    put(&mut out, at, None, &nh);
                    i = j;
                }
            }
        }
        Ok(sha256(&out))
    }
}

// ---------------------------------------------------------------- semantics

fn enc_receipt(
    w: &mut W,
    pred: &[u8],
    recv: &[u8],
    rid: &H,
    signer: &[u8],
    key: &[u8],
    gas_price: u128,
    deposit: u128,
) {
    w.bytes(pred).bytes(recv).raw(rid).u8(0).bytes(signer).raw(key).u128(gas_price);
    w.u32(0).u32(0).u32(1).u8(3).u128(deposit);
}

fn merklize(mut level: Vec<H>) -> H {
    if level.is_empty() {
        return [0u8; 32];
    }
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        for pair in level.chunks(2) {
            next.push(if pair.len() == 2 { sha256_2(&pair[0], &pair[1]) } else { pair[0] });
        }
        level = next;
    }
    level[0]
}

/// Summary statistics of a successful run (for host diagnostics only).
#[derive(Debug, Clone, Copy, Default)]
pub struct Stats {
    pub receipts: usize,
    pub refunds: usize,
    pub witness_entries: usize,
    pub witness_bytes: usize,
    pub distinct_receivers: usize,
}

/// The relation check. Returns the canonical claim.bin bytes, or the reason
/// the inputs do not yield a claim.
pub fn derive_claim(request: &[u8], witness: &[u8]) -> Res<(Vec<u8>, Stats)> {
    let req = parse_request(request)?;
    // ---- static domain (spec §3, S rows)
    if req.protocol_version != PROTOCOL_VERSION {
        return Err(Error::OutOfDomain("protocol_version != 86"));
    }
    if req.chain_id != CHAIN_ID {
        return Err(Error::OutOfDomain("chain_id != mainnet"));
    }
    let n = req.receipts.len();
    if (n as u128 - 1) * G >= req.gas_limit as u128 {
        return Err(Error::OutOfDomain("compute limit: (n-1)*G >= gas_limit"));
    }
    let mut ids = BTreeSet::new();
    for r in &req.receipts {
        if !(valid_account_id(r.predecessor) && valid_account_id(r.receiver) && valid_account_id(r.signer)) {
            return Err(Error::OutOfDomain("invalid account id"));
        }
        if r.predecessor == b"system" {
            return Err(Error::OutOfDomain("system predecessor"));
        }
        if !is_named(r.receiver) {
            return Err(Error::OutOfDomain("receiver is not a NamedAccount"));
        }
        if !ids.insert(r.receipt_id) {
            return Err(Error::OutOfDomain("duplicate receipt id"));
        }
    }
    let wit = parse_witness(witness, &req.pre_state_root)?;
    if wit.total_bytes > MAX_WITNESS_BYTES {
        return Err(Error::OutOfDomain("witness too large"));
    }

    // ---- sequential execution (spec §2, D rows)
    // current value of every touched account key (key = 0x00 ‖ account_id)
    let mut state: BTreeMap<Vec<u8>, [u8; 72]> = BTreeMap::new();
    let mut leaves: Vec<H> = Vec::with_capacity(n);
    let mut refunds = W::default();
    let mut refund_count: u32 = 0;
    let mut tokens: u128 = 0;
    for r in &req.receipts {
        let mut key = Vec::with_capacity(1 + r.receiver.len());
        key.push(0u8);
        key.extend_from_slice(r.receiver);
        let cur = match state.get(&key) {
            Some(v) => *v,
            None => {
                let v = wit
                    .lookup(&req.pre_state_root, &key)?
                    .ok_or(Error::OutOfDomain("receiver account does not exist"))?;
                let v: [u8; 72] =
                    v.try_into().map_err(|_| Error::OutOfDomain("receiver value is not AccountV1 (72 bytes)"))?;
                v
            }
        };
        let amount = u128::from_le_bytes(cur[0..16].try_into().unwrap());
        let locked = u128::from_le_bytes(cur[16..32].try_into().unwrap());
        let storage_usage = u64::from_le_bytes(cur[64..72].try_into().unwrap());
        if amount == u128::MAX {
            return Err(Error::OutOfDomain("receiver uses the AccountV2 sentinel"));
        }
        let new_amount = amount.checked_add(r.deposit).ok_or(Error::OutOfDomain("balance overflow"))?;
        if new_amount == u128::MAX {
            return Err(Error::OutOfDomain("new balance equals the V2 sentinel"));
        }
        let avail = new_amount.checked_add(locked).ok_or(Error::OutOfDomain("amount+locked overflow"))?;
        if !(avail >= STORAGE_AMOUNT_PER_BYTE * storage_usage as u128
            || storage_usage <= ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT)
        {
            return Err(Error::OutOfDomain("storage stake not covered"));
        }
        let p = r.gas_price.min(req.block_gas_price);
        let burnt = p.checked_mul(G).ok_or(Error::OutOfDomain("tokens_burnt overflow"))?;
        let surplus = (r.gas_price - p).checked_mul(G).ok_or(Error::OutOfDomain("refund overflow"))?;
        tokens = tokens.checked_add(burnt).ok_or(Error::OutOfDomain("tokens_burnt_total overflow"))?;
        let mut nv = cur;
        nv[0..16].copy_from_slice(&new_amount.to_le_bytes());
        state.insert(key, nv);

        // outcome
        let mut partial = W::default();
        if surplus > 0 {
            let mut idb = W::default();
            idb.raw(&r.receipt_id).u64(req.block_height).u64(0);
            let refund_id = sha256(&idb.0);
            enc_receipt(&mut refunds, b"system", r.signer, &refund_id, r.signer, r.signer_key, 0, surplus);
            refund_count += 1;
            partial.u32(1).raw(&refund_id);
        } else {
            partial.u32(0);
        }
        partial.u64(G as u64).u128(burnt).bytes(r.receiver).u8(2).u32(0);
        let mut leaf = W::default();
        leaf.u32(2).raw(&r.receipt_id).raw(&sha256(&partial.0));
        leaves.push(sha256(&leaf.0));
    }

    // ---- post root by value replacement along revealed paths
    let upd_owned: Vec<(Vec<u8>, H)> = state.iter().map(|(k, v)| (nibbles(k), sha256(v))).collect();
    let mut upd: Vec<(&[u8], &H, u32)> = upd_owned.iter().map(|(p, h)| (p.as_slice(), h, 72u32)).collect();
    upd.sort_by(|a, b| a.0.cmp(b.0));
    let post = wit.rehash(&req.pre_state_root, &upd)?;

    // ---- claim
    let mut rc = W::default();
    rc.u64(req.shard_id).raw(req.receipts_vec_bytes);
    let mut rf = W::default();
    rf.u32(refund_count).raw(&refunds.0);
    let mut c = W::default();
    c.bytes(CLAIM_FORMAT).bytes(STATEMENT_ID).u32(req.protocol_version).bytes(req.chain_id);
    c.u64(req.shard_id).u64(req.block_height).u128(req.block_gas_price).u64(req.gas_limit);
    c.raw(&req.pre_state_root).u32(n as u32).raw(&sha256(&rc.0)).raw(&post).raw(&merklize(leaves));
    c.u32(refund_count).raw(&sha256(&rf.0)).u64((G * n as u128) as u64).u128(tokens);
    let stats = Stats {
        receipts: n,
        refunds: refund_count as usize,
        witness_entries: wit.nodes.len(),
        witness_bytes: wit.total_bytes,
        distinct_receivers: state.len(),
    };
    Ok((c.0, stats))
}

/// Structural check of claim bytes (tags, widths, no trailing bytes). Used by
/// the verifier as a cheap pre-filter; soundness does not depend on it (the
/// proof binds the exact bytes).
pub fn claim_well_formed(b: &[u8]) -> bool {
    if b.len() > MAX_CLAIM_BYTES {
        return false;
    }
    let mut r = R::new(b);
    let ok = (|| -> Res<()> {
        r.tag(CLAIM_FORMAT)?;
        r.tag(STATEMENT_ID)?;
        r.u32()?;
        if !chain_id_ok(r.bytes()?) {
            return Err(Error::Malformed("chain id"));
        }
        r.take(8 + 8 + 16 + 8 + 32 + 4 + 32 * 3 + 4 + 32 + 8 + 16)?;
        r.end()
    })();
    ok.is_ok()
}

/// Exact expected params.bin for this challenge (claim-v1 §5).
pub fn expected_params() -> Vec<u8> {
    let mut w = W::default();
    w.bytes(PARAMS_FORMAT).bytes(STATEMENT_ID).u32(PROTOCOL_VERSION).bytes(CHAIN_ID).raw(&RUNTIME_CONFIG_DIGEST);
    w.0
}
