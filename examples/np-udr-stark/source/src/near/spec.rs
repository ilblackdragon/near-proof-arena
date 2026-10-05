//! Owned mirrors of the `NearSpec` definitions the NEAR trace generators use
//! (`spec/lean/NearSpec/{Bytes,Primitives,Outcome,Trie,TransferV1,Codec}.lean`).
//!
//! Lean `Nat`s are `u64`/`u128` here (every in-domain value fits; arithmetic
//! that could leave the domain is checked and panics with "out of domain").
//! The partial trie [`PTrie`] is the inductive `NearSpec.PTrie` (a tree, not an
//! arena), built by [`build_witness`] exactly like `NearSpec.Codec.buildWitness`.

use std::collections::HashMap;

use super::reexec::sha256;
use super::reexec::spec as rx;

pub type Bytes = Vec<u8>;

/// `NearSpec.Params`.
pub mod params {
    pub const NEW_ACTION_RECEIPT_EXEC: u128 = 108_059_500_000;
    pub const TRANSFER_EXEC: u128 = 115_123_062_500;
    /// Gas burnt per Transfer receipt.
    pub const G: u128 = NEW_ACTION_RECEIPT_EXEC + TRANSFER_EXEC;
    pub const STORAGE_AMOUNT_PER_BYTE: u128 = 10_000_000_000_000_000_000;
    pub const ZERO_BALANCE_STORAGE_LIMIT: u128 = 770;
    pub const PROTOCOL_VERSION: u32 = 86;
    pub const CHAIN_ID: &[u8] = b"mainnet";
    pub const MAX_BATCH: usize = 256;
    pub const MAX_WITNESS_BYTES: u64 = 3_000_000;
    pub const U128_MAX: u128 = u128::MAX;
}

/// `AccountId.system`.
pub const SYSTEM: &[u8] = b"system";

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------

/// `leN w x`: `w` low-order little-endian bytes of `x`.
pub fn le_n(w: usize, x: u128) -> Bytes {
    (0..w).map(|i| if i < 16 { (x >> (8 * i)) as u8 } else { 0 }).collect()
}
pub fn u16b(x: u128) -> Bytes { le_n(2, x) }
pub fn u32b(x: u128) -> Bytes { le_n(4, x) }
pub fn u64b(x: u128) -> Bytes { le_n(8, x) }
pub fn u128b(x: u128) -> Bytes { le_n(16, x) }
/// `borshBytes`: `u32` length then the bytes.
pub fn borsh_bytes(b: &[u8]) -> Bytes {
    let mut v = u32b(b.len() as u128);
    v.extend_from_slice(b);
    v
}
/// `leNat` (of at most 16 bytes; higher bytes must be zero).
pub fn le_nat(b: &[u8]) -> u128 {
    let mut x: u128 = 0;
    for (i, &y) in b.iter().enumerate() {
        if i < 16 {
            x |= (y as u128) << (8 * i);
        } else {
            assert!(y == 0, "leNat: value exceeds u128");
        }
    }
    x
}
pub fn zeros(n: usize) -> Bytes { vec![0; n] }

// ---------------------------------------------------------------------------
// Primitives
// ---------------------------------------------------------------------------

/// `NearSpec.Account` (V1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Account {
    pub amount: u128,
    pub locked: u128,
    pub code_hash: Bytes,
    pub storage_usage: u128,
}

impl Account {
    pub fn encode(&self) -> Bytes {
        let mut v = u128b(self.amount);
        v.extend(u128b(self.locked));
        v.extend_from_slice(&self.code_hash);
        v.extend(u64b(self.storage_usage));
        v
    }
    /// `Account.decode`: exactly 72 bytes, amount not the V2 sentinel.
    pub fn decode(b: &[u8]) -> Option<Account> {
        if b.len() != 72 {
            return None;
        }
        let amount = le_nat(&b[..16]);
        if amount == params::U128_MAX {
            return None;
        }
        Some(Account {
            amount,
            locked: le_nat(&b[16..32]),
            code_hash: b[32..64].to_vec(),
            storage_usage: le_nat(&b[64..]),
        })
    }
    /// `⟨0, 0, [], 0⟩`
    pub fn default0() -> Account {
        Account { amount: 0, locked: 0, code_hash: vec![], storage_usage: 0 }
    }
}

/// `NearSpec.PublicKey`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PublicKey {
    pub tag: u8,
    pub data: Bytes,
}
impl PublicKey {
    pub fn encode(&self) -> Bytes {
        let mut v = vec![self.tag];
        v.extend_from_slice(&self.data);
        v
    }
}

/// `NearSpec.Receipt` (single-Transfer action receipt). `Default` is
/// `⟨[], [], [], [], ⟨0, []⟩, 0, 0⟩` (the default of `Ext.rc`).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Receipt {
    pub predecessor_id: Bytes,
    pub receiver_id: Bytes,
    pub receipt_id: Bytes,
    pub signer_id: Bytes,
    pub signer_pk: PublicKey,
    pub gas_price: u128,
    pub deposit: u128,
}

impl Receipt {
    /// Exact nearcore borsh (`Receipt.encode`).
    pub fn encode(&self) -> Bytes {
        let mut v = borsh_bytes(&self.predecessor_id);
        v.extend(borsh_bytes(&self.receiver_id));
        v.extend_from_slice(&self.receipt_id);
        v.push(0);
        v.extend(borsh_bytes(&self.signer_id));
        v.extend(self.signer_pk.encode());
        v.extend(u128b(self.gas_price));
        v.extend(u32b(0));
        v.extend(u32b(0));
        v.extend(u32b(1));
        v.push(3);
        v.extend(u128b(self.deposit));
        v
    }
    pub fn from_rx(r: &rx::Receipt<'_>) -> Receipt {
        Receipt {
            predecessor_id: r.predecessor.to_vec(),
            receiver_id: r.receiver.to_vec(),
            receipt_id: r.receipt_id.to_vec(),
            signer_id: r.signer.to_vec(),
            signer_pk: PublicKey { tag: r.signer_pk[0], data: r.signer_pk[1..].to_vec() },
            gas_price: r.gas_price,
            deposit: r.deposit,
        }
    }
}

/// `receiptIdFrom parent height idx = sha256(parent ‖ u64 height ‖ u64 idx)`.
pub fn receipt_id_from(parent: &[u8], height: u128, idx: u128) -> Bytes {
    let mut v = parent.to_vec();
    v.extend(u64b(height));
    v.extend(u64b(idx));
    sha256(&v).to_vec()
}

/// `gasRefundReceipt parent height refund`.
pub fn gas_refund_receipt(parent: &Receipt, height: u128, refund: u128) -> Receipt {
    Receipt {
        predecessor_id: SYSTEM.to_vec(),
        receiver_id: parent.signer_id.clone(),
        receipt_id: receipt_id_from(&parent.receipt_id, height, 0),
        signer_id: parent.signer_id.clone(),
        signer_pk: parent.signer_pk.clone(),
        gas_price: 0,
        deposit: refund,
    }
}

/// borsh `Vec<Receipt>`.
pub fn encode_receipts(rs: &[Receipt]) -> Bytes {
    let mut v = u32b(rs.len() as u128);
    for r in rs {
        v.extend(r.encode());
    }
    v
}
pub fn receipts_commitment(shard_id: u128, rs: &[Receipt]) -> Bytes {
    let mut v = u64b(shard_id);
    v.extend(encode_receipts(rs));
    sha256(&v).to_vec()
}
pub fn refunds_commitment(rs: &[Receipt]) -> Bytes { sha256(&encode_receipts(rs)).to_vec() }

// ---------------------------------------------------------------------------
// Outcomes
// ---------------------------------------------------------------------------

/// `NearSpec.Outcome`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    pub id: Bytes,
    pub receipt_ids: Vec<Bytes>,
    pub gas_burnt: u128,
    pub tokens_burnt: u128,
    pub executor_id: Bytes,
}
impl Outcome {
    /// `borsh(PartialExecutionOutcome)`.
    pub fn partial_encode(&self) -> Bytes {
        let mut v = u32b(self.receipt_ids.len() as u128);
        for r in &self.receipt_ids {
            v.extend_from_slice(r);
        }
        v.extend(u64b(self.gas_burnt));
        v.extend(u128b(self.tokens_burnt));
        v.extend(borsh_bytes(&self.executor_id));
        v.push(2);
        v.extend(u32b(0));
        v
    }
    /// `Outcome.leaf = sha256(u32 2 ‖ id ‖ sha256 partialEncode)`.
    pub fn leaf(&self) -> Bytes {
        let mut v = u32b(2);
        v.extend_from_slice(&self.id);
        v.extend(sha256(&self.partial_encode()));
        sha256(&v).to_vec()
    }
}

/// `merkleRoot` over already-hashed leaves.
pub fn merkle_root(leaves: &[Bytes]) -> Bytes {
    if leaves.is_empty() {
        return zeros(32);
    }
    let mut l: Vec<Bytes> = leaves.to_vec();
    while l.len() > 1 {
        l = l
            .chunks(2)
            .map(|p| if p.len() == 2 { sha256(&[p[0].as_slice(), p[1].as_slice()].concat()).to_vec() } else { p[0].clone() })
            .collect();
    }
    l.pop().unwrap()
}
pub fn outcome_root(os: &[Outcome]) -> Bytes { merkle_root(&os.iter().map(|o| o.leaf()).collect::<Vec<_>>()) }

// ---------------------------------------------------------------------------
// Trie
// ---------------------------------------------------------------------------

/// `NearSpec.Slot`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Slot {
    Val(Bytes),
    Ref(u128, Bytes),
}
impl Slot {
    pub fn value_ref(&self) -> Bytes {
        match self {
            Slot::Val(v) => [u32b(v.len() as u128), sha256(v).to_vec()].concat(),
            Slot::Ref(len, h) => [u32b(*len), h.clone()].concat(),
        }
    }
    pub fn get(&self) -> Option<&Bytes> {
        match self {
            Slot::Val(v) => Some(v),
            Slot::Ref(..) => None,
        }
    }
}

/// `NearSpec.PTrie`; `Kids` is the list of child slots (`None` = no child).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PTrie {
    Hash(Bytes),
    Leaf(Vec<u8>, Slot, u128),
    Ext(Vec<u8>, Box<PTrie>, u128),
    Branch(Option<Slot>, Vec<Option<PTrie>>, u128),
}

/// Bytes to nibbles, high nibble first.
pub fn nibbles(b: &[u8]) -> Vec<u8> {
    b.iter().flat_map(|&x| [x / 16, x % 16]).collect()
}
/// `packNibbles` (pairs; an odd last nibble is dropped).
pub fn pack_nibbles(n: &[u8]) -> Bytes {
    n.chunks_exact(2).map(|p| (p[0] as u32 * 16 + p[1] as u32) as u8).collect()
}
/// `hexPrefix nibs isLeaf`.
pub fn hex_prefix(nibs: &[u8], is_leaf: bool) -> Bytes {
    let leaf_bit: u32 = if is_leaf { 32 } else { 0 };
    if nibs.len() % 2 == 1 {
        let mut v = vec![(16 + nibs[0] as u32 + leaf_bit) as u8];
        v.extend(pack_nibbles(&nibs[1..]));
        v
    } else {
        let mut v = vec![leaf_bit as u8];
        v.extend(pack_nibbles(nibs));
        v
    }
}
/// `accountKeyPath id = nibbles (0 :: id)`.
pub fn account_key_path(id: &[u8]) -> Vec<u8> {
    let mut b = vec![0u8];
    b.extend_from_slice(id);
    nibbles(&b)
}
/// `isPrefix p l`.
pub fn is_prefix(p: &[u8], l: &[u8]) -> bool { l.starts_with(p) }

pub fn kids_bitmap(cs: &[Option<PTrie>]) -> u128 {
    cs.iter().enumerate().map(|(i, c)| if c.is_some() { 1u128 << i } else { 0 }).sum()
}

impl PTrie {
    /// The bytes the node hash is taken of (`Render.nodeSer`; `[]` for `.hash`).
    pub fn node_ser(&self) -> Bytes {
        let mut v = vec![];
        match self {
            PTrie::Hash(_) => {}
            PTrie::Leaf(k, s, mem) => {
                let hp = hex_prefix(k, true);
                v.push(0);
                v.extend(u32b(hp.len() as u128));
                v.extend(hp);
                v.extend(s.value_ref());
                v.extend(u64b(*mem));
            }
            PTrie::Ext(k, c, mem) => {
                let hp = hex_prefix(k, false);
                v.push(3);
                v.extend(u32b(hp.len() as u128));
                v.extend(hp);
                v.extend(c.hash_of());
                v.extend(u64b(*mem));
            }
            PTrie::Branch(s, cs, mem) => {
                match s {
                    None => v.push(1),
                    Some(s) => {
                        v.push(2);
                        v.extend(s.value_ref());
                    }
                }
                v.extend(u16b(kids_bitmap(cs)));
                for c in cs.iter().flatten() {
                    v.extend(c.hash_of());
                }
                v.extend(u64b(*mem));
            }
        }
        v
    }
    /// `PTrie.hashOf`.
    pub fn hash_of(&self) -> Bytes {
        match self {
            PTrie::Hash(h) => h.clone(),
            _ => sha256(&self.node_ser()).to_vec(),
        }
    }
}

// ---------------------------------------------------------------------------
// Inputs (`NearSpec.Codec`)
// ---------------------------------------------------------------------------

/// `NearSpec.TransferV1.Witness`.
#[derive(Clone, Debug)]
pub struct Witness {
    pub receipts: Vec<Receipt>,
    pub trie: PTrie,
}

/// The decoded claim (`TransferV1.Claim`; the reexec type, fixed widths).
pub type Claim = rx::Claim;

fn take(b: &[u8], n: usize) -> &[u8] { &b[..n.min(b.len())] }
fn drop(b: &[u8], n: usize) -> &[u8] { &b[n.min(b.len())..] }

/// `hpDecode`.
pub fn hp_decode(b: &[u8]) -> Vec<u8> {
    match b.split_first() {
        None => vec![],
        Some((&f, rest)) => {
            let mut v = if (f / 16) % 2 == 1 { vec![f % 16] } else { vec![] };
            v.extend(nibbles(rest));
            v
        }
    }
}

type Store = HashMap<Bytes, Bytes>;

/// `NearSpec.Codec.build` (same leniency as the Lean builder).
fn build(store: &Store, h: &[u8], keys: &[Vec<u8>]) -> PTrie {
    if keys.is_empty() {
        return PTrie::Hash(h.to_vec());
    }
    let Some(node) = store.get(h) else { return PTrie::Hash(h.to_vec()) };
    let val = |len: u128, vh: &[u8], want: bool| -> Slot {
        if want {
            if let Some(v) = store.get(vh) {
                if v.len() as u128 == len {
                    return Slot::Val(v.clone());
                }
            }
        }
        Slot::Ref(len, vh.to_vec())
    };
    let mem = le_nat(drop(node, node.len().saturating_sub(8)));
    let body = take(node, node.len().saturating_sub(8));
    let Some((&t, rest)) = body.split_first() else { return PTrie::Hash(h.to_vec()) };
    match t {
        0 => {
            let klen = le_nat(take(rest, 4)) as usize;
            let k = hp_decode(take(drop(rest, 4), klen));
            let r2 = drop(rest, 4 + klen);
            let want = keys.iter().any(|x| *x == k);
            let s = val(le_nat(take(r2, 4)), take(drop(r2, 4), 32), want);
            PTrie::Leaf(k, s, mem)
        }
        3 => {
            let klen = le_nat(take(rest, 4)) as usize;
            let k = hp_decode(take(drop(rest, 4), klen));
            let child = take(drop(rest, 4 + klen), 32);
            let keys2: Vec<Vec<u8>> = keys.iter().filter(|x| is_prefix(&k, x)).map(|x| x[k.len()..].to_vec()).collect();
            PTrie::Ext(k.clone(), Box::new(build(store, child, &keys2)), mem)
        }
        _ => {
            let (vslot, rest) = if t == 2 {
                let want = keys.iter().any(|x| x.is_empty());
                (Some(val(le_nat(take(rest, 4)), take(drop(rest, 4), 32), want)), drop(rest, 36))
            } else {
                (None, rest)
            };
            let mut bm = le_nat(take(rest, 2));
            let mut bs = drop(rest, 2);
            let mut kids = Vec::with_capacity(16);
            for i in 0..16u8 {
                if bm % 2 == 1 {
                    let ch = take(bs, 32);
                    bs = drop(bs, 32);
                    let ks: Vec<Vec<u8>> =
                        keys.iter().filter(|x| x.first() == Some(&i)).map(|x| x[1..].to_vec()).collect();
                    kids.push(Some(build(store, ch, &ks)));
                } else {
                    kids.push(None);
                }
                bm /= 2;
            }
            PTrie::Branch(vslot, kids, mem)
        }
    }
}

/// Decoded inputs: the request's claim header fields, the witness, the claim.
pub struct Inputs {
    pub claim: Claim,
    pub witness: Witness,
}

/// Decode `request.bin` / `witness.bin` (`Codec.decodeRequest`,
/// `decodeWitness`, `buildWitness`) and derive the claim (reexec engine,
/// = `Codec.deriveClaim`).  `Err` if malformed or out of domain.
pub fn load_inputs(request: &[u8], witness: &[u8]) -> Result<Inputs, String> {
    let claim = super::reexec::engine::derive_claim(request, witness)?;
    let req = rx::decode_request(request).map_err(|e| format!("request: {e}"))?;
    let (_, values) = rx::decode_witness(witness).map_err(|e| format!("witness: {e}"))?;
    let store: Store = values.iter().map(|v| (sha256(v).to_vec(), v.to_vec())).collect();
    let receipts: Vec<Receipt> = req.receipts.iter().map(Receipt::from_rx).collect();
    let keys: Vec<Vec<u8>> = receipts.iter().map(|r| account_key_path(&r.receiver_id)).collect();
    let trie = build(&store, &req.pre_state_root, &keys);
    Ok(Inputs { claim, witness: Witness { receipts, trie } })
}
