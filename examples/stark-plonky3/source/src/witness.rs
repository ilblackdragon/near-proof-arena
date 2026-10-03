//! The structured witness: everything the trace generator needs, derived
//! natively from `request.bin` + `witness.bin`.
//!
//! The relation is first re-executed with the reference engine (copied from
//! `examples/reexec-witness`): out-of-domain requests are refused here,
//! before any proving work, and the claim is derived. The STARK witness is
//! then built from the same data (trie paths, account chains, outcome tree,
//! all hashed messages).

use crate::consts::*;
use crate::engine::{domain_static, run_batch};
use crate::sha256;
use crate::spec::*;
use crate::trie::{PTrie, Store, nibbles_of};
use crate::wire::{Reader, Writer};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct RcptW {
    pub pred: Vec<u8>,
    pub recv: Vec<u8>,
    pub signer: Vec<u8>,
    pub rid: [u8; 32],
    pub kt: u8,
    pub pk: [u8; 64],
    pub gp: u128,
    pub dep: u128,
    pub hr: bool,
    pub d: u128,
    pub burnt: u128,
    pub ramt: u128,
    pub tok: u128,
    pub rf: u32,
    pub refund_id: [u8; 32],
    pub peo_dig: [u8; 32],
    pub k: usize,
    pub t_prev: u32,
    pub abef: u128,
    pub aaft: u128,
    pub locked: u128,
    pub storage: u64,
    pub o: u32,
    pub o2: u32,
}

#[derive(Clone, Debug)]
pub struct AcctW {
    pub id: Vec<u8>,
    pub val: [u8; 72],
    pub post_amt: u128,
    pub owner: usize,
    pub iterm: u32,
    pub t_last: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NKind {
    Leaf,
    Ext,
    B1,
    B2,
}

#[derive(Clone, Debug)]
pub struct NodeW {
    pub kind: NKind,
    pub odd: bool,
    pub x0: u8,
    /// HP key bytes after the flag byte.
    pub keybytes: Vec<u8>,
    /// Key segment nibbles (leaf / ext).
    pub nibbles: Vec<u8>,
    pub vlen: [u8; 4],
    pub vh: [u8; 32],
    pub touched: Option<usize>,
    pub bm: u16,
    /// Pre-state child hash per slot (ext: slot 0).
    pub child_hash: [Option<[u8; 32]>; 16],
    /// Revealed child node ids.
    pub cid: [Option<usize>; 16],
    pub mem: [u8; 8],
    pub pre: Vec<u8>,
    pub post: Vec<u8>,
    pub pre_dig: [u8; 32],
    pub post_dig: [u8; 32],
}

impl NodeW {
    pub fn s(&self) -> u32 {
        self.nibbles.len() as u32
    }
}

#[derive(Clone, Debug, Default)]
pub struct PathRowW {
    pub k: usize,
    pub t: u32,
    pub nib: u8,
    pub n: usize,
    pub i: u32,
    pub n2: usize,
    pub i2: u32,
    pub jump: bool,
    pub n3: usize,
    pub i3: u32,
    pub start: bool,
    pub end: bool,
}

#[derive(Clone, Debug)]
pub struct MrkRowW {
    pub j: u32,
    pub i: u32,
    pub sp: u32,
    pub s: u32,
    pub odd: bool,
    pub lil: bool,
    pub root: bool,
    pub msg_l: MsgId,
    pub msg_r: MsgId,
    pub own: MsgId,
    pub l: [u8; 32],
    pub r: [u8; 32],
}

pub struct Wit {
    pub claim: Claim,
    pub claim_bytes: Vec<u8>,
    pub pv: Vec<u8>,
    pub receipts: Vec<RcptW>,
    pub accounts: Vec<AcctW>,
    pub nodes: Vec<NodeW>,
    pub paths: Vec<PathRowW>,
    pub mrk: Vec<MrkRowW>,
    pub sorted_rids: Vec<[u8; 32]>,
    /// Every hashed message: (msg id, bytes, digest).
    pub msgs: Vec<(MsgId, Vec<u8>, [u8; 32])>,
}

fn parse_node(raw: &[u8]) -> Result<NodeW, String> {
    let mut r = Reader::new(raw);
    let e = |x: crate::wire::WireError| format!("trie node: {x}");
    let tag = r.u8("tag").map_err(e)?;
    let mut n = NodeW {
        kind: NKind::Leaf,
        odd: false,
        x0: 0,
        keybytes: vec![],
        nibbles: vec![],
        vlen: [0; 4],
        vh: [0; 32],
        touched: None,
        bm: 0,
        child_hash: [None; 16],
        cid: [None; 16],
        mem: [0; 8],
        pre: raw.to_vec(),
        post: vec![],
        pre_dig: sha256(raw),
        post_dig: [0; 32],
    };
    match tag {
        0 | 3 => {
            n.kind = if tag == 0 { NKind::Leaf } else { NKind::Ext };
            let hp = r.bytes("hp").map_err(e)?;
            if hp.is_empty() || hp.len() > 1 + MAX_KEY_BYTES {
                return Err("hp length".into());
            }
            let f = hp[0];
            let leaf = (f >> 5) & 1 == 1;
            n.odd = (f >> 4) & 1 == 1;
            n.x0 = f & 15;
            if f >> 6 != 0 || leaf != (tag == 0) || (!n.odd && n.x0 != 0) {
                return Err("non-canonical hp flags".into());
            }
            n.keybytes = hp[1..].to_vec();
            if n.odd {
                n.nibbles.push(n.x0);
            }
            for &b in &n.keybytes {
                n.nibbles.push(b >> 4);
                n.nibbles.push(b & 15);
            }
            if tag == 0 {
                n.vlen = r.take(4, "vlen").map_err(e)?.try_into().unwrap();
                n.vh = r.hash("vh").map_err(e)?;
            } else {
                n.child_hash[0] = Some(r.hash("child").map_err(e)?);
            }
        }
        1 | 2 => {
            n.kind = if tag == 1 { NKind::B1 } else { NKind::B2 };
            if tag == 2 {
                n.vlen = r.take(4, "vlen").map_err(e)?.try_into().unwrap();
                n.vh = r.hash("vh").map_err(e)?;
            }
            n.bm = r.u16("bm").map_err(e)?;
            for j in 0..16 {
                if n.bm >> j & 1 == 1 {
                    n.child_hash[j] = Some(r.hash("child").map_err(e)?);
                }
            }
        }
        _ => return Err("node tag".into()),
    }
    n.mem = r.take(8, "mem").map_err(e)?.try_into().unwrap();
    r.finish().map_err(e)?;
    Ok(n)
}

/// Byte offsets of the 32-byte windows that may differ between the pre and
/// post serialization: (offset, Some(slot) for child windows / None for value).
pub fn node_windows(n: &NodeW) -> Vec<(usize, Option<usize>)> {
    let hp = 1 + n.keybytes.len();
    let mut w = vec![];
    match n.kind {
        NKind::Leaf => w.push((5 + hp + 4, None)),
        NKind::Ext => w.push((5 + hp, Some(0))),
        NKind::B1 | NKind::B2 => {
            if n.kind == NKind::B2 {
                w.push((1 + 4, None));
            }
            let mut pos = if n.kind == NKind::B1 { 3 } else { 39 };
            for j in 0..16 {
                if n.bm >> j & 1 == 1 {
                    w.push((pos, Some(j)));
                    pos += 32;
                }
            }
        }
    }
    w
}

struct Builder<'s> {
    store: &'s HashMap<[u8; 32], &'s [u8]>,
    nodes: Vec<NodeW>,
}

impl Builder<'_> {
    /// Reveal the node with hash `h` for the accounts `keys` (remaining nibbles).
    fn build(&mut self, h: [u8; 32], keys: Vec<(usize, Vec<u8>)>) -> Result<usize, String> {
        let raw = self.store.get(&h).ok_or("unrevealed trie node on a receiver path")?;
        let mut n = parse_node(raw)?;
        let id = self.nodes.len();
        self.nodes.push(n.clone());
        match n.kind {
            NKind::Leaf => {
                for (k, rest) in &keys {
                    if rest == &n.nibbles {
                        n.touched = Some(*k);
                    } else {
                        return Err("receiver key not in trie".into());
                    }
                }
            }
            NKind::Ext => {
                let mut sub = vec![];
                for (k, rest) in keys {
                    if !rest.starts_with(&n.nibbles) {
                        return Err("receiver key not in trie".into());
                    }
                    sub.push((k, rest[n.nibbles.len()..].to_vec()));
                }
                let c = self.build(n.child_hash[0].unwrap(), sub)?;
                n.cid[0] = Some(c);
            }
            NKind::B1 | NKind::B2 => {
                let mut per: Vec<Vec<(usize, Vec<u8>)>> = vec![vec![]; 16];
                for (k, rest) in keys {
                    if rest.is_empty() {
                        if n.kind != NKind::B2 {
                            return Err("receiver key not in trie".into());
                        }
                        n.touched = Some(k);
                    } else {
                        per[rest[0] as usize].push((k, rest[1..].to_vec()));
                    }
                }
                for j in 0..16 {
                    if !per[j].is_empty() {
                        let ch = n.child_hash[j].ok_or("receiver key not in trie")?;
                        let sub = std::mem::take(&mut per[j]);
                        n.cid[j] = Some(self.build(ch, sub)?);
                    }
                }
            }
        }
        self.nodes[id] = n;
        Ok(id)
    }
}

fn merkle_rows(leaves: &[(MsgId, [u8; 32])]) -> (Vec<MrkRowW>, Vec<(MsgId, Vec<u8>, [u8; 32])>) {
    let mut rows = vec![];
    let mut msgs = vec![];
    let mut level: Vec<(MsgId, [u8; 32])> = leaves.to_vec();
    let mut j = 1u32;
    let mut idx = 0u32;
    loop {
        let sp = level.len() as u32;
        let s = sp.div_ceil(2);
        let odd = sp % 2 == 1;
        let mut next = vec![];
        for i in 0..s {
            let lil = i == s - 1;
            let root = s == 1;
            let (ml, dl) = level[2 * i as usize];
            if lil && odd {
                rows.push(MrkRowW {
                    j, i, sp, s, odd, lil, root, msg_l: ml, msg_r: (0, 0), own: ml, l: [0; 32], r: [0; 32],
                });
                next.push((ml, dl));
            } else {
                let (mr, dr) = level[2 * i as usize + 1];
                let own = (K_MRK, idx);
                let mut buf = Vec::with_capacity(64);
                buf.extend_from_slice(&dl);
                buf.extend_from_slice(&dr);
                let dg = sha256(&buf);
                msgs.push((own, buf, dg));
                rows.push(MrkRowW { j, i, sp, s, odd, lil, root, msg_l: ml, msg_r: mr, own, l: dl, r: dr });
                next.push((own, dg));
            }
            idx += 1;
        }
        if s == 1 {
            break;
        }
        level = next;
        j += 1;
    }
    (rows, msgs)
}

/// Build the structured witness. `Err` = out of domain or malformed input.
pub fn build(request: &[u8], witness: &[u8]) -> Result<Wit, String> {
    build_opts(request, witness, true)
}

/// `checked = false` (testing only): skip the reference re-execution's domain
/// checks and build traces anyway with wrapping arithmetic, so that the AIR's
/// own rejection of out-of-domain witnesses can be tested (`npdev conform`).
/// The claim is then whatever this builder computed.
pub fn build_opts(request: &[u8], witness: &[u8], checked: bool) -> Result<Wit, String> {
    let req = decode_request(request).map_err(|e| format!("request: {e}"))?;
    let (wroot, values) = decode_witness(witness).map_err(|e| format!("witness: {e}"))?;
    if wroot != req.pre_state_root {
        return Err("witness pre_state_root != request pre_state_root".into());
    }
    let mut store: Store<'_> = Store::with_capacity(values.len());
    for v in &values {
        store.insert(sha256(v), v);
    }
    // ---- reference re-execution (domain + claim) ----
    let keys: Vec<Vec<u8>> = req.receipts.iter().map(|r| nibbles_of(0, r.receiver)).collect();
    let key_refs: Vec<&[u8]> = keys.iter().map(|k| k.as_slice()).collect();
    let mut trie = PTrie::build(&store, req.pre_state_root, &key_refs)?;
    let out = if checked {
        domain_static(req.protocol_version, req.chain_id, req.gas_limit, &req.receipts, trie.revealed_bytes())?;
        Some(run_batch(req.block_height, req.block_gas_price, &mut trie, &req.receipts)?)
    } else {
        if req.receipts.is_empty() {
            return Err("unconstructible: empty batch".into());
        }
        None
    };
    let mut rcw = Writer::with_capacity(8 + req.receipts_bytes.len());
    rcw.u64(req.shard_id).raw(req.receipts_bytes);
    let rc_digest = sha256(&rcw.0);
    let nref = req.receipts.iter().filter(|r| r.gas_price > req.block_gas_price).count() as u32;
    let out = out.unwrap_or(crate::engine::Outputs {
        slice_post_root: [0; 32],
        outcome_root: [0; 32],
        refund_count: nref,
        refunds_commitment: [0; 32],
        gas_burnt_total: (G as u64).wrapping_mul(req.receipts.len() as u64),
        tokens_burnt_total: 0,
    });
    let mut claim = Claim {
        protocol_version: req.protocol_version,
        chain_id: req.chain_id.to_vec(),
        shard_id: req.shard_id,
        block_height: req.block_height,
        block_gas_price: req.block_gas_price,
        gas_limit: req.gas_limit,
        pre_state_root: req.pre_state_root,
        receipt_count: req.receipts.len() as u32,
        receipts_commitment: rc_digest,
        slice_post_root: out.slice_post_root,
        outcome_root: out.outcome_root,
        refund_count: out.refund_count,
        refunds_commitment: out.refunds_commitment,
        gas_burnt_total: out.gas_burnt_total,
        tokens_burnt_total: out.tokens_burnt_total,
    };
    let mut msgs: Vec<(MsgId, Vec<u8>, [u8; 32])> = vec![((K_RC, 0), rcw.0.clone(), rc_digest)];

    // ---- accounts and trie paths ----
    let mut acct_of: HashMap<Vec<u8>, usize> = HashMap::new();
    let mut accounts: Vec<AcctW> = vec![];
    for r in &req.receipts {
        if !acct_of.contains_key(r.receiver) {
            acct_of.insert(r.receiver.to_vec(), accounts.len());
            accounts.push(AcctW {
                id: r.receiver.to_vec(),
                val: [0; 72],
                post_amt: 0,
                owner: 0,
                iterm: 0,
                t_last: 0,
            });
        }
    }
    let mut b = Builder { store: &store, nodes: vec![] };
    let akeys: Vec<(usize, Vec<u8>)> =
        accounts.iter().enumerate().map(|(k, a)| (k, nibbles_of(0, &a.id))).collect();
    b.build(req.pre_state_root, akeys)?;
    let mut nodes = b.nodes;
    for (id, n) in nodes.iter().enumerate() {
        if let Some(k) = n.touched {
            let v = store.get(&n.vh).ok_or("account value not revealed")?;
            if v.len() != 72 || n.vlen != 72u32.to_le_bytes() {
                return Err("account value is not 72 bytes".into());
            }
            accounts[k].val.copy_from_slice(v);
            accounts[k].owner = id;
            accounts[k].iterm = if n.kind == NKind::Leaf { n.s() } else { 0 };
        }
    }
    // ---- receipts ----
    let bgp = req.block_gas_price;
    let mut amounts: Vec<u128> =
        accounts.iter().map(|a| u128::from_le_bytes(a.val[..16].try_into().unwrap())).collect();
    let mut last_t: Vec<u32> = vec![0; accounts.len()];
    let mut receipts = vec![];
    let mut tok: u128 = 0;
    let mut rf: u32 = 0;
    let mut o: u32 = 12;
    let mut o2: u32 = 4;
    let mut leaves: Vec<(MsgId, [u8; 32])> = vec![];
    let mut rfw = Writer::with_capacity(4 + 200 * req.receipts.len());
    rfw.u32(out.refund_count);
    for (r_idx, r) in req.receipts.iter().enumerate() {
        let k = acct_of[r.receiver];
        let hr = r.gas_price > bgp;
        let p = r.gas_price.min(bgp);
        let d = if hr { r.gas_price - bgp } else { bgp - r.gas_price };
        let burnt = (G as u128).wrapping_mul(p);
        let ramt = if hr { (G as u128).wrapping_mul(d) } else { 0 };
        tok = tok.wrapping_add(burnt);
        if hr {
            rf += 1;
        }
        let mut pk = [0u8; 64];
        let kt = r.signer_pk[0];
        pk[..r.signer_pk.len() - 1].copy_from_slice(&r.signer_pk[1..]);
        let mut refund_id = [0u8; 32];
        if hr {
            let mut idb = Vec::with_capacity(48);
            idb.extend_from_slice(&r.receipt_id);
            idb.extend_from_slice(&req.block_height.to_le_bytes());
            idb.extend_from_slice(&0u64.to_le_bytes());
            refund_id = sha256(&idb);
            msgs.push(((K_RID, r_idx as u32), idb, refund_id));
            write_refund(&mut rfw, r, &refund_id, ramt);
        }
        let mut peo = Writer::with_capacity(128);
        if hr {
            peo.u32(1).raw(&refund_id);
        } else {
            peo.u32(0);
        }
        peo.u64(G).u128(burnt).bytes(r.receiver).u8(2).u32(0);
        let peo_dig = sha256(&peo.0);
        msgs.push(((K_PEO, r_idx as u32), peo.0, peo_dig));
        let mut leaf = Vec::with_capacity(68);
        leaf.extend_from_slice(&2u32.to_le_bytes());
        leaf.extend_from_slice(&r.receipt_id);
        leaf.extend_from_slice(&peo_dig);
        let ld = sha256(&leaf);
        msgs.push(((K_LEAF, r_idx as u32), leaf, ld));
        leaves.push(((K_LEAF, r_idx as u32), ld));
        let abef = amounts[k];
        let aaft = abef.wrapping_add(r.deposit);
        amounts[k] = aaft;
        let t_prev = last_t[k];
        last_t[k] = r_idx as u32 + 1;
        let val = &accounts[k].val;
        let rw = RcptW {
            pred: r.predecessor.to_vec(),
            recv: r.receiver.to_vec(),
            signer: r.signer.to_vec(),
            rid: r.receipt_id,
            kt,
            pk,
            gp: r.gas_price,
            dep: r.deposit,
            hr,
            d,
            burnt,
            ramt,
            tok,
            rf,
            refund_id,
            peo_dig,
            k,
            t_prev,
            abef,
            aaft,
            locked: u128::from_le_bytes(val[16..32].try_into().unwrap()),
            storage: u64::from_le_bytes(val[64..72].try_into().unwrap()),
            o,
            o2,
        };
        o += (crate::air::rcpt::RC_FIXED as usize
            + r.predecessor.len()
            + r.receiver.len()
            + r.signer.len()
            + 32 * kt as usize) as u32;
        if hr {
            o2 += (crate::air::rcpt::RF_FIXED as usize + 2 * r.signer.len() + 32 * kt as usize) as u32;
        }
        receipts.push(rw);
    }
    if rfw.0.len() as u32 != o2 || rcw.0.len() as u32 != o {
        return Err("internal: offset mismatch".into());
    }
    msgs.push(((K_RF, 0), rfw.0.clone(), sha256(&rfw.0)));
    if checked && sha256(&rfw.0) != claim.refunds_commitment {
        return Err("internal: refunds commitment mismatch".into());
    }
    claim.refunds_commitment = sha256(&rfw.0);
    claim.tokens_burnt_total = tok;
    for (k, a) in accounts.iter_mut().enumerate() {
        a.post_amt = amounts[k];
        a.t_last = last_t[k];
    }
    // ---- post-state node serializations (children have larger ids) ----
    for id in (0..nodes.len()).rev() {
        let mut post = nodes[id].pre.clone();
        for (off, slot) in node_windows(&nodes[id]) {
            let repl: Option<[u8; 32]> = match slot {
                Some(j) => nodes[id].cid[j].map(|c| nodes[c].post_dig),
                None => nodes[id].touched.map(|k| {
                    let a = &accounts[k];
                    let mut v = a.val;
                    v[..16].copy_from_slice(&a.post_amt.to_le_bytes());
                    sha256(&v)
                }),
            };
            if let Some(h) = repl {
                post[off..off + 32].copy_from_slice(&h);
            }
        }
        nodes[id].post_dig = sha256(&post);
        nodes[id].post = post;
    }
    if nodes[0].pre_dig != claim.pre_state_root || (checked && nodes[0].post_dig != claim.slice_post_root) {
        return Err("internal: trie root mismatch".into());
    }
    claim.slice_post_root = nodes[0].post_dig;
    for (id, n) in nodes.iter().enumerate() {
        msgs.push(((K_NPRE, id as u32), n.pre.clone(), n.pre_dig));
        msgs.push(((K_NPOST, id as u32), n.post.clone(), n.post_dig));
    }
    for (k, a) in accounts.iter().enumerate() {
        let mut v = a.val;
        msgs.push(((K_VPRE, k as u32), v.to_vec(), sha256(&v)));
        v[..16].copy_from_slice(&a.post_amt.to_le_bytes());
        msgs.push(((K_VPOST, k as u32), v.to_vec(), sha256(&v)));
    }
    // ---- walks ----
    let mut paths = vec![];
    for (k, a) in accounts.iter().enumerate() {
        let key = nibbles_of(0, &a.id);
        let (mut n, mut i) = (0usize, 0u32);
        for (t, &x) in key.iter().enumerate() {
            let node = &nodes[n];
            let (n2, i2) = match node.kind {
                NKind::B1 | NKind::B2 => (node.cid[x as usize].ok_or("walk: missing child")?, 0),
                _ => {
                    if node.nibbles.get(i as usize) != Some(&x) {
                        return Err("walk: key mismatch".into());
                    }
                    (n, i + 1)
                }
            };
            let (jump, n3, i3) = if nodes[n2].kind == NKind::Ext && i2 == nodes[n2].s() && i2 > 0 {
                (true, nodes[n2].cid[0].ok_or("walk: ext child")?, 0)
            } else {
                (false, n2, i2)
            };
            paths.push(PathRowW {
                k,
                t: t as u32,
                nib: x,
                n,
                i,
                n2,
                i2,
                jump,
                n3,
                i3,
                start: t == 0,
                end: t + 1 == key.len(),
            });
            n = n3;
            i = i3;
        }
        if n != a.owner || i != a.iterm {
            return Err("walk: does not end at the value slot".into());
        }
    }
    // ---- outcome tree ----
    let (mrk, mmsgs) = merkle_rows(&leaves);
    let root_digest = {
        let mut dig: HashMap<MsgId, [u8; 32]> = leaves.iter().copied().collect();
        for (m, _, d) in &mmsgs {
            dig.insert(*m, *d);
        }
        dig[&mrk.last().unwrap().own]
    };
    if checked && root_digest != claim.outcome_root {
        return Err("internal: outcome root mismatch".into());
    }
    claim.outcome_root = root_digest;
    msgs.extend(mmsgs);
    let claim_bytes = claim.encode();
    let pv = claim_bytes[claim_bytes.len() - NUM_PV..].to_vec();
    let mut sorted_rids: Vec<[u8; 32]> = receipts.iter().map(|r| r.rid).collect();
    sorted_rids.sort_by(|a, b| a.iter().rev().cmp(b.iter().rev()));
    Ok(Wit { claim, claim_bytes, pv, receipts, accounts, nodes, paths, mrk, sorted_rids, msgs })
}
