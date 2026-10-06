//! Shared data of the honest-trace generators (`ZkFormal/Near/Render/Common.lean`).
//!
//! Cells are `u32` naturals `< p` (BabyBear); rows are `Vec<u32>`.

use std::collections::HashMap;

use super::ext::*;
use super::ids::*;
use super::reexec::sha256;
use super::spec::*;

/// A table row (cells `< p`).
pub type Row = Vec<u32>;

/// The BabyBear prime `p = 15·2^27 + 1`.
pub const P: u64 = 2013265921;

/// `toNats`/`shaN`: SHA-256 as a byte vector.
pub fn sha_n(b: &[u8]) -> Bytes { sha256(b).to_vec() }

/// A message emitted on `BYTES` (`id = kind + 16·idx`); its digest is consumed
/// exactly once on `DIGEST`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Msg {
    pub id: u32,
    pub bytes: Bytes,
}

/// `clog2 n`: smallest `l` with `n ≤ 2^l`.
pub fn clog2(n: usize) -> usize {
    let mut l = 0;
    while (1usize << l) < n {
        l += 1;
    }
    l
}
/// `logOf n = max 1 (clog2 n)`.
pub fn log_of(n: usize) -> usize { clog2(n).max(1) }
/// `padTo rows pad`: pad with copies of `pad` to `2^logOf |rows|` rows.
pub fn pad_to(mut rows: Vec<Row>, pad: Row) -> Vec<Row> {
    let h = 1usize << log_of(rows.len());
    rows.resize(h, pad);
    rows
}
/// `zeroRow w`.
pub fn zero_row(w: usize) -> Row { vec![0; w] }
/// `mkTab H W f`.
pub fn mk_tab(h: usize, w: usize, f: impl Fn(usize, usize) -> u64) -> Vec<Row> {
    (0..h).map(|q| (0..w).map(|c| cell(f(q, c))).collect()).collect()
}
/// A cell value (must already be `< p`).
#[inline]
pub fn cell(x: u64) -> u32 {
    debug_assert!(x < P, "cell value {x} not < p");
    x as u32
}
/// `leBytes w x`.
pub fn le_bytes(w: usize, x: u128) -> Bytes { le_n(w, x) }
/// `invP x = x^(p−2) mod p` (`0 ↦ 0`).
pub fn inv_p(x: u64) -> u64 {
    let (mut b, mut e, mut r) = (x % P, P - 2, 1u64);
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % P;
        }
        b = b * b % P;
        e >>= 1;
    }
    r
}

/// `kidIds nr`: revealed child ids.
pub fn kid_ids(nr: &NodeRec) -> Vec<usize> {
    nr.kids().iter().filter_map(|k| if let Kid::Node(c) = k { Some(*c) } else { None }).collect()
}

/// Everything the generators need about an `Ext` and its claim (`Info`).
#[derive(Clone, Debug)]
pub struct Info {
    pub e: Ext,
    pub c: Claim,
    pub ns: Vec<NodeRec>,
    /// pre / post serialization (`nodeSer` of the record tries) of each node
    pub pre: Vec<Bytes>,
    pub post: Vec<Bytes>,
    /// depth of each node (root `0`)
    pub depth: Vec<usize>,
    /// walk target: the node itself, or (empty-key extension with a revealed
    /// child) its child's target
    pub res: Vec<usize>,
    /// pre / post value bytes of touched slots (72 bytes; `[]` elsewhere)
    pub vpre: Vec<Bytes>,
    pub vpost: Vec<Bytes>,
    /// touched slots, ascending
    pub touched: Vec<usize>,
}

static EMPTY: Vec<u8> = Vec::new();

impl Info {
    /// `pre.getD n []`
    pub fn pre_at(&self, n: usize) -> &Bytes { self.pre.get(n).unwrap_or(&EMPTY) }
    pub fn post_at(&self, n: usize) -> &Bytes { self.post.get(n).unwrap_or(&EMPTY) }
    pub fn vpre_at(&self, n: usize) -> &Bytes { self.vpre.get(n).unwrap_or(&EMPTY) }
    pub fn vpost_at(&self, n: usize) -> &Bytes { self.vpost.get(n).unwrap_or(&EMPTY) }
    /// `res.getD n d`
    pub fn res_or(&self, n: usize, d: usize) -> usize { self.res.get(n).copied().unwrap_or(d) }
    /// `preDig n = sha256 (pre n)`
    pub fn pre_dig(&self, n: usize) -> Bytes { sha_n(self.pre_at(n)) }
    pub fn post_dig(&self, n: usize) -> Bytes { sha_n(self.post_at(n)) }
    /// `nodeAt n` (default `.branch none [] 0`).
    pub fn node_at(&self, n: usize) -> NodeRec { self.ns.get(n).cloned().unwrap_or_else(NodeRec::dflt) }
    /// `nRcpt`.
    pub fn n_rcpt(&self) -> usize { self.e.rs.len() }
    /// Public inputs `c.encode` as naturals (`pubOf`).
    pub fn pub_nats(&self) -> Vec<u32> { self.c.encode().iter().map(|&b| b as u32).collect() }
}

/// `resF ns f n`.
pub fn res_f(ns: &[NodeRec], f: usize, n: usize) -> usize {
    let (mut f, mut n) = (f, n);
    loop {
        if f == 0 {
            return n;
        }
        match ns.get(n) {
            Some(NodeRec::Ext(k, Kid::Node(c), _)) if k.is_empty() => {
                n = *c;
                f -= 1;
            }
            _ => return n,
        }
    }
}

/// `subD ns f n d`: preorder `(node, depth)` (fuel `f`).
fn sub_d(ns: &[NodeRec], f: usize, n: usize, d: usize, out: &mut Vec<(usize, usize)>) {
    if f == 0 {
        return;
    }
    out.push((n, d));
    let nr = ns.get(n).cloned().unwrap_or_else(NodeRec::dflt);
    for c in kid_ids(&nr) {
        sub_d(ns, f - 1, c, d + 1, out);
    }
}

/// `nodeSer (treeOf ns vals N n)` for every node, memoized bottom-up
/// (equal to the Lean definition on records whose child links form a tree;
/// the fuel `N` never runs out there).
fn sers(ns: &[NodeRec], vals: &dyn Fn(usize) -> Bytes) -> Vec<Bytes> {
    let n = ns.len();
    let mut memo: Vec<Option<Bytes>> = vec![None; n];
    fn go(ns: &[NodeRec], vals: &dyn Fn(usize) -> Bytes, memo: &mut Vec<Option<Bytes>>, f: usize, i: usize) -> Bytes {
        // returns nodeSer of (treeOf ns vals f i); memoized for f large enough
        if let Some(s) = &memo[i] {
            return s.clone();
        }
        let dig = |c: usize, memo: &mut Vec<Option<Bytes>>| -> Bytes {
            if f <= 1 || c >= ns.len() {
                vec![] // `.hash []`
            } else {
                sha_n(&go(ns, vals, memo, f - 1, c))
            }
        };
        let vh = |nr: &NodeRec| -> Bytes { if nr.touched() { sha_n(&vals(i)) } else { vec![] } };
        let nr = &ns[i];
        let mut digs: HashMap<usize, Bytes> = HashMap::new();
        for c in kid_ids(nr) {
            let d = dig(c, memo);
            digs.insert(c, d);
        }
        // `nodeSer` of the record trie: as `ser`, but a touched value's
        // `valueRef` is `u32 |vals i| ‖ sha256 (vals i)` (honest: |vals i| = 72)
        let s = match nr {
            NodeRec::Leaf(k, VSlot::Touched, mem) => {
                let hp = hex_prefix(k, true);
                let v = vals(i);
                [vec![0], u32b(hp.len() as u128), hp, u32b(v.len() as u128), sha_n(&v), u64b(*mem)].concat()
            }
            NodeRec::Branch(Some(VSlot::Touched), kids, mem) => {
                let v = vals(i);
                let mut out = [vec![2], u32b(v.len() as u128), sha_n(&v), u16b(bitmap_of(kids))].concat();
                for k in kids {
                    out.extend(kid_bytes(&|c| digs[&c].clone(), k));
                }
                out.extend(u64b(*mem));
                out
            }
            _ => ser(&vh(nr), &|c| digs[&c].clone(), nr),
        };
        memo[i] = Some(s.clone());
        s
    }
    (0..n).map(|i| go(ns, vals, &mut memo, n, i)).collect()
}

/// `mkInfo c e`.
pub fn mk_info(c: &Claim, e: &Ext) -> Info {
    let ns = e.ns.clone();
    let n = ns.len();
    let touched: Vec<usize> = (0..n).filter(|&k| ns[k].touched()).collect();
    let vpre: Vec<Bytes> = (0..n).map(|k| if ns[k].touched() { e.vals0(k) } else { vec![] }).collect();
    let nr = e.rs.len();
    let vpost: Vec<Bytes> = (0..n).map(|k| if ns[k].touched() { e.vals_at(nr, k) } else { vec![] }).collect();
    let res: Vec<usize> = (0..n).map(|k| res_f(&ns, n + 1, k)).collect();
    let pre = sers(&ns, &|k| e.vals0(k));
    let post = sers(&ns, &|k| e.vals_at(nr, k));
    let mut depth = vec![0usize; n];
    let mut sd = vec![];
    sub_d(&ns, n + 1, 0, 0, &mut sd);
    for (k, d) in sd {
        if k < n {
            depth[k] = d;
        }
    }
    Info { e: e.clone(), c: c.clone(), ns, pre, post, depth, res, vpre, vpost, touched }
}

// ---------------------------------------------------------------------------
// Walks
// ---------------------------------------------------------------------------

/// An edge `[N, I, sym, N2, I2]`.
pub type Edge = Vec<usize>;

/// `keySyms rc = nibbles (0 ‖ receiver) ++ [END]`.
pub fn key_syms(rc: &Receipt) -> Vec<usize> {
    let mut v: Vec<usize> = account_key_path(&rc.receiver_id).into_iter().map(|x| x as usize).collect();
    v.push(SYM_END);
    v
}

/// `stepOf I N i sym`.
pub fn step_of(i: &Info, nn: usize, ii: usize, sym: usize) -> Result<(usize, usize), String> {
    let Some(nr) = i.ns.get(nn) else { return Err(format!("walk: node {nn} missing")) };
    match nr {
        NodeRec::Leaf(k, v, _) => {
            if sym < 16 {
                if k.get(ii).map(|&x| x as usize) == Some(sym) {
                    Ok((nn, ii + 1))
                } else {
                    Err(format!("walk: leaf {nn} key mismatch at {ii}"))
                }
            } else if sym == SYM_END && ii == k.len() && *v == VSlot::Touched {
                Ok((nn, 0))
            } else {
                Err(format!("walk: leaf {nn} END at {ii}"))
            }
        }
        NodeRec::Ext(k, kid, _) => {
            if sym < 16 && k.get(ii).map(|&x| x as usize) == Some(sym) {
                if ii + 1 == k.len() {
                    match kid {
                        Kid::Node(c) => Ok((i.res_or(*c, *c), 0)),
                        _ => Err(format!("walk: ext {nn} child unrevealed")),
                    }
                } else {
                    Ok((nn, ii + 1))
                }
            } else {
                Err(format!("walk: ext {nn} key mismatch at {ii}"))
            }
        }
        NodeRec::Branch(v, kids, _) => {
            if ii != 0 {
                Err(format!("walk: branch {nn} at {ii}"))
            } else if sym < 16 {
                match kids.get(sym) {
                    Some(Kid::Node(c)) => Ok((i.res_or(*c, *c), 0)),
                    _ => Err(format!("walk: branch {nn} slot {sym} not revealed")),
                }
            } else if sym == SYM_END && *v == Some(VSlot::Touched) {
                Ok((nn, 0))
            } else {
                Err(format!("walk: branch {nn} END"))
            }
        }
    }
}

/// A walk step: symbol index `t` (`None` for `START`), symbol, edge.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WStep {
    pub t: Option<usize>,
    pub sym: usize,
    pub edge: Edge,
    pub last: bool,
}

/// `walkOf I rc`: `START` then one step per key symbol.
pub fn walk_of(i: &Info, rc: &Receipt) -> Result<Vec<WStep>, String> {
    let r0 = i.res_or(0, 0);
    let mut out = vec![WStep { t: None, sym: SYM_START, edge: vec![0, 0, SYM_START, r0, 0], last: false }];
    let mut st = (r0, 0);
    for (t, sym) in key_syms(rc).into_iter().enumerate() {
        let st2 = step_of(i, st.0, st.1, sym)?;
        out.push(WStep { t: Some(t), sym, edge: vec![st.0, st.1, sym, st2.0, st2.1], last: sym == SYM_END });
        st = st2;
    }
    Ok(out)
}

/// `walksOf I`: all walks, receipt order (a failing walk is empty).
pub fn walks_of(i: &Info) -> Vec<Vec<WStep>> { i.e.rs.iter().map(|rc| walk_of(i, rc).unwrap_or_default()).collect() }

/// `walkErrors I` (none for honest records).
pub fn walk_errors(i: &Info) -> Vec<String> { i.e.rs.iter().filter_map(|rc| walk_of(i, rc).err()).collect() }

/// `edgeUses ws`: edge use counts.
pub fn edge_uses(ws: &[Vec<WStep>]) -> HashMap<Edge, usize> {
    let mut m = HashMap::new();
    for w in ws {
        for s in w {
            *m.entry(s.edge.clone()).or_insert(0) += 1;
        }
    }
    m
}

/// `finalOf w`: the slot a walk reaches.
pub fn final_of(w: &[WStep]) -> usize { w.last().map(|s| s.edge.get(3).copied().unwrap_or(0)).unwrap_or(0) }

/// `tprevOf e r`: `1 +` the previous receipt on `slot r`, or `0`.
pub fn tprev_of(e: &Ext, r: usize) -> usize { (0..r).filter(|&r2| e.slot(r2) == e.slot(r)).last().map(|x| x + 1).unwrap_or(0) }

/// `tlastOf e k`: `1 +` the last receipt on `k`, or `0`.
pub fn tlast_of(e: &Ext, k: usize) -> usize {
    (0..e.rs.len()).filter(|&r2| e.slot(r2) == k).last().map(|x| x + 1).unwrap_or(0)
}
