//! Revealed trie records and the extracted data `Ext`
//! (`ZkFormal/Near/Spec/{Trie,Good,Prune}.lean`).

use super::reexec::sha256;
use super::spec::*;

/// `VSlot`: value slot of a revealed leaf / branch-with-value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VSlot {
    /// unrevealed (or untouched) value: `ValueRef { length, hash }`
    Ref(u128, Bytes),
    /// a touched account value
    Touched,
}

/// `Kid`: child slot of a branch / child of an extension.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kid {
    None,
    Hash(Bytes),
    Node(usize),
}

/// `NodeRec`: a revealed node (`mem` = stored `memory_usage`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NodeRec {
    Leaf(Vec<u8>, VSlot, u128),
    Ext(Vec<u8>, Kid, u128),
    Branch(Option<VSlot>, Vec<Kid>, u128),
}

impl NodeRec {
    /// `.branch none [] 0` (the `getD` default of the generators).
    pub fn dflt() -> NodeRec {
        NodeRec::Branch(None, vec![], 0)
    }
    /// `NodeRec.kids`.
    pub fn kids(&self) -> &[Kid] {
        match self {
            NodeRec::Leaf(..) => &[],
            NodeRec::Ext(_, k, _) => std::slice::from_ref(k),
            NodeRec::Branch(_, ks, _) => ks,
        }
    }
    /// `NodeRec.touched`.
    pub fn touched(&self) -> bool {
        matches!(
            self,
            NodeRec::Leaf(_, VSlot::Touched, _) | NodeRec::Branch(Some(VSlot::Touched), _, _)
        )
    }
    /// `NodeRec.key` (`[]` for a branch).
    pub fn key(&self) -> &[u8] {
        match self {
            NodeRec::Leaf(k, ..) | NodeRec::Ext(k, ..) => k,
            NodeRec::Branch(..) => &[],
        }
    }
}

/// `kidBit`.
pub fn kid_bit(k: &Kid) -> u128 {
    if matches!(k, Kid::None) { 0 } else { 1 }
}
/// `bitmapOf kids 0`.
pub fn bitmap_of(kids: &[Kid]) -> u128 {
    kids.iter().enumerate().map(|(i, k)| kid_bit(k) << i).sum()
}

/// `vrefBytes vh v`.
pub fn vref_bytes(vh: &[u8], v: &VSlot) -> Bytes {
    match v {
        VSlot::Ref(len, h) => [u32b(*len), h.clone()].concat(),
        VSlot::Touched => [u32b(72), vh.to_vec()].concat(),
    }
}
/// `kidBytes dig kid`.
pub fn kid_bytes(dig: &dyn Fn(usize) -> Bytes, k: &Kid) -> Bytes {
    match k {
        Kid::None => vec![],
        Kid::Hash(h) => h.clone(),
        Kid::Node(c) => dig(*c),
    }
}
/// `ser vh dig nr` (Spec/Trie.lean).
pub fn ser(vh: &[u8], dig: &dyn Fn(usize) -> Bytes, nr: &NodeRec) -> Bytes {
    let mut v = vec![];
    match nr {
        NodeRec::Leaf(k, s, mem) => {
            let hp = hex_prefix(k, true);
            v.push(0);
            v.extend(u32b(hp.len() as u128));
            v.extend(hp);
            v.extend(vref_bytes(vh, s));
            v.extend(u64b(*mem));
        }
        NodeRec::Ext(k, kid, mem) => {
            let hp = hex_prefix(k, false);
            v.push(3);
            v.extend(u32b(hp.len() as u128));
            v.extend(hp);
            v.extend(kid_bytes(dig, kid));
            v.extend(u64b(*mem));
        }
        NodeRec::Branch(s, kids, mem) => {
            match s {
                None => v.push(1),
                Some(s) => {
                    v.push(2);
                    v.extend(vref_bytes(vh, s));
                }
            }
            v.extend(u16b(bitmap_of(kids)));
            for k in kids {
                v.extend(kid_bytes(dig, k));
            }
            v.extend(u64b(*mem));
        }
    }
    v
}

/// `nodeSize nr`.
pub fn node_size(nr: &NodeRec) -> usize {
    ser(&zeros(32), &|_| zeros(32), nr).len() + if nr.touched() { 72 } else { 0 }
}
/// `revealedOf ns`.
pub fn revealed_of(ns: &[NodeRec]) -> usize {
    ns.iter().map(node_size).sum()
}

/// `slotOf vals n v`.
fn slot_of(vals: &dyn Fn(usize) -> Bytes, n: usize, v: &VSlot) -> Slot {
    match v {
        VSlot::Ref(len, h) => Slot::Ref(*len, h.clone()),
        VSlot::Touched => Slot::Val(vals(n)),
    }
}

/// `treeOf ns vals f n` (fuel `f`).
pub fn tree_of(ns: &[NodeRec], vals: &dyn Fn(usize) -> Bytes, f: usize, n: usize) -> PTrie {
    if f == 0 {
        return PTrie::Hash(vec![]);
    }
    let sub = |k: &Kid| -> Option<PTrie> {
        match k {
            Kid::None => None,
            Kid::Hash(h) => Some(PTrie::Hash(h.clone())),
            Kid::Node(c) => Some(tree_of(ns, vals, f - 1, *c)),
        }
    };
    match ns.get(n) {
        None => PTrie::Hash(vec![]),
        Some(NodeRec::Leaf(k, v, mem)) => PTrie::Leaf(k.clone(), slot_of(vals, n, v), *mem),
        Some(NodeRec::Ext(k, kid, mem)) => PTrie::Ext(
            k.clone(),
            Box::new(sub(kid).unwrap_or(PTrie::Hash(vec![]))),
            *mem,
        ),
        Some(NodeRec::Branch(v, kids, mem)) => PTrie::Branch(
            v.as_ref().map(|v| slot_of(vals, n, v)),
            kids.iter().map(sub).collect(),
            *mem,
        ),
    }
}

/// `trieOf ns vals`.
pub fn trie_of(ns: &[NodeRec], vals: &dyn Fn(usize) -> Bytes) -> PTrie {
    tree_of(ns, vals, ns.len(), 0)
}

// ---------------------------------------------------------------------------
// Ext (Spec/Good.lean)
// ---------------------------------------------------------------------------

/// `Ext`: data extracted from an accepted trace / built from a witness.
#[derive(Clone, Debug)]
pub struct Ext {
    /// revealed trie nodes, root = node `0`
    pub ns: Vec<NodeRec>,
    /// `vl` of the pruned trie: `vals0 k = vals0_list[k].unwrap_or([])`
    pub vals0_list: Vec<Option<Bytes>>,
    /// the receipts, in batch order
    pub rs: Vec<Receipt>,
    /// `slot r` for `r < rs.len()`
    pub slots: Vec<usize>,
    /// `slot r` for `r ≥ rs.len()` (walk of the default receipt's key)
    pub slot_default: usize,
}

/// `burnPrice bgp rc = min rc.gasPrice bgp`.
pub fn burn_price(bgp: u128, rc: &Receipt) -> u128 {
    rc.gas_price.min(bgp)
}
/// `burntOf bgp rc = G · burnPrice`.
pub fn burnt_of(bgp: u128, rc: &Receipt) -> u128 {
    params::G
        .checked_mul(burn_price(bgp, rc))
        .expect("out of domain: burnt")
}
/// `surplusOf bgp rc = G · (gasPrice − burnPrice)`.
pub fn surplus_of(bgp: u128, rc: &Receipt) -> u128 {
    params::G
        .checked_mul(rc.gas_price - burn_price(bgp, rc))
        .expect("out of domain: surplus")
}

impl Ext {
    /// `vals0 k` (`valsOfList`).
    pub fn vals0(&self, k: usize) -> Bytes {
        match self.vals0_list.get(k) {
            Some(Some(v)) => v.clone(),
            _ => vec![],
        }
    }
    /// `slot r`.
    pub fn slot(&self, r: usize) -> usize {
        self.slots.get(r).copied().unwrap_or(self.slot_default)
    }
    /// `acc0 k`: pre-state account of slot `k` (default `⟨0,0,[],0⟩`).
    pub fn acc0(&self, k: usize) -> Account {
        Account::decode(&self.vals0(k)).unwrap_or_else(Account::default0)
    }
    /// `rc r` (default when out of range).
    pub fn rc(&self, r: usize) -> Receipt {
        self.rs.get(r).cloned().unwrap_or_default()
    }
    /// `amtAt k r`: amount of slot `k` before receipt `r`.
    pub fn amt_at(&self, k: usize, r: usize) -> u128 {
        let mut a = self.acc0(k).amount;
        for r2 in 0..r {
            if self.slot(r2) == k {
                a = a
                    .checked_add(self.rc(r2).deposit)
                    .expect("out of domain: amount");
            }
        }
        a
    }
    /// `valsAt r k`: value bytes of slot `k` before receipt `r`.
    pub fn vals_at(&self, r: usize, k: usize) -> Bytes {
        Account {
            amount: self.amt_at(k, r),
            ..self.acc0(k)
        }
        .encode()
    }
    /// `tokAt c r`: `tokens_burnt` before receipt `r`.
    pub fn tok_at(&self, c: &Claim, r: usize) -> u128 {
        (0..r).fold(0u128, |a, r2| {
            a.checked_add(burnt_of(c.block_gas_price, &self.rc(r2)))
                .expect("out of domain: tokens")
        })
    }
    /// `refundOf c r`: the gas-refund receipt of receipt `r` (none if no surplus).
    pub fn refund_of(&self, c: &Claim, r: usize) -> Vec<Receipt> {
        let s = surplus_of(c.block_gas_price, &self.rc(r));
        if s == 0 {
            vec![]
        } else {
            vec![gas_refund_receipt(&self.rc(r), c.block_height as u128, s)]
        }
    }
    /// `outcomeOf c r`.
    pub fn outcome_of(&self, c: &Claim, r: usize) -> Outcome {
        let rc = self.rc(r);
        Outcome {
            id: rc.receipt_id.clone(),
            receipt_ids: self
                .refund_of(c, r)
                .into_iter()
                .map(|x| x.receipt_id)
                .collect(),
            gas_burnt: params::G,
            tokens_burnt: burnt_of(c.block_gas_price, &rc),
            executor_id: rc.receiver_id.clone(),
        }
    }
    /// `outcomes c`.
    pub fn outcomes(&self, c: &Claim) -> Vec<Outcome> {
        (0..self.rs.len()).map(|r| self.outcome_of(c, r)).collect()
    }
    /// `refunds c`.
    pub fn refunds(&self, c: &Claim) -> Vec<Receipt> {
        (0..self.rs.len())
            .flat_map(|r| self.refund_of(c, r))
            .collect()
    }
    /// `witnessOf e`'s trie: `trieOf ns vals0`.
    pub fn pre_trie(&self) -> PTrie {
        trie_of(&self.ns, &|k| self.vals0(k))
    }
}

// ---------------------------------------------------------------------------
// Prune (Spec/Prune.lean)
// ---------------------------------------------------------------------------

/// `afterExt k keys`.
fn after_ext(k: &[u8], keys: &[Vec<u8>]) -> Vec<Vec<u8>> {
    keys.iter()
        .filter(|x| is_prefix(k, x))
        .map(|x| x[k.len()..].to_vec())
        .collect()
}
/// `afterNib j keys`.
fn after_nib(j: usize, keys: &[Vec<u8>]) -> Vec<Vec<u8>> {
    keys.iter()
        .filter(|x| x.first().map(|&y| y as usize) == Some(j))
        .map(|x| x[1..].to_vec())
        .collect()
}
/// `toRef`.
fn to_ref(s: &Slot) -> Slot {
    match s {
        Slot::Val(v) => Slot::Ref(v.len() as u128, sha256(v).to_vec()),
        Slot::Ref(l, h) => Slot::Ref(*l, h.clone()),
    }
}

/// `prune keys t`.
pub fn prune(keys: &[Vec<u8>], t: &PTrie) -> PTrie {
    match t {
        PTrie::Hash(h) => PTrie::Hash(h.clone()),
        PTrie::Leaf(k, ..) => {
            if keys.iter().any(|x| x == k) {
                t.clone()
            } else {
                PTrie::Hash(t.hash_of())
            }
        }
        PTrie::Ext(k, c, mem) => {
            let ks = after_ext(k, keys);
            if ks.is_empty() {
                PTrie::Hash(t.hash_of())
            } else {
                PTrie::Ext(k.clone(), Box::new(prune(&ks, c)), *mem)
            }
        }
        PTrie::Branch(v, cs, mem) => {
            if keys.is_empty() {
                PTrie::Hash(t.hash_of())
            } else {
                let v2 = if keys.iter().any(|x| x.is_empty()) {
                    v.clone()
                } else {
                    v.as_ref().map(to_ref)
                };
                let cs2 = cs
                    .iter()
                    .enumerate()
                    .map(|(j, c)| c.as_ref().map(|c| prune(&after_nib(j, keys), c)))
                    .collect();
                PTrie::Branch(v2, cs2, *mem)
            }
        }
    }
}

/// `cnt p`: number of revealed nodes.
pub fn cnt(p: &PTrie) -> usize {
    match p {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(..) => 1,
        PTrie::Ext(_, c, _) => 1 + cnt(c),
        PTrie::Branch(_, cs, _) => 1 + cs.iter().flatten().map(cnt).sum::<usize>(),
    }
}

fn vslot(s: &Slot) -> VSlot {
    match s {
        Slot::Val(_) => VSlot::Touched,
        Slot::Ref(l, h) => VSlot::Ref(*l, h.clone()),
    }
}
fn kid_of(c: &PTrie, id: usize) -> Kid {
    match c {
        PTrie::Hash(h) => Kid::Hash(h.clone()),
        _ => Kid::Node(id),
    }
}
/// `kidsList cs id`.
fn kids_list(cs: &[Option<PTrie>], mut id: usize) -> Vec<Kid> {
    cs.iter()
        .map(|c| match c {
            None => Kid::None,
            Some(c) => {
                let k = kid_of(c, id);
                id += cnt(c);
                k
            }
        })
        .collect()
}

/// `recs p b`: preorder records of `p`, root id `b` (appended to `out`).
pub fn recs(p: &PTrie, b: usize, out: &mut Vec<NodeRec>) {
    match p {
        PTrie::Hash(_) => {}
        PTrie::Leaf(k, v, mem) => out.push(NodeRec::Leaf(k.clone(), vslot(v), *mem)),
        PTrie::Ext(k, c, mem) => {
            out.push(NodeRec::Ext(k.clone(), kid_of(c, b + 1), *mem));
            recs(c, b + 1, out);
        }
        PTrie::Branch(v, cs, mem) => {
            out.push(NodeRec::Branch(
                v.as_ref().map(vslot),
                kids_list(cs, b + 1),
                *mem,
            ));
            let mut id = b + 1;
            for c in cs.iter().flatten() {
                recs(c, id, out);
                id += cnt(c);
            }
        }
    }
}

/// `vl p`: revealed value of each node (preorder).
pub fn vl(p: &PTrie, out: &mut Vec<Option<Bytes>>) {
    match p {
        PTrie::Hash(_) => {}
        PTrie::Leaf(_, v, _) => out.push(v.get().cloned()),
        PTrie::Ext(_, c, _) => {
            out.push(None);
            vl(c, out);
        }
        PTrie::Branch(v, cs, _) => {
            out.push(v.as_ref().and_then(|s| s.get().cloned()));
            for c in cs.iter().flatten() {
                vl(c, out);
            }
        }
    }
}

/// `slotIdx p key`: relative id of the node whose value `p.get key` reads.
pub fn slot_idx(p: &PTrie, key: &[u8]) -> usize {
    match p {
        PTrie::Hash(_) | PTrie::Leaf(..) => 0,
        PTrie::Ext(k, c, _) => 1 + slot_idx(c, &key[k.len().min(key.len())..]),
        PTrie::Branch(_, cs, _) => match key.split_first() {
            None => 0,
            Some((&n, rest)) => 1 + slot_idx_kids(cs, n as usize, rest),
        },
    }
}
/// `slotIdxKids cs i key`.
fn slot_idx_kids(cs: &[Option<PTrie>], i: usize, key: &[u8]) -> usize {
    let mut acc = 0;
    for (j, c) in cs.iter().enumerate() {
        if j == i {
            return acc + c.as_ref().map(|c| slot_idx(c, key)).unwrap_or(0);
        }
        if let Some(c) = c {
            acc += cnt(c);
        }
    }
    acc // `.nil` reached: 0 added
}

/// `keysOf w`.
pub fn keys_of(w: &Witness) -> Vec<Vec<u8>> {
    w.receipts
        .iter()
        .map(|r| account_key_path(&r.receiver_id))
        .collect()
}

/// `extOf c w`: records of a witness (pruned to the touched paths).
pub fn ext_of(_c: &Claim, w: &Witness) -> Ext {
    let p = prune(&keys_of(w), &w.trie);
    let mut ns = vec![];
    recs(&p, 0, &mut ns);
    let mut vals0_list = vec![];
    vl(&p, &mut vals0_list);
    let slots = w
        .receipts
        .iter()
        .map(|r| slot_idx(&p, &account_key_path(&r.receiver_id)))
        .collect();
    let slot_default = slot_idx(&p, &account_key_path(&[]));
    Ext {
        ns,
        vals0_list,
        rs: w.receipts.clone(),
        slots,
        slot_default,
    }
}
