//! Partial NEAR state trie (`NearSpec.PTrie`) in an index arena.
//!
//! Built from nearcore's `PartialState` values exactly like
//! `NearSpec.Codec.build`: the nodes on the paths to the requested keys are
//! revealed, everything else is a `Hash` stub. Revealed nodes are parsed
//! strictly and must be in canonical form (re-serializing the parsed node
//! gives the original bytes), so `sha256(raw node)` equals `PTrie.hashOf` of
//! the revealed node and the pre-state root needs no re-hashing.

use crate::sha256;
use crate::wire::{Reader, WireError, Writer};
use sha2::{Digest, Sha256};
use std::collections::HashMap;

pub const NONE: u32 = u32::MAX;

#[derive(Clone, Debug)]
pub enum Slot<'a> {
    /// Revealed value: original bytes and (after an update) the current value.
    Val { orig: &'a [u8], cur: Option<Box<[u8]>> },
    /// Unrevealed `ValueRef`.
    Ref { len: u32, hash: [u8; 32] },
}

impl Slot<'_> {
    pub fn current(&self) -> Option<&[u8]> {
        match self {
            Slot::Val { orig, cur } => Some(cur.as_deref().unwrap_or(orig)),
            Slot::Ref { .. } => None,
        }
    }
    fn value_ref(&self, w: &mut Writer) {
        match self {
            Slot::Val { .. } => {
                let v = self.current().unwrap();
                w.u32(v.len() as u32).raw(&sha256(v));
            }
            Slot::Ref { len, hash } => {
                w.u32(*len).raw(hash);
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Kind<'a> {
    Hash,
    Leaf { key: Vec<u8>, slot: Slot<'a> },
    Ext { key: Vec<u8>, child: u32 },
    Branch { value: Option<Slot<'a>>, kids: [u32; 16] },
}

#[derive(Clone, Debug)]
pub struct Node<'a> {
    pub kind: Kind<'a>,
    pub mem: u64,
    /// Node hash (pre-state; recomputed lazily when `dirty`).
    pub hash: [u8; 32],
    pub dirty: bool,
}

pub struct PTrie<'a> {
    pub nodes: Vec<Node<'a>>,
    pub root: u32,
}

/// Bytes → nibbles (high first).
pub fn nibbles_of(prefix: u8, b: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(2 + 2 * b.len());
    v.push(prefix >> 4);
    v.push(prefix & 15);
    for &x in b {
        v.push(x >> 4);
        v.push(x & 15);
    }
    v
}

/// `NibbleSlice::encode_nibbles` (`NearSpec.hexPrefix`).
pub fn hex_prefix(nibs: &[u8], leaf: bool, w: &mut Writer) {
    let flag = if leaf { 32u8 } else { 0 };
    let hp_len = 1 + nibs.len() / 2;
    w.u32(hp_len as u32);
    let rest = if nibs.len() % 2 == 1 {
        w.u8(16 + nibs[0] + flag);
        &nibs[1..]
    } else {
        w.u8(flag);
        nibs
    };
    for p in rest.chunks_exact(2) {
        w.u8(p[0] * 16 + p[1]);
    }
}

fn hp_decode(b: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(2 * b.len());
    if let Some((&f, rest)) = b.split_first() {
        if (f >> 4) % 2 == 1 {
            v.push(f & 15);
        }
        for &x in rest {
            v.push(x >> 4);
            v.push(x & 15);
        }
    }
    v
}

fn hp_canonical(raw: &[u8], nibs: &[u8], leaf: bool) -> bool {
    let mut w = Writer::with_capacity(4 + raw.len());
    hex_prefix(nibs, leaf, &mut w);
    w.0.len() == raw.len() + 4 && &w.0[4..] == raw
}

/// Parsed raw node (`RawTrieNodeWithSize`).
enum Raw<'a> {
    Leaf { key: Vec<u8>, vlen: u32, vh: [u8; 32] },
    Ext { key: Vec<u8>, child: [u8; 32] },
    Branch { value: Option<(u32, [u8; 32])>, kids: [Option<[u8; 32]>; 16], _p: std::marker::PhantomData<&'a ()> },
}

fn parse_node(b: &[u8]) -> Result<(Raw<'_>, u64), WireError> {
    let mut r = Reader::new(b);
    let tag = r.u8("node tag")?;
    let raw = match tag {
        0 | 3 => {
            let hp = r.bytes("node key")?;
            if hp.is_empty() {
                return Err(WireError("empty node key"));
            }
            let key = hp_decode(hp);
            if !hp_canonical(hp, &key, tag == 0) {
                return Err(WireError("non-canonical node key"));
            }
            if tag == 0 {
                let vlen = r.u32("value len")?;
                let vh = r.hash("value hash")?;
                Raw::Leaf { key, vlen, vh }
            } else {
                Raw::Ext { key, child: r.hash("child")? }
            }
        }
        1 | 2 => {
            let value = if tag == 2 { Some((r.u32("value len")?, r.hash("value hash")?)) } else { None };
            let bm = r.u16("bitmap")?;
            let mut kids = [None; 16];
            for (i, k) in kids.iter_mut().enumerate() {
                if bm >> i & 1 == 1 {
                    *k = Some(r.hash("child")?);
                }
            }
            Raw::Branch { value, kids, _p: std::marker::PhantomData }
        }
        _ => return Err(WireError("unknown node tag")),
    };
    let mem = r.u64("memory usage")?;
    r.finish()?;
    Ok((raw, mem))
}

pub type Store<'a> = HashMap<[u8; 32], &'a [u8]>;

impl<'a> PTrie<'a> {
    /// `NearSpec.Codec.build`: reveal the paths to `keys` (nibble paths).
    pub fn build(store: &Store<'a>, root: [u8; 32], keys: &[&[u8]]) -> Result<PTrie<'a>, String> {
        let mut t = PTrie { nodes: Vec::new(), root: 0 };
        t.root = t.build_at(store, root, keys)?;
        Ok(t)
    }

    fn push(&mut self, n: Node<'a>) -> u32 {
        self.nodes.push(n);
        (self.nodes.len() - 1) as u32
    }

    fn stub(&mut self, h: [u8; 32]) -> u32 {
        self.push(Node { kind: Kind::Hash, mem: 0, hash: h, dirty: false })
    }

    fn mk_slot(store: &Store<'a>, len: u32, vh: [u8; 32], want: bool) -> Slot<'a> {
        if want {
            if let Some(v) = store.get(&vh) {
                if v.len() == len as usize {
                    return Slot::Val { orig: v, cur: None };
                }
            }
        }
        Slot::Ref { len, hash: vh }
    }

    fn build_at(&mut self, store: &Store<'a>, h: [u8; 32], keys: &[&[u8]]) -> Result<u32, String> {
        if keys.is_empty() {
            return Ok(self.stub(h));
        }
        let Some(raw) = store.get(&h) else { return Ok(self.stub(h)) };
        let (node, mem) = parse_node(raw).map_err(|e| format!("witness trie node: {e}"))?;
        let kind = match node {
            Raw::Leaf { key, vlen, vh } => {
                let want = keys.iter().any(|k| *k == key.as_slice());
                Kind::Leaf { slot: Self::mk_slot(store, vlen, vh, want), key }
            }
            Raw::Ext { key, child } => {
                let sub: Vec<&[u8]> =
                    keys.iter().filter(|k| k.starts_with(&key)).map(|k| &k[key.len()..]).collect();
                let c = self.build_at(store, child, &sub)?;
                Kind::Ext { key, child: c }
            }
            Raw::Branch { value, kids, .. } => {
                let value = value.map(|(len, vh)| Self::mk_slot(store, len, vh, keys.iter().any(|k| k.is_empty())));
                let mut out = [NONE; 16];
                for (i, kh) in kids.iter().enumerate() {
                    if let Some(kh) = kh {
                        let sub: Vec<&[u8]> = keys
                            .iter()
                            .filter(|k| k.first() == Some(&(i as u8)))
                            .map(|k| &k[1..])
                            .collect();
                        out[i] = self.build_at(store, *kh, &sub)?;
                    }
                }
                Kind::Branch { value, kids: out }
            }
        };
        Ok(self.push(Node { kind, mem, hash: h, dirty: false }))
    }

    /// Locate the node owning the value slot at `key` (`PTrie.get`/`set`
    /// path). Returns the node index; `path` receives every node visited.
    pub fn locate(&self, key: &[u8], path: &mut Vec<u32>) -> Option<u32> {
        let mut i = self.root;
        let mut key = key;
        loop {
            path.push(i);
            let n = &self.nodes[i as usize];
            match &n.kind {
                Kind::Hash => return None,
                Kind::Leaf { key: k, slot } => {
                    return (k.as_slice() == key && matches!(slot, Slot::Val { .. })).then_some(i);
                }
                Kind::Ext { key: k, child } => {
                    if !key.starts_with(k) {
                        return None;
                    }
                    key = &key[k.len()..];
                    i = *child;
                }
                Kind::Branch { value, kids } => match key.split_first() {
                    None => return matches!(value, Some(Slot::Val { .. })).then_some(i),
                    Some((&n0, rest)) => {
                        let c = kids[n0 as usize];
                        if c == NONE {
                            return None;
                        }
                        key = rest;
                        i = c;
                    }
                },
            }
        }
    }

    pub fn slot_mut(&mut self, i: u32) -> &mut Slot<'a> {
        match &mut self.nodes[i as usize].kind {
            Kind::Leaf { slot, .. } => slot,
            Kind::Branch { value: Some(s), .. } => s,
            _ => unreachable!("locate returns value owners only"),
        }
    }

    pub fn slot(&self, i: u32) -> &Slot<'a> {
        match &self.nodes[i as usize].kind {
            Kind::Leaf { slot, .. } => slot,
            Kind::Branch { value: Some(s), .. } => s,
            _ => unreachable!("locate returns value owners only"),
        }
    }

    /// Current root hash (`PTrie.hashOf` of the updated trie).
    pub fn root_hash(&mut self) -> [u8; 32] {
        self.hash_of(self.root)
    }

    fn hash_of(&mut self, i: u32) -> [u8; 32] {
        if !self.nodes[i as usize].dirty {
            return self.nodes[i as usize].hash;
        }
        let mut w = Writer::with_capacity(600);
        // children first (immutable borrow of kind is cloned cheaply via indices)
        match &self.nodes[i as usize].kind {
            Kind::Hash => {}
            Kind::Leaf { .. } => {}
            Kind::Ext { child, .. } => {
                let c = *child;
                self.hash_of(c);
            }
            Kind::Branch { kids, .. } => {
                let kids = *kids;
                for c in kids {
                    if c != NONE {
                        self.hash_of(c);
                    }
                }
            }
        }
        let n = &self.nodes[i as usize];
        match &n.kind {
            Kind::Hash => unreachable!(),
            Kind::Leaf { key, slot } => {
                w.u8(0);
                hex_prefix(key, true, &mut w);
                slot.value_ref(&mut w);
            }
            Kind::Ext { key, child } => {
                w.u8(3);
                hex_prefix(key, false, &mut w);
                w.raw(&self.nodes[*child as usize].hash);
            }
            Kind::Branch { value, kids } => {
                match value {
                    None => {
                        w.u8(1);
                    }
                    Some(s) => {
                        w.u8(2);
                        s.value_ref(&mut w);
                    }
                }
                let mut bm = 0u16;
                for (j, &c) in kids.iter().enumerate() {
                    if c != NONE {
                        bm |= 1 << j;
                    }
                }
                w.u16(bm);
                for &c in kids {
                    if c != NONE {
                        w.raw(&self.nodes[c as usize].hash);
                    }
                }
            }
        }
        w.u64(n.mem);
        let h: [u8; 32] = Sha256::digest(&w.0).into();
        let n = &mut self.nodes[i as usize];
        n.hash = h;
        n.dirty = false;
        h
    }

    /// `PTrie.revealedBytes` of the (pre-state) trie.
    pub fn revealed_bytes(&self) -> u64 {
        self.revealed_at(self.root)
    }

    fn revealed_at(&self, i: u32) -> u64 {
        let hp = |k: &Vec<u8>| 1 + (k.len() / 2) as u64;
        match &self.nodes[i as usize].kind {
            Kind::Hash => 0,
            Kind::Leaf { key, slot } => {
                1 + 4 + hp(key) + 36 + 8 + if let Slot::Val { orig, .. } = slot { orig.len() as u64 } else { 0 }
            }
            Kind::Ext { key, child } => 1 + 4 + hp(key) + 32 + 8 + self.revealed_at(*child),
            Kind::Branch { value, kids } => {
                let v = match value {
                    Some(Slot::Val { orig, .. }) => 1 + 36 + orig.len() as u64,
                    Some(Slot::Ref { .. }) => 1 + 36,
                    None => 1,
                };
                let mut s = v + 2 + 8;
                for &c in kids {
                    if c != NONE {
                        s += 32 + self.revealed_at(c);
                    }
                }
                s
            }
        }
    }
}
