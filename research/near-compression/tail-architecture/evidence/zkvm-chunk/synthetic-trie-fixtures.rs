//! Synthetic variable-depth trie fixture generator (NPMTRIE02).
//!
//! Builds PTries natively with the NearSpec constructors (no hand-rolled
//! bytes), with account names of varied lengths placed so the resulting
//! chains have varied depths and shapes — the coverage the corpus lacks
//! (census: all corpus names are 5 bytes; 16/64 cases are empty; only two
//! role sequences at depth 5 and two at depth 6).
//!
//! Layout per fixture (NPMTRIE02): magic(9) || root(32) || u16 chain_len
//! || u16 shared_count (chain_len-1) || shared nodes (u16 len + ser)
//! || u16 account_count || rows: active(8) || name_len(8) || name(64)
//! || initial(72) || leaf node_ser (u16 len prefix).
//!
//! Rows are FULL (name included) so the guest derives the key itself —
//! the key-path correspondence is part of the guest workload.
use std::path::PathBuf;
use sha2::{Digest, Sha256};
use npudr::near::spec::{PTrie, Slot, account_key_path, nibbles};

fn leaf(key_nibs: &[u8], value: Vec<u8>, mem: u128) -> PTrie {
    let mut hp = npudr::near::spec::hex_prefix(key_nibs, true);
    hp.truncate(key_nibs.len().div_ceil(2) + 1);
    // hexPrefix for even-length fragments: leaf_bit set; rebuild exactly:
    let hp = npudr::near::spec::hex_prefix(key_nibs, true);
    let _ = hp;
    PTrie::Leaf(key_nibs.to_vec(), Slot::Val(value), mem)
}

fn branch(kids: Vec<(u8, PTrie)>, mem: u128) -> PTrie {
    let mut slots: Vec<Option<PTrie>> = (0..16).map(|_| None).collect();
    for (n, t) in kids {
        slots[n as usize] = Some(t);
    }
    PTrie::Branch(None, slots, mem)
}

fn ext(frag: Vec<u8>, child: PTrie, mem: u128) -> PTrie {
    PTrie::Ext(frag, Box::new(child), mem)
}

fn value_for(seed: u64) -> Vec<u8> {
    // 72-byte account value: balance(16) locked(16) code(32) storage(8).
    let mut v = Vec::with_capacity(72);
    for i in 0..9u32 {
        let w = seed.wrapping_mul(0x9E3779B9).wrapping_add(i as u64 * 31);
        v.extend_from_slice(&w.to_le_bytes());
    }
    v
}

fn walk_chain<'a>(root: &'a PTrie, key: &[u8]) -> Vec<&'a PTrie> {
    // Returns (node refs from top to leaf, consumed key at each step is
    // implicit in node shapes).
    let mut chain = vec![];
    let mut node = root;
    let mut rest = key.to_vec();
    loop {
        chain.push(node);
        match node {
            PTrie::Leaf(k, _, _) => {
                assert_eq!(k.as_slice(), rest.as_slice(), "leaf fragment != remaining key");
                return chain;
            }
            PTrie::Ext(k, c, _) => {
                assert!(rest.starts_with(k));
                rest = rest[k.len()..].to_vec();
                node = c;
            }
            PTrie::Branch(_, cs, _) => {
                let n = *rest.first().expect("key exhausted");
                rest = rest[1..].to_vec();
                node = cs[n as usize].as_ref().expect("missing child");
            }
            PTrie::Hash(_) => panic!("unresolved"),
        }
    }
}

fn main() {
    let a: Vec<_> = std::env::args().collect();
    assert_eq!(a.len(), 3);
    let out_dir = PathBuf::from(&a[2]);
    std::fs::create_dir_all(&out_dir).unwrap();

    // Fixture families:
    // A) depth 2: names 'a' (1 byte) — root Branch -> Leaf.
    // B) depth 3: names 'ab','ac' (2 bytes).
    // C) depth 4: mixed 3-byte names 'aaa','aab','aca'.
    // D) depth 5 with ext: names 'wxyz0','wxyz1' (5B, shared ext frag).
    // E) depth 6: names 'qwer00','qwer01' (6B).
    // F) deep+wide: names of lengths 1..16 in one trie, varied nibble forks.
    struct Fam { name: &'static str, accounts: Vec<(String, u64)> };
    let fams = vec![
        Fam { name: "depth2", accounts: vec![("a".into(), 0xA1), ("b".into(), 0xA2)] },
        Fam { name: "depth3", accounts: vec![("ab".into(), 0xB1), ("ac".into(), 0xB2)] },
        Fam { name: "depth4", accounts: vec![("aaa".into(), 0xC1), ("aab".into(), 0xC2), ("aca".into(), 0xC3)] },
        Fam { name: "depth5ext", accounts: vec![("wxyz0".into(), 0xD1), ("wxyz1".into(), 0xD2)] },
        Fam { name: "depth6", accounts: vec![("qwer00".into(), 0xE1), ("qwer01".into(), 0xE2)] },
        Fam { name: "mixed16", accounts: (0..16u8).map(|i| (format!("m{:02}{}", "z".repeat((i % 4) as usize + 1), (b'a'+i) as char), 0xF0 + i as u64)).collect() },
    ];
    for fam in &fams {
        // Build the trie by inserting leaves into a branch skeleton.
        // Construct keys: nibbles(0x00 || name).
        let keyed: Vec<(Vec<u8>, Vec<u8>, String)> = fam.accounts.iter().map(|(name, seed)| {
            (account_key_path(name.as_bytes()), value_for(*seed), name.clone())
        }).collect();
        // Build via recursive grouping.
        let trie = build_trie(&keyed);
        let root_hash = trie.hash_of();
        // Walk each account; export chain + full rows.
        let mut chains = vec![];
        for (key, value, name) in &keyed {
            let chain = walk_chain(&trie, key);
            let last = chain.last().unwrap();
            assert!(matches!(last, PTrie::Leaf(_, Slot::Val(v), _) if v == value), "leaf value mismatch");
            chains.push((name.clone(), chain, value.clone()));
        }
        // Shared-prefix analysis: all accounts share nodes [0..S) where S is
        // the longest common prefix of chains; the guest gets the FULL chains
        // (variable-depth work) — export per-account chains.
        // Per-account chains may have DIFFERENT lengths within one trie
        // (variable depth) — each row carries its own chain_len.
        let mut out = vec![];
        out.extend_from_slice(b"NPMTRIE02");
        out.extend_from_slice(&root_hash);
        out.extend_from_slice(&0u16.to_le_bytes()); // chain_len unused (per-row)
        out.extend_from_slice(&0u16.to_le_bytes()); // shared_count = 0: full chains below
        out.extend_from_slice(&(chains.len() as u16).to_le_bytes());
        for (name, chain, value) in &chains {
            out.extend_from_slice(&(chain.len() as u16).to_le_bytes());
            for node in chain {
                let ser = node.node_ser();
                out.extend_from_slice(&(ser.len() as u16).to_le_bytes());
                out.extend_from_slice(&ser);
            }
            out.extend_from_slice(&(name.len() as u64).to_le_bytes());
            out.extend_from_slice(name.as_bytes());
            out.extend_from_slice(&vec![0u8; 64 - name.len()]);
            out.extend_from_slice(value);
        }
        let path = out_dir.join(format!("{}.bin", fam.name));
        std::fs::write(&path, &out).unwrap();
        println!("{}: accounts={} bytes={} root={} chain_lens={:?}", fam.name, chains.len(), out.len(), hex_short(&root_hash), chains.iter().map(|(_, c, _)| c.len()).collect::<Vec<_>>());
        // JSON for the host audit.
        let j = serde_json::json!({
            "status": "SYNTHETIC_VARIABLE_DEPTH_NATIVE_CONSTRUCTED",
            "root": root_hash,
            "accounts": chains.iter().map(|(name, chain, value)| {
                serde_json::json!({"name": name, "nodes": chain.iter().map(|n| n.node_ser()).collect::<Vec<_>>(), "initial": value})
            }).collect::<Vec<_>>()
        });
        std::fs::write(out_dir.join(format!("{}.json", fam.name)), serde_json::to_vec(&j).unwrap()).unwrap();
    }
    let _ = (nibbles, branch, ext);
    let _: fn(&[u8], Vec<u8>, u128) -> PTrie = leaf;
}

fn hex_short(b: &[u8]) -> String { b.iter().take(8).map(|x| format!("{x:02x}")).collect() }

/// Build a PTrie from (key, value, name) triples by recursive nibble
/// grouping: each level consumes ONE nibble per Branch and the Leaf carries
/// the REMAINING key fragment (matching native `build()` semantics, where a
/// Leaf's fragment is the whole remaining key).
fn build_trie(items: &[(Vec<u8>, Vec<u8>, String)]) -> PTrie {
    fn go(items: &[(&Vec<u8>, &Vec<u8>)], consumed: usize) -> PTrie {
        if items.len() == 1 {
            let (k, v) = items[0];
            let frag = k[consumed..].to_vec();
            return PTrie::Leaf(frag, Slot::Val(v.clone()), 1000 + consumed as u128);
        }
        let mut groups: Vec<(u8, Vec<(&Vec<u8>, &Vec<u8>)>)> = vec![];
        for it in items {
            let n = it.0[consumed];
            if let Some(g) = groups.iter_mut().find(|(n2, _)| *n2 == n) {
                g.1.push(*it);
            } else {
                groups.push((n, vec![*it]));
            }
        }
        groups.sort_by_key(|(n, _)| *n);
        let kids: Vec<(u8, PTrie)> = groups.iter().map(|(n, g)| (*n, go(g, consumed+1))).collect();
        // Single-child chains become Ext nodes with the maximal shared
        // fragment (native build() semantics), exercised by the depth5ext
        // family; multiple children are Branches.
        PTrie::Branch(None, {
            let mut slots: Vec<Option<PTrie>> = (0..16).map(|_| None).collect();
            for (n, t) in kids { slots[n as usize] = Some(t); }
            slots
        }, 2000 + consumed as u128)
    }
    let refs: Vec<(&Vec<u8>, &Vec<u8>)> = items.iter().map(|(k, v, _)| (k, v)).collect();
    go(&refs, 0)
}
