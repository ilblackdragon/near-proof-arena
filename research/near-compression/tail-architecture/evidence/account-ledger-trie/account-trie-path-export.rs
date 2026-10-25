//! Fixed-format binary account-table witness fixture (NPMTRIE01).
//!
//! Layout (all little-endian):
//!   magic(9) "NPMTRIE01" || root(32) || u16 chain_len(=6)
//!   || shared[chain_len-1] nodes:
//!        u16 node_len || tag(1) || u16 fragment_len || fragment(frag bytes)
//!        || u16 kids_bitmap || child_count(kids_count) * hash(32)
//!        || u64 mem
//!   || 16 rows: active(8) || leaf_len(8) || leaf_tag(8) || leaf_frag(2)
//!        || leaf_value_ref(4+32) || leaf_mem(8) || code_hash(32)
//!
//! The shared prefix (chain nodes 0..chain_len-2) is byte-identical for all
//! accounts in a case (verified corpus census; asserted at export time). The
//! leaf attaches to the last shared node by the account's final key nibble.
//! code_hash carries initial[32:64], which the 18-word table row lacks; it is
//! authenticated by the trie leaf's value_ref = u32le(72) || sha256(initial
//! 72 bytes). Trusted-local export; verification happens in-circuit and in
//! the independent Python audit.
use std::path::PathBuf;
use sha2::{Digest, Sha256};
use npudr::{v3::{d0::walk_d0, hint::decode_w, rcptfam::native}, near::spec::{account_key_path, PTrie}};

fn main(){
    let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),3);let case=PathBuf::from(&a[1]);
    let cb=std::fs::read(case.join("claim.bin")).unwrap();let wb=std::fs::read(case.join("witness.bin")).unwrap();
    let walk=walk_d0(&cb).unwrap();let n=native(&cb,&wb).unwrap();
    let mut seen=std::collections::BTreeSet::new();let mut accounts=vec![];
    for r in n.rs(){if seen.insert(r.receiver_id.clone()){accounts.push(r.receiver_id.clone());}}
    assert!(accounts.len()<=16,"account table overflow");
    // Walk each account's path; collect chains and validate shape.
    let mut chains=vec![];
    for id in &accounts{
        let key=account_key_path(id);
        let mut chain=vec![];
        let mut node=n.pre.clone();
        let mut rest:Vec<u8>=key.iter().copied().collect();
        loop{
            match &node{
                PTrie::Hash(_)=>panic!("unresolved trie node"),
                PTrie::Leaf(_,_,_)=>{
                    // The witness fixture stores the leaf's OWN bytes.
                    chain.push(rest_of_leaf(&node));
                    break;
                },
                PTrie::Ext(_,_,_)=>{chain.push(node.node_ser());rest=rest[fragment_len(&node)..].to_vec();node=child_of(&node);},
                PTrie::Branch(_,_,_)=>{
                    let c=*rest.first().expect("key exhausted before value");
                    chain.push(node.node_ser());
                    rest=rest[1..].to_vec();
                    node=child_of_nibble(&node,c).expect("missing branch child");
                },
            }
        }
        chains.push((id.clone(),chain));
    }
    // Shared-prefix assertion: all chains agree on nodes 0..len-1.
    let chain_len=if chains.is_empty(){6}else{chains[0].1.len()};
    if !chains.is_empty(){
        assert!(chains.iter().all(|(id,c)|c.len()==chain_len),"chain length differs ({:?})",chains.iter().map(|(i,c)|(i.clone(),c.len())).collect::<Vec<_>>());
        for i in 0..chain_len-1{
            let first=chains[0].1[i].clone();
            assert!(chains.iter().all(|(_,c)|c[i]==first),"shared node {i} differs");
        }
    }
    // Serialize.
    let mut out=vec![];
    out.extend_from_slice(b"NPMTRIE01");
    out.extend_from_slice(&walk.slot_b2.prev_state_root);
    out.extend_from_slice(&(chain_len as u16).to_le_bytes());
    if chains.is_empty(){
        // Empty table: zeroed shared chain; the circuit gates all trie
        // constraints on the has-accounts bit (root host-checked only).
        for _ in 0..chain_len-1{
            out.extend_from_slice(&0u16.to_le_bytes());
        }
        out.extend_from_slice(&0u16.to_le_bytes()); // account_count = 0
        std::fs::write(&a[2],&out).unwrap();
        let v=serde_json::json!({"status":"IN_CIRCUIT_TRIE_WITNESS_EXPORT","pre_state_root":walk.slot_b2.prev_state_root,"chain_len":chain_len,"shared":[],"accounts":[]});
        std::fs::write(format!("{}.json",a[2]),serde_json::to_vec(&v).unwrap()).unwrap();
        return;
    }
    // Shared nodes 0..chain_len-2 (the branch the leaves attach to is the
    // LAST shared node, index chain_len-2; per-key nibble selects the leaf).
    for ser in &chains[0].1[..chain_len-1]{
        out.extend_from_slice(&(ser.len() as u16).to_le_bytes());
        out.extend_from_slice(ser);
    }
    out.extend_from_slice(&(accounts.len() as u16).to_le_bytes());
    for (id,chain) in &chains{
        let key=account_key_path(id);
        let leaf=&chain[chain_len-1];
        assert_eq!(leaf[0],0u8,"leaf tag");
        // Leaf node_ser: 0 || u32le(hp_len) || hp || value_ref(4+32) || u64le(mem).
        let hplen=u32::from_le_bytes(leaf[1..5].try_into().unwrap()) as usize;
        let hp=&leaf[5..5+hplen];
        let value_ref=&leaf[5+hplen..5+hplen+36];
        assert_eq!(value_ref[..4],72u32.to_le_bytes(),"leaf value length");
        let _=hp;
        // Account initial value: native pre trie get.
        let initial=npudr::v3::hint::get(&n.pre,&account_key_path(id)).expect("initial value");
        assert_eq!(initial.len(),72);
        // The leaf's value_ref hash must be sha256 of this initial value.
        assert_eq!(&value_ref[4..],Sha256::digest(&initial).as_slice(),"leaf value hash");
        let _=key;
        out.extend_from_slice(&1u64.to_le_bytes());       // active
        out.extend_from_slice(&initial);                  // 72B account value
        out.extend_from_slice(leaf);                      // leaf node_ser
    }
    std::fs::write(&a[2],&out).unwrap();
    // JSON for the Python audit (unchanged semantics).
    let v=serde_json::json!({
        "status":"IN_CIRCUIT_TRIE_WITNESS_EXPORT",
        "pre_state_root":walk.slot_b2.prev_state_root,
        "chain_len":chain_len,
        "shared":chains[0].1[..chain_len-1].iter().map(|s|s.to_vec()).collect::<Vec<_>>(),
        "accounts":chains.iter().map(|(id,chain)|{
            serde_json::json!({"receiver":id,"leaf":chain[chain_len-1]})
        }).collect::<Vec<_>>()
    });
    std::fs::write(format!("{}.json",a[2]),serde_json::to_vec(&v).unwrap()).unwrap();
}

// --- helpers ---------------------------------------------------------------
fn fragment_len(t:&PTrie)->usize{
    match t{PTrie::Ext(k,_,_)=>k.len(),PTrie::Leaf(k,_,_)=>k.len(),_=>0}
}
fn child_of(t:&PTrie)->PTrie{
    match t{PTrie::Ext(_,c,_)=>(**c).clone(),_=>panic!("child_of on non-ext")}
}
fn child_of_nibble(t:&PTrie,nib:u8)->Option<PTrie>{
    match t{PTrie::Branch(_,cs,_)=>cs[nib as usize].as_ref().cloned(),_=>panic!("child_of_nibble on non-branch")}
}
fn rest_of_leaf(t:&PTrie)->Vec<u8>{
    match t{PTrie::Leaf(k,s,m)=>{
        let mut v=vec![0u8];
        let mut ser=t.node_ser().clone();
        let _=(k,s,m);
        ser.drain(..0);
        ser
    },_=>panic!("rest_of_leaf on non-leaf")}
}
