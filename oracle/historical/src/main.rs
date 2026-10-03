//! near-arena-historical: obtain AUTHENTIC mainnet trie nodes for historical
//! replay fixtures.
//!
//! Public JSON-RPC exposes account *values* at a block but never the trie
//! nodes on the path to `TrieKey::Account` (see docs/HISTORICAL_REPLAY.md).
//! The only public source of trie nodes we found is the state-sync protocol:
//! every node keeps a state snapshot for the current epoch's sync block and
//! answers `StateRequestHeader` / `StateRequestPart` from any peer. A state
//! part is a `PartialState` (raw trie nodes and values) for a contiguous key
//! range of the shard trie rooted at `B_prev.chunks[shard].prev_state_root`,
//! where `B_prev` is the block before the epoch's sync block.
//!
//! Commands (all output is raw nearcore bytes as received, plus JSON summaries):
//!   header PEER SYNC_HASH SHARD OUT          StateRequestHeader -> OUT (borsh ShardStateSyncResponseHeader)
//!   part   PEER SYNC_HASH SHARD PART OUT     StateRequestPart   -> OUT (borsh StatePart, as received)
//!   range  ROOT_HEX PART_FILE                key range fully revealed by a part (JSON)
//!   build --ctx CTX.json --parts P1,P2,... --out DIR
//!                                            run the pinned Runtime::apply on the parts' trie
//!                                            nodes (src/replay.rs); writes request.bin,
//!                                            witness.bin, expected_claim.bin, apply_witness.bin,
//!                                            diagnostics.json
//!   replay DIR...                            re-run cases from request.bin + apply_witness.bin
//!
//!   whereis ROOT_HEX HASH PART_FILE...       nibble path where a node hash is referenced
//!
//! PEER = ed25519:<pubkey>@<ip:port> (e.g. from the `network_info` RPC).

#[path = "../../src/domain.rs"]
mod domain;
#[path = "../../src/enc.rs"]
#[allow(dead_code)]
mod enc;
mod replay;

use anyhow::{Context, bail};
use borsh::BorshDeserialize;
use near_network::raw::{Connection, DirectMessage, Message};
use near_primitives::hash::{CryptoHash, hash};
use near_primitives::network::PeerId;
use near_primitives::state::PartialState;
use near_primitives::state_part::StatePart;
use near_primitives::types::ShardId;
use std::collections::HashMap;
use std::str::FromStr;

const MAINNET_GENESIS: &str = "EPnLgE7iEq9s7yTkos96M3cWymH5avBAPm3qx3NXqR8H";

fn parse_peer(s: &str) -> anyhow::Result<(PeerId, std::net::SocketAddr)> {
    let (k, a) = s.split_once('@').context("PEER must be key@addr")?;
    let pk = near_crypto_pk(k)?;
    Ok((PeerId::new(pk), a.parse()?))
}

fn near_crypto_pk(k: &str) -> anyhow::Result<near_crypto::PublicKey> {
    k.parse().map_err(|e| anyhow::anyhow!("bad key {k}: {e:?}"))
}

async fn request(peer: &str, msg: DirectMessage, head_height: u64) -> anyhow::Result<near_primitives::state_sync::ShardStateSyncResponse> {
    let (peer_id, addr) = parse_peer(peer)?;
    let clock = near_time::Clock::real();
    let mut conn = Connection::connect(
        &clock,
        addr,
        peer_id,
        None,
        "mainnet",
        CryptoHash::from_str(MAINNET_GENESIS).unwrap(),
        head_height,
        vec![ShardId::new(0)],
        Some(near_time::Duration::seconds(120)),
    )
    .await
    .map_err(|e| anyhow::anyhow!("connect: {e:?}"))?;
    eprintln!("connected to {addr}");
    conn.send_message(msg).await?;
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(180);
    loop {
        if std::time::Instant::now() > deadline {
            bail!("timeout waiting for state response");
        }
        let (m, _) = conn.recv().await.context("recv")?;
        if let Message::Direct(DirectMessage::VersionedStateResponse(r)) = m {
            return Ok(r.take_state_response());
        }
    }
}

fn head_height() -> u64 {
    std::env::var("NEAR_HEAD_HEIGHT").ok().and_then(|s| s.parse().ok()).unwrap_or(0)
}

fn load_part(path: &str) -> anyhow::Result<Vec<Vec<u8>>> {
    let bytes = std::fs::read(path)?;
    let part = StatePart::from_bytes(bytes)?;
    let PartialState::TrieValues(v) = part.to_partial_state()?;
    Ok(v.into_iter().map(|x| x.to_vec()).collect())
}

// ---- minimal RawTrieNodeWithSize decoder (raw_node.rs) for range discovery ----
enum Node {
    Leaf(Vec<u8>, CryptoHash),
    Branch(Option<CryptoHash>, Vec<(u8, CryptoHash)>),
    Ext(Vec<u8>, CryptoHash),
}

fn nibbles(enc: &[u8]) -> (Vec<u8>, bool) {
    let first = enc[0];
    let odd = first & 0x10 != 0;
    let leaf = first & 0x20 != 0;
    let mut n = vec![];
    if odd {
        n.push(first & 0x0f);
    }
    for b in &enc[1..] {
        n.push(b >> 4);
        n.push(b & 0x0f);
    }
    (n, leaf)
}

fn decode_node(b: &[u8]) -> Option<Node> {
    let mut r = b;
    let tag = u8::deserialize(&mut r).ok()?;
    let children = |r: &mut &[u8]| -> Option<Vec<(u8, CryptoHash)>> {
        let mask = u16::deserialize(r).ok()?;
        let mut v = vec![];
        for i in 0..16u8 {
            if mask & (1 << i) != 0 {
                v.push((i, CryptoHash(<[u8; 32]>::deserialize(r).ok()?)));
            }
        }
        Some(v)
    };
    let n = match tag {
        0 => {
            let k = Vec::<u8>::deserialize(&mut r).ok()?;
            let _len = u32::deserialize(&mut r).ok()?;
            let h = <[u8; 32]>::deserialize(&mut r).ok()?;
            Node::Leaf(k, CryptoHash(h))
        }
        1 => Node::Branch(None, children(&mut r)?),
        2 => {
            let _len = u32::deserialize(&mut r).ok()?;
            let h = <[u8; 32]>::deserialize(&mut r).ok()?;
            Node::Branch(Some(CryptoHash(h)), children(&mut r)?)
        }
        3 => {
            let k = Vec::<u8>::deserialize(&mut r).ok()?;
            Node::Ext(k, CryptoHash(<[u8; 32]>::deserialize(&mut r).ok()?))
        }
        _ => return None,
    };
    let _mem = u64::deserialize(&mut r).ok()?;
    if !r.is_empty() {
        return None;
    }
    Some(n)
}

fn nib_to_hex(n: &[u8]) -> String {
    n.iter().map(|x| format!("{x:x}")).collect()
}

/// DFS over the nodes present in the part; returns (min key, max key, #keys) in nibbles,
/// counting only keys whose value is carried by the part, trimmed of up to 8
/// outliers at each end (bisection hint only; never used for correctness).
fn key_range(root: CryptoHash, map: &HashMap<CryptoHash, &[u8]>) -> (Option<String>, Option<String>, usize) {
    let mut keys: Vec<Vec<u8>> = vec![];
    let mut stack = vec![(root, vec![])];
    while let Some((h, path)) = stack.pop() {
        let Some(b) = map.get(&h) else { continue };
        match decode_node(b) {
            Some(Node::Leaf(k, v)) => {
                // only keys whose value is carried by this part
                if map.contains_key(&v) {
                    let mut p = path.clone();
                    p.extend(nibbles(&k).0);
                    keys.push(p);
                }
            }
            Some(Node::Ext(k, c)) => {
                let mut p = path.clone();
                p.extend(nibbles(&k).0);
                stack.push((c, p));
            }
            Some(Node::Branch(v, ch)) => {
                if v.is_some_and(|v| map.contains_key(&v)) {
                    keys.push(path.clone());
                }
                for (i, c) in ch {
                    let mut p = path.clone();
                    p.push(i);
                    stack.push((c, p));
                }
            }
            None => {} // a value, not a node
        }
    }
    keys.sort();
    keys.dedup();
    // A few values on the paths to the part boundaries are carried by several
    // parts (e.g. the BranchWithValue at 0x07, DelayedReceiptIndices); trim them
    // so the range reflects the part's bulk.
    let t = (keys.len() / 50).min(8);
    let core = &keys[t..keys.len() - t];
    (core.first().map(|k| nib_to_hex(k)), core.last().map(|k| nib_to_hex(k)), keys.len())
}

fn main() -> anyhow::Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let rt = tokio::runtime::Runtime::new()?;
    match a.get(1).map(String::as_str) {
        Some("header") => {
            let (peer, sync, shard, out) = (&a[2], CryptoHash::from_str(&a[3]).unwrap(), a[4].parse::<u64>()?, &a[5]);
            let r = rt.block_on(request(peer, DirectMessage::StateRequestHeader(ShardId::new(shard), sync), head_height()))?;
            let hdr = r.take_header().context("peer returned no header")?;
            std::fs::write(out, borsh::to_vec(&hdr)?)?;
            let chunk = hdr.cloned_chunk();
            let root_node = hdr.state_root_node();
            println!(
                "{}",
                serde_json::json!({
                    "chunk_hash": chunk.chunk_hash().0.to_string(),
                    "chunk_height_included": hdr.chunk_height_included(),
                    "chunk_prev_state_root": hdr.chunk_prev_state_root().to_string(),
                    "state_root_node_hash": hash(&root_node.data).to_string(),
                    "state_root_memory_usage": root_node.memory_usage,
                    "num_state_parts": hdr.num_state_parts(),
                    "bytes": std::fs::metadata(out)?.len(),
                })
            );
        }
        Some("part") => {
            let (peer, sync, shard, part, out) =
                (&a[2], CryptoHash::from_str(&a[3]).unwrap(), a[4].parse::<u64>()?, a[5].parse::<u64>()?, &a[6]);
            let r = rt.block_on(request(peer, DirectMessage::StateRequestPart(ShardId::new(shard), sync, part), head_height()))?;
            let (pid, p) = r.take_part().context("peer returned no part")?;
            if pid != part {
                bail!("asked part {part}, got {pid}");
            }
            let bytes = p.to_bytes();
            std::fs::write(out, &bytes)?;
            println!("{}", serde_json::json!({"part_id": pid, "bytes": bytes.len()}));
        }
        Some("range") => {
            let root = CryptoHash::from_str(&a[2]).unwrap();
            let vals = load_part(&a[3])?;
            let map: HashMap<CryptoHash, &[u8]> = vals.iter().map(|v| (hash(v), v.as_slice())).collect();
            let (lo, hi, n) = key_range(root, &map);
            println!(
                "{}",
                serde_json::json!({"values": vals.len(), "bytes": vals.iter().map(|v| v.len()).sum::<usize>(),
                    "root_present": map.contains_key(&root), "keys": n, "first_key_nibbles": lo, "last_key_nibbles": hi})
            );
        }
        Some("build") => {
            let get = |n: &str| a.iter().position(|x| x == n).and_then(|i| a.get(i + 1)).cloned().context(n.to_string());
            let ctx: serde_json::Value = serde_json::from_slice(&std::fs::read(get("--ctx")?)?)?;
            let parts: Vec<String> = get("--parts")?.split(',').map(String::from).collect();
            let req = replay::parse_ctx(&ctx).map_err(|e| anyhow::anyhow!(e))?;
            let storage = replay::storage_from_parts(&parts).map_err(|e| anyhow::anyhow!(e))?;
            let d = replay::build(req, &storage, std::path::Path::new(&get("--out")?)).map_err(|e| anyhow::anyhow!(e))?;
            println!("{}", serde_json::to_string(&d["claim"])?);
        }
        Some("replay") => {
            let mut bad = 0;
            for d in &a[2..] {
                match replay::replay(std::path::Path::new(d)) {
                    Ok(()) => println!("REPLAY_OK {d}"),
                    Err(e) => {
                        bad += 1;
                        println!("REPLAY_MISMATCH {d}: {e}");
                    }
                }
            }
            if bad > 0 {
                std::process::exit(1);
            }
        }
        Some("whereis") => {
            // whereis ROOT HASH PART... : nibble path at which HASH is referenced
            let root = CryptoHash::from_str(&a[2]).unwrap();
            let target = CryptoHash::from_str(&a[3]).unwrap();
            let mut vals = vec![];
            for p in &a[4..] {
                vals.extend(load_part(p)?);
            }
            let map: HashMap<CryptoHash, &[u8]> = vals.iter().map(|v| (hash(v), v.as_slice())).collect();
            let mut stack = vec![(root, vec![])];
            while let Some((h, path)) = stack.pop() {
                if h == target {
                    println!("{}", serde_json::json!({"path_nibbles": nib_to_hex(&path)}));
                    return Ok(());
                }
                let Some(b) = map.get(&h) else { continue };
                match decode_node(b) {
                    Some(Node::Leaf(k, v)) if v == target => {
                        let mut p = path.clone();
                        p.extend(nibbles(&k).0);
                        println!("{}", serde_json::json!({"value_of_key_nibbles": nib_to_hex(&p)}));
                        return Ok(());
                    }
                    Some(Node::Branch(Some(v), _)) if v == target => {
                        println!("{}", serde_json::json!({"value_of_key_nibbles": nib_to_hex(&path)}));
                        return Ok(());
                    }
                    Some(Node::Ext(k, c)) => {
                        let mut p = path.clone();
                        p.extend(nibbles(&k).0);
                        stack.push((c, p));
                    }
                    Some(Node::Branch(_, ch)) => {
                        for (i, c) in ch {
                            let mut p = path.clone();
                            p.push(i);
                            stack.push((c, p));
                        }
                    }
                    _ => {}
                }
            }
            bail!("not referenced from the given parts");
        }
        _ => bail!("usage: see src/main.rs"),
    }
    Ok(())
}
