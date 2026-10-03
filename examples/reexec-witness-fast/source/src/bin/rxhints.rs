//! Test helper: print `proof-mutators` FormatHints (JSON) for a
//! `reexec-witness-v1` proof: hash stubs / value hashes as commitments, every
//! u32 length field, and every trie-node byte range. Not part of any trust path.
use reexec::spec::read_receipt;
use reexec::wire::{Reader, WResult};

#[derive(Default)]
struct H {
    commitments: Vec<(String, usize, usize)>,
    lengths: Vec<(String, usize, usize)>,
    nodes: Vec<(String, usize, usize)>,
}

fn node(r: &mut Reader<'_>, h: &mut H, path: &str) -> WResult<()> {
    let start = r.pos;
    let tag = r.u8("tag")?;
    let key = |r: &mut Reader<'_>, h: &mut H| -> WResult<()> {
        h.lengths.push((format!("{path}.keylen"), r.pos, 4));
        reexec::proof::read_key(r).map(|_| ())
    };
    match tag {
        0 => {
            h.commitments.push((format!("{path}.hash"), r.pos, 32));
            r.hash("h")?;
        }
        1 | 2 => {
            key(r, h)?;
            h.lengths.push((format!("{path}.vlen"), r.pos, 4));
            if tag == 1 {
                r.bytes("v")?;
            } else {
                r.u32("len")?;
                h.commitments.push((format!("{path}.vhash"), r.pos, 32));
                r.hash("h")?;
            }
            r.u64("mem")?;
        }
        3 => {
            key(r, h)?;
            node(r, h, &format!("{path}.e"))?;
            r.u64("mem")?;
        }
        _ => {
            if tag == 5 {
                h.lengths.push((format!("{path}.vlen"), r.pos, 4));
                r.bytes("v")?;
            } else if tag == 6 {
                r.u32("len")?;
                h.commitments.push((format!("{path}.vhash"), r.pos, 32));
                r.hash("h")?;
            }
            let bm = r.u16("bm")?;
            for i in 0..16 {
                if bm >> i & 1 == 1 {
                    node(r, h, &format!("{path}.{i:x}"))?;
                }
            }
            r.u64("mem")?;
        }
    }
    h.nodes.push((path.to_string(), start, r.pos - start));
    Ok(())
}

fn main() {
    let a = reexec::parse_args(&["proof"]);
    let p = std::fs::read(&a["proof"]).unwrap_or_else(|e| reexec::die(&format!("proof: {e}")));
    let mut r = Reader::new(&p);
    let mut h = H::default();
    (|| -> WResult<()> {
        h.lengths.push(("receipt_count".into(), 0, 4));
        let n = r.u32("n")?;
        for i in 0..n {
            h.lengths.push((format!("receipt{i}.predecessor_len"), r.pos, 4));
            let s = r.pos;
            read_receipt(&mut r)?;
            h.commitments.push((format!("receipt{i}.id"), s + 4 + 4 + p[s..s + 4].iter().rev().fold(0usize, |a, &b| a * 256 + b as usize)
                + { let o = s + 4 + u32::from_le_bytes(p[s..s + 4].try_into().unwrap()) as usize; u32::from_le_bytes(p[o..o + 4].try_into().unwrap()) as usize }, 32));
        }
        node(&mut r, &mut h, "root")
    })()
    .unwrap_or_else(|e| reexec::die(&format!("proof: {e}")));
    let reg = |v: &[(String, usize, usize)]| {
        v.iter().map(|(l, o, n)| format!("{{\"label\":\"{l}\",\"offset\":{o},\"len\":{n}}}")).collect::<Vec<_>>().join(",")
    };
    let lens = h
        .lengths
        .iter()
        .map(|(l, o, w)| format!("{{\"label\":\"{l}\",\"offset\":{o},\"width\":{w}}}"))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "{{\"commitments\":[{}],\"lengths\":[{}],\"trie_nodes\":[{}],\"transcript\":[],\"domain_tag\":null}}",
        reg(&h.commitments),
        lens,
        reg(&h.nodes)
    );
}
