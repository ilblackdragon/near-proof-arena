//! No panics on any input: random mutations of the public fixtures'
//! `request.bin` / `witness.bin` and structured out-of-range values must make
//! `npudr::near::prepare` return `Err` (or a valid result), never panic or
//! overflow the stack; the judge `prove` binary must then exit 2 and write
//! nothing.
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use npudr::near::reexec::spec as rx;
use npudr::near::{self, genmax, spec};

fn cases() -> Vec<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../oracle/fixtures/public/cases");
    let mut v: Vec<_> = std::fs::read_dir(d).unwrap().map(|e| e.unwrap().path()).collect();
    v.sort();
    v
}

fn read(d: &Path, f: &str) -> Vec<u8> { std::fs::read(d.join(f)).unwrap() }

/// `prepare_unguarded` on a big-stack thread; `Err(panic message)` if it panicked.
fn run(req: Vec<u8>, wit: Vec<u8>) -> Result<Result<Vec<u8>, String>, String> {
    let h = std::thread::Builder::new()
        .stack_size(near::BIG_STACK)
        .spawn(move || near::prepare_unguarded(&req, &wit).map(|(c, _, _)| c))
        .unwrap();
    h.join().map_err(|p| {
        p.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| p.downcast_ref::<String>().cloned()).unwrap_or_default()
    })
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize { (self.next() % n.max(1) as u64) as usize }
}

fn mutate(rng: &mut Rng, b: &[u8]) -> Vec<u8> {
    let mut m = b.to_vec();
    let k = 1 + rng.below(3);
    for _ in 0..k {
        let p = rng.below(m.len());
        match rng.below(8) {
            0 => m[p] ^= 1 << rng.below(8),
            1 => m[p] = 0,
            2 => m[p] = 0xff,
            3 => m[p] = rng.next() as u8,
            4 => m.truncate(p),
            5 => m.insert(p, rng.next() as u8),
            6 => {
                // overwrite a little-endian u32/u128-sized window with extremes
                let w = [4usize, 8, 16][rng.below(3)];
                let v = if rng.below(2) == 0 { 0xff } else { 0x00 };
                for x in m.iter_mut().skip(p).take(w) {
                    *x = v;
                }
            }
            _ => {
                let q = rng.below(m.len());
                let (a, c) = (p.min(q), p.max(q));
                let chunk = m[a..c.min(a + 64)].to_vec();
                m.splice(p..p, chunk);
            }
        }
        if m.is_empty() {
            break;
        }
    }
    m
}

#[test]
fn fixture_mutations_never_panic() {
    let iters: usize = std::env::var("NPUDR_FUZZ_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(60);
    let mut rng = Rng(0x243f_6a88_85a3_08d3);
    let (mut ok, mut err) = (0usize, 0usize);
    for d in cases() {
        let (req, wit) = (read(&d, "request.bin"), read(&d, "witness.bin"));
        for it in 0..iters {
            let (r2, w2) = match it % 3 {
                0 => (mutate(&mut rng, &req), wit.clone()),
                1 => (req.clone(), mutate(&mut rng, &wit)),
                _ => (mutate(&mut rng, &req), mutate(&mut rng, &wit)),
            };
            match run(r2.clone(), w2.clone()) {
                Ok(Ok(c)) => {
                    // accepted: must be exactly the reexec engine's claim
                    assert_eq!(c, near::reexec::engine::derive_claim(&r2, &w2).unwrap().encode());
                    ok += 1
                }
                Ok(Err(_)) => err += 1,
                Err(p) => {
                    let f = std::env::temp_dir().join("npudr-fuzz-panic");
                    std::fs::create_dir_all(&f).unwrap();
                    std::fs::write(f.join("request.bin"), &r2).unwrap();
                    std::fs::write(f.join("witness.bin"), &w2).unwrap();
                    panic!("{d:?} mutation {it}: prepare panicked: {p} (inputs in {f:?})");
                }
            }
        }
    }
    eprintln!("mutations: {ok} accepted (in domain), {err} rejected, 0 panics");
}

/// All fields of `request.bin`.
#[derive(Clone)]
struct Req {
    pv: u32,
    chain: Vec<u8>,
    shard: u64,
    height: u64,
    bgp: u128,
    gas_limit: u64,
    root: [u8; 32],
    rs: Vec<spec::Receipt>,
}

impl Req {
    fn of(b: &[u8]) -> Req {
        let r = rx::decode_request(b).unwrap();
        Req {
            pv: r.protocol_version,
            chain: r.chain_id.to_vec(),
            shard: r.shard_id,
            height: r.block_height,
            bgp: r.block_gas_price,
            gas_limit: r.gas_limit,
            root: r.pre_state_root,
            rs: r.receipts.iter().map(spec::Receipt::from_rx).collect(),
        }
    }
    fn encode(&self) -> Vec<u8> {
        let le = |w: &mut Vec<u8>, b: &[u8]| {
            w.extend((b.len() as u32).to_le_bytes());
            w.extend(b);
        };
        let mut w = vec![];
        le(&mut w, rx::REQUEST_FORMAT);
        le(&mut w, rx::STATEMENT_ID);
        w.extend(self.pv.to_le_bytes());
        le(&mut w, &self.chain);
        w.extend(self.shard.to_le_bytes());
        w.extend(self.height.to_le_bytes());
        w.extend(self.bgp.to_le_bytes());
        w.extend(self.gas_limit.to_le_bytes());
        w.extend(self.root);
        w.extend(spec::encode_receipts(&self.rs));
        w
    }
}

#[test]
fn structured_out_of_range_rejected() {
    // a fixture with several receipts
    let d = cases().into_iter().find(|d| d.ends_with("s20261003-v0")).unwrap();
    let (req, wit) = (read(&d, "request.bin"), read(&d, "witness.bin"));
    let base = Req::of(&req);
    assert_eq!(base.encode(), req, "request encoder");
    assert!(matches!(run(req.clone(), wit.clone()), Ok(Ok(_))));
    let max = u128::MAX;
    let mut muts: Vec<(&str, Box<dyn Fn(&mut Req)>)> = vec![
        ("deposit u128::MAX", Box::new(|r: &mut Req| r.rs[0].deposit = max)),
        ("deposit u128::MAX - 1", Box::new(|r: &mut Req| r.rs[0].deposit = max - 1)),
        ("deposits sum overflow", Box::new(|r: &mut Req| {
            let k = r.rs[0].receiver_id.clone();
            for x in r.rs.iter_mut() {
                x.receiver_id = k.clone();
                x.deposit = max / 2;
            }
        })),
        ("gas_price u128::MAX, bgp u128::MAX", Box::new(|r: &mut Req| {
            r.bgp = max;
            r.rs[0].gas_price = max;
        })),
        ("gas_price u128::MAX (surplus overflow)", Box::new(|r: &mut Req| r.rs[0].gas_price = max)),
        ("bgp u128::MAX, all burn (tokens overflow)", Box::new(|r: &mut Req| {
            r.bgp = max;
            for x in r.rs.iter_mut() {
                x.gas_price = max / 300_000_000_000;
            }
        })),
        ("65-byte receiver", Box::new(|r: &mut Req| r.rs[0].receiver_id = vec![b'a'; 65])),
        ("65-byte signer", Box::new(|r: &mut Req| r.rs[0].signer_id = vec![b'a'; 65])),
        ("1-byte predecessor", Box::new(|r: &mut Req| r.rs[0].predecessor_id = b"a".to_vec())),
        ("system predecessor", Box::new(|r: &mut Req| r.rs[0].predecessor_id = b"system".to_vec())),
        ("implicit receiver", Box::new(|r: &mut Req| r.rs[0].receiver_id = vec![b'a'; 64])),
        ("n = 0", Box::new(|r: &mut Req| r.rs.clear())),
        ("n = 257", Box::new(|r: &mut Req| {
            let r0 = r.rs[0].clone();
            r.rs = (0..257u32)
                .map(|i| spec::Receipt { receipt_id: npudr::hash::sha256(&i.to_le_bytes()).to_vec(), ..r0.clone() })
                .collect();
        })),
        ("duplicate receipt id", Box::new(|r: &mut Req| {
            let id = r.rs[0].receipt_id.clone();
            r.rs[1].receipt_id = id;
        })),
        ("wrong root", Box::new(|r: &mut Req| r.root[0] ^= 1)),
        ("zero root", Box::new(|r: &mut Req| r.root = [0; 32])),
        ("gas limit 0", Box::new(|r: &mut Req| r.gas_limit = 0)),
        ("protocol version 85", Box::new(|r: &mut Req| r.pv = 85)),
        ("chain testnet", Box::new(|r: &mut Req| r.chain = b"testnet".to_vec())),
        ("unknown receiver", Box::new(|r: &mut Req| r.rs[0].receiver_id = b"nobody-here.near".to_vec())),
        ("secp256k1 key with ed25519 length", Box::new(|r: &mut Req| r.rs[0].signer_pk.tag = 1)),
    ];
    // in-domain variants (must be accepted, claim = reexec)
    let ok_muts: Vec<(&str, Box<dyn Fn(&mut Req)>)> = vec![
        ("bgp 0", Box::new(|r: &mut Req| r.bgp = 0)),
        ("gas price 0", Box::new(|r: &mut Req| r.rs[0].gas_price = 0)),
        ("big deposit", Box::new(|r: &mut Req| r.rs[0].deposit = 1u128 << 120)),
        ("max shard/height", Box::new(|r: &mut Req| {
            r.shard = u64::MAX;
            r.height = u64::MAX;
        })),
    ];
    for (name, f) in muts.drain(..) {
        let mut r = base.clone();
        f(&mut r);
        match run(r.encode(), wit.clone()) {
            Ok(Ok(_)) => panic!("{name}: accepted"),
            Ok(Err(e)) => eprintln!("{name}: rejected: {e}"),
            Err(p) => panic!("{name}: panicked: {p}"),
        }
    }
    for (name, f) in ok_muts {
        let mut r = base.clone();
        f(&mut r);
        let b = r.encode();
        match run(b.clone(), wit.clone()) {
            Ok(Ok(c)) => assert_eq!(c, near::reexec::engine::derive_claim(&b, &wit).unwrap().encode(), "{name}"),
            Ok(Err(e)) => panic!("{name}: rejected: {e}"),
            Err(p) => panic!("{name}: panicked: {p}"),
        }
    }
    // witness-side: empty, wrong format, non-ascending values, garbage nodes
    let (root, vals) = rx::decode_witness(&wit).unwrap();
    let vals: Vec<Vec<u8>> = vals.iter().map(|v| v.to_vec()).collect();
    let set: BTreeSet<Vec<u8>> = vals.iter().cloned().collect();
    let mut bad_wits: Vec<(&str, Vec<u8>)> = vec![
        ("empty", vec![]),
        ("no values", genmax::encode_witness(&root, &BTreeSet::new())),
        ("other root", genmax::encode_witness(&[7; 32], &set)),
    ];
    let mut desc = vec![];
    desc.extend(&wit[..wit.len() - 1]); // truncated
    bad_wits.push(("truncated", desc));
    for (k, v) in vals.iter().enumerate() {
        // corrupt one value at a time (node tag, lengths, memory usage)
        for j in [0usize, 1, 4, v.len() / 2, v.len() - 1] {
            let mut s2 = set.clone();
            s2.remove(v);
            let mut w = v.clone();
            w[j.min(v.len() - 1)] ^= 0x80;
            s2.insert(w);
            bad_wits.push(("corrupt value", genmax::encode_witness(&root, &s2)));
        }
        if k > 40 {
            break;
        }
    }
    for (name, w) in bad_wits {
        if let Err(p) = run(req.clone(), w) {
            panic!("witness {name}: panicked: {p}");
        }
    }
}

/// A chain of empty-key extensions deeper than any in-domain path: rejected
/// by the depth guard (no stack overflow).
#[test]
fn deep_extension_chain_rejected() {
    // leaf with empty key under 130 one-child branches is what genmax builds;
    // here: one receiver, then 80,000 empty-key extensions (3.7 MB > 3 MB)
    let id = b"deep-chain.near".to_vec();
    let key = spec::account_key_path(&id);
    let val = {
        let mut v = 1000u128.to_le_bytes().to_vec();
        v.extend([0u8; 16 + 32]);
        v.extend(100u64.to_le_bytes());
        v
    };
    let mut values = BTreeSet::new();
    values.insert(val.clone());
    // leaf with the whole key
    let hp = spec::hex_prefix(&key, true);
    let mut leaf = vec![0u8];
    leaf.extend((hp.len() as u32).to_le_bytes());
    leaf.extend(&hp);
    leaf.extend(72u32.to_le_bytes());
    leaf.extend(npudr::hash::sha256(&val));
    leaf.extend(0u64.to_le_bytes());
    let mut h = npudr::hash::sha256(&leaf);
    values.insert(leaf);
    for e in 0..80_000u64 {
        let mut s = vec![3u8, 1, 0, 0, 0, 0];
        s.extend(h);
        s.extend(e.to_le_bytes());
        h = npudr::hash::sha256(&s);
        values.insert(s);
    }
    let rc = spec::Receipt {
        predecessor_id: b"alice.near".to_vec(),
        receiver_id: id,
        receipt_id: vec![1; 32],
        signer_id: b"alice.near".to_vec(),
        signer_pk: spec::PublicKey { tag: 0, data: vec![2; 32] },
        gas_price: 100,
        deposit: 1,
    };
    let req = genmax::encode_request(0, 1, 100, 1 << 50, &h, &[rc]);
    let wit = genmax::encode_witness(&h, &values);
    match run(req, wit) {
        Ok(Err(e)) => assert!(e.contains("too deep") || e.contains("too large"), "{e}"),
        Ok(Ok(_)) => panic!("accepted"),
        Err(p) => panic!("panicked: {p}"),
    }
}

/// The judge binary: rejected inputs → exit 2, no output files; a fixture →
/// exit 0, both files.
#[test]
fn prove_binary_exit_codes() {
    let exe = env!("CARGO_BIN_EXE_prove");
    let tmp = std::env::temp_dir().join(format!("npudr-prove-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(tmp.join("pub")).unwrap();
    let params = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../oracle/fixtures/public/params.bin");
    std::fs::copy(params, tmp.join("pub/public.bin")).unwrap();
    let d = cases().into_iter().find(|d| d.ends_with("example-tierA")).unwrap();
    let (req, wit) = (read(&d, "request.bin"), read(&d, "witness.bin"));
    let prove = |req: &[u8], wit: &[u8]| -> (i32, bool, bool) {
        std::fs::write(tmp.join("request.bin"), req).unwrap();
        std::fs::write(tmp.join("witness.bin"), wit).unwrap();
        let (c, p) = (tmp.join("claim.bin"), tmp.join("proof.bin"));
        let _ = std::fs::remove_file(&c);
        let _ = std::fs::remove_file(&p);
        let st = std::process::Command::new(exe)
            .args(["--public", tmp.join("pub").to_str().unwrap()])
            .args(["--request", tmp.join("request.bin").to_str().unwrap()])
            .args(["--witness", tmp.join("witness.bin").to_str().unwrap()])
            .args(["--claim-out", c.to_str().unwrap(), "--proof-out", p.to_str().unwrap()])
            .stderr(std::process::Stdio::null())
            .status()
            .unwrap();
        let leftovers = std::fs::read_dir(&tmp).unwrap().filter(|e| e.as_ref().unwrap().file_name().to_string_lossy().contains(".tmp-")).count();
        assert_eq!(leftovers, 0, "temporary files left");
        (st.code().unwrap_or(-1), c.exists(), p.exists())
    };
    let mut rng = Rng(7);
    for i in 0..12 {
        let (r2, w2) = if i % 2 == 0 { (mutate(&mut rng, &req), wit.clone()) } else { (req.clone(), mutate(&mut rng, &wit)) };
        if run(r2.clone(), w2.clone()).map(|r| r.is_ok()).unwrap_or(false) {
            continue; // still in domain
        }
        assert_eq!(prove(&r2, &w2), (2, false, false), "mutation {i}");
    }
    assert_eq!(prove(&[], &wit), (2, false, false));
    assert_eq!(prove(&req, &wit), (0, true, true));
    assert_eq!(std::fs::read(tmp.join("claim.bin")).unwrap(), read(&d, "expected_claim.bin"));
    let _ = std::fs::remove_dir_all(&tmp);
}
