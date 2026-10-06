//! Ed25519 verdicts and signatures from nearcore's own code (near-crypto at the pinned
//! commit, ed25519-dalek 2.2.0 / curve25519-dalek 4.1.3 with the node's feature set).
//!
//!   ed25519-judge --in IN.jsonl --out OUT.jsonl
//!       IN: one JSON object per line {"id", "pk", "sig", "msg"} (hex; pk 32 B, sig 64 B).
//!       OUT: {"id", "sig_decodes", "verify", "verify_raw"}:
//!         sig_decodes = borsh `near_crypto::Signature` decoding of `0x00 ‖ sig` succeeds
//!                       (it rejects `sig[63] & 0xE0 != 0`, signature.rs:1174-1183);
//!         verify      = `Signature::verify(msg, PublicKey::ED25519(pk))` on the decoded
//!                       signature (null if it does not decode) — what
//!                       `ValidatedTransaction::new` evaluates (transaction.rs:302-308);
//!         verify_raw  = the same `Signature::verify` on `ed25519_dalek::Signature::from_bytes(sig)`
//!                       without the borsh pre-check (defined for every 64-byte string).
//!   ed25519-sign --seed S --n N --out OUT.jsonl
//!       N signatures made by `near_crypto::SecretKey::sign` (ED25519) on random keys and
//!       messages (lengths 0..300, every 4th one a 32-byte "transaction hash"), with the
//!       nearcore verdict of the honest signature.

use borsh::BorshDeserialize;
use near_crypto::{ED25519PublicKey, ED25519SecretKey, PublicKey, SecretKey, Signature};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::{Value, json};
use std::io::{BufRead, Write};
use std::path::Path;

fn unhex(v: &Value, k: &str) -> Vec<u8> {
    hex::decode(v[k].as_str().unwrap_or_else(|| panic!("missing {k}"))).expect("hex")
}

pub fn judge_one(pk: &[u8], sig: &[u8], msg: &[u8]) -> Value {
    let pk: [u8; 32] = pk.try_into().expect("pk must be 32 bytes");
    let sig: [u8; 64] = sig.try_into().expect("sig must be 64 bytes");
    let public_key = PublicKey::ED25519(ED25519PublicKey(pk));
    let mut enc = vec![0u8];
    enc.extend_from_slice(&sig);
    let decoded = Signature::try_from_slice(&enc).ok();
    let verify = decoded.as_ref().map(|s| s.verify(msg, &public_key));
    let raw = Signature::ED25519(ed25519_dalek::Signature::from_bytes(&sig));
    let verify_raw = raw.verify(msg, &public_key);
    json!({"sig_decodes": decoded.is_some(), "verify": verify, "verify_raw": verify_raw})
}

pub fn cmd_judge(inp: &Path, out: &Path) -> i32 {
    let f = std::io::BufReader::new(std::fs::File::open(inp).expect("open --in"));
    let mut w = std::io::BufWriter::new(std::fs::File::create(out).expect("create --out"));
    let mut n = 0usize;
    for line in f.lines() {
        let line = line.unwrap();
        if line.trim().is_empty() {
            continue;
        }
        let v: Value = serde_json::from_str(&line).expect("json line");
        let mut r = judge_one(&unhex(&v, "pk"), &unhex(&v, "sig"), &unhex(&v, "msg"));
        r["id"] = v["id"].clone();
        writeln!(w, "{}", r).unwrap();
        n += 1;
    }
    eprintln!("judged {n} ed25519 cases");
    0
}

pub fn cmd_sign(seed: u64, n: usize, out: &Path) -> i32 {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut w = std::io::BufWriter::new(std::fs::File::create(out).expect("create --out"));
    for i in 0..n {
        let sk_seed: [u8; 32] = rng.r#gen();
        let kp = ed25519_dalek::SigningKey::from_bytes(&sk_seed);
        let sk = SecretKey::ED25519(ED25519SecretKey(kp.to_keypair_bytes()));
        let len = if i % 4 == 0 { 32 } else { rng.gen_range(0..300) };
        let msg: Vec<u8> = (0..len).map(|_| rng.r#gen()).collect();
        let sig = sk.sign(&msg);
        let sig_bytes = match &sig {
            Signature::ED25519(s) => s.to_bytes(),
            _ => unreachable!(),
        };
        let pk = match sk.public_key() {
            PublicKey::ED25519(p) => p.0,
            _ => unreachable!(),
        };
        let mut r = judge_one(&pk, &sig_bytes, &msg);
        r["id"] = json!(format!("near-sign-{seed}-{i}"));
        r["pk"] = json!(hex::encode(pk));
        r["sig"] = json!(hex::encode(sig_bytes));
        r["msg"] = json!(hex::encode(&msg));
        r["sk_seed"] = json!(hex::encode(sk_seed));
        writeln!(w, "{}", r).unwrap();
    }
    0
}
