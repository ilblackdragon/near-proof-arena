//! `mldsa-vectors`: ML-DSA-65 verification verdicts of the pinned crate, for the Lean pin
//! (`spec/lean/v3/NearSpecV3/Examples/MlDsaVectors.lean`).
//!
//! Every verdict is `near_crypto::Signature::verify` itself (aws-lc-rs 1.16.2, pure ML-DSA-65 with
//! an empty context), on nearcore-shaped inputs: 32-byte messages (a transaction or NEP-461 hash
//! is 32 bytes), keys from `SecretKey::from_seed`. Valid signatures are mutated in each field and
//! in every malformed-hint class the library rejects. Output: JSON on stdout,
//! `{keys: [hex], sigs: [hex], cases: [{name, key, msg, sig, patch: [[offset, byte]], expect}]}`.
use near_crypto::{KeyType, MlDsa65Signature, PublicKey, SecretKey, Signature};
use serde_json::json;
use sha2::Digest;

const CT: usize = 48;
const Z: usize = 3200;
const OMEGA: usize = 55;
const K: usize = 6;
const H: usize = CT + Z; // start of the 61-byte hint block

fn raw_sig(s: &Signature) -> Vec<u8> {
    match s {
        Signature::MLDSA65(x) => x.0.to_vec(),
        _ => panic!("not ML-DSA"),
    }
}
fn raw_pk(p: &PublicKey) -> Vec<u8> {
    match p {
        PublicKey::MLDSA65(x) => x.0.to_vec(),
        _ => panic!("not ML-DSA"),
    }
}
fn verdict(pk: &PublicKey, msg: &[u8], sig: &[u8]) -> bool {
    let s = Signature::MLDSA65(MlDsa65Signature(Box::new(sig.try_into().unwrap())));
    s.verify(msg, pk)
}

/// The hint-encoding mutations that make `HintBitUnpack` fail (FIPS 204 Algorithm 21), each only
/// when the signature's hint layout allows it. Returns (name, patch).
pub fn hint_mutations(sig: &[u8]) -> Vec<(&'static str, Vec<(usize, u8)>)> {
    let y = &sig[H..H + OMEGA + K];
    let cnt: Vec<usize> = (0..K).map(|i| y[OMEGA + i] as usize).collect();
    let total = cnt[K - 1];
    let mut out = Vec::new();
    // indices not strictly increasing inside one polynomial: swap the first two of a poly with ≥ 2
    let mut start = 0;
    for i in 0..K {
        if cnt[i] >= start + 2 {
            out.push(("hint-unordered", vec![(H + start, y[start + 1]), (H + start + 1, y[start])]));
            out.push(("hint-duplicate", vec![(H + start + 1, y[start])]));
            break;
        }
        start = cnt[i];
    }
    // a count above ω
    out.push(("hint-count-over-omega", vec![(H + OMEGA + K - 1, (OMEGA + 1) as u8)]));
    out.push(("hint-count-255", vec![(H + OMEGA + K - 1, 255)]));
    // a decreasing count
    if cnt[1] < OMEGA {
        out.push(("hint-count-decreasing", vec![(H + OMEGA, (cnt[1] + 1) as u8)]));
    }
    // a non-zero unused index slot
    if total < OMEGA {
        out.push(("hint-padding-nonzero", vec![(H + OMEGA - 1, 1)]));
        // one extra hint appended to the last polynomial (well-formed encoding, wrong hint)
        let last = if total > 0 { y[total - 1] } else { 0 };
        if last < 255 && total > cnt[K - 2] {
            out.push(("hint-extra-wellformed", vec![(H + total, last + 1), (H + OMEGA + K - 1, (total + 1) as u8)]));
        }
    }
    // a well-formed but different hint: drop the last hint
    if total > 0 && total > cnt[K - 2] {
        out.push(("hint-drop-last", vec![(H + total - 1, 0), (H + OMEGA + K - 1, (total - 1) as u8)]));
    }
    out
}

/// `mldsa-vectors --check FILE`: for each line `SEED_STR MSG_HEX SIG_HEX` of FILE, the public key
/// `SecretKey::from_seed(MLDSA65, SEED_STR)` and `near_crypto::Signature::verify` of the signature
/// (item 10: the boundary signatures of `tools/d3/mldsa65_bound.py`). JSON lines on stdout.
fn check(path: &str) -> i32 {
    for line in std::fs::read_to_string(path).unwrap().lines().filter(|l| !l.trim().is_empty()) {
        let v: Vec<&str> = line.split_whitespace().collect();
        let pk = SecretKey::from_seed(KeyType::MLDSA65, v[0]).public_key();
        let msg = hex::decode(v[1]).unwrap();
        let sig = hex::decode(v[2]).unwrap();
        println!("{}", json!({"seed": v[0], "pk": hex::encode(raw_pk(&pk)), "msg": v[1],
            "sig_sha256": hex::encode(sha2::Sha256::digest(&sig)), "verify": verdict(&pk, &msg, &sig)}));
    }
    0
}

pub fn command(args: &[String]) -> i32 {
    if let Some(i) = args.iter().position(|a| a == "--check") {
        return check(&args[i + 1]);
    }
    let keys: Vec<SecretKey> = (0..2).map(|i| SecretKey::from_seed(KeyType::MLDSA65, &format!("w06-mldsa-vector-{i}"))).collect();
    let pks: Vec<PublicKey> = keys.iter().map(|k| k.public_key()).collect();
    let mut sigs: Vec<Vec<u8>> = Vec::new();
    let mut cases = Vec::new();
    let mut add = |name: String, key: usize, msg: &[u8], sig_id: usize, base: &[u8], patch: Vec<(usize, u8)>, pks: &[PublicKey]| {
        let mut s = base.to_vec();
        for &(o, b) in &patch {
            s[o] = b;
        }
        let expect = verdict(&pks[key], msg, &s);
        cases.push(json!({"name": name, "key": key, "msg": hex::encode(msg), "sig": sig_id,
            "patch": patch.iter().map(|(o, b)| json!([o, b])).collect::<Vec<_>>(), "expect": expect}));
    };
    for m in 0..12u8 {
        let key = (m % 2) as usize;
        let msg: Vec<u8> = (0..32u8).map(|i| i.wrapping_mul(37).wrapping_add(m.wrapping_mul(101))).collect();
        let sig = raw_sig(&keys[key].sign(&msg));
        let id = sigs.len();
        sigs.push(sig.clone());
        add(format!("m{m}-valid"), key, &msg, id, &sig, vec![], &pks);
        if m < 4 {
            add(format!("m{m}-wrong-key"), 1 - key, &msg, id, &sig, vec![], &pks);
            let mut other = msg.clone();
            other[31] ^= 1;
            add(format!("m{m}-wrong-msg"), key, &other, id, &sig, vec![], &pks);
            add(format!("m{m}-ctilde-flip"), key, &msg, id, &sig, vec![(0, sig[0] ^ 1)], &pks);
            add(format!("m{m}-ctilde-last-flip"), key, &msg, id, &sig, vec![(CT - 1, sig[CT - 1] ^ 0x80)], &pks);
            add(format!("m{m}-z-flip"), key, &msg, id, &sig, vec![(CT + 1000, sig[CT + 1000] ^ 4)], &pks);
            // z coefficient 0 packed as 0 → z = γ1 (norm bound violated)
            add(format!("m{m}-z-norm-gamma1"), key, &msg, id, &sig, vec![(CT, 0), (CT + 1, 0), (CT + 2, sig[CT + 2] & 0xF0)], &pks);
            // packed 2^20 − 1 → z = −γ1 + 1 (norm bound violated)
            add(format!("m{m}-z-norm-neg"), key, &msg, id, &sig, vec![(CT, 0xFF), (CT + 1, 0xFF), (CT + 2, sig[CT + 2] | 0x0F)], &pks);
            for (n, p) in hint_mutations(&sig) {
                add(format!("m{m}-{n}"), key, &msg, id, &sig, p, &pks);
            }
        }
    }
    // an all-zero and an all-0xFF signature, against key 0
    let msg0: Vec<u8> = vec![7u8; 32];
    for (n, b) in [("zero-sig", 0u8), ("ff-sig", 0xFF)] {
        let id = sigs.len();
        let s = vec![b; 3309];
        sigs.push(s.clone());
        add(n.to_string(), 0, &msg0, id, &s, vec![], &pks);
    }
    let out = json!({
        "crate": "aws-lc-rs 1.16.2 via near_crypto::Signature::verify (nearcore 44f7ae6c)",
        "keys": pks.iter().map(|p| hex::encode(raw_pk(p))).collect::<Vec<_>>(),
        "sigs": sigs.iter().map(hex::encode).collect::<Vec<_>>(),
        "cases": cases,
    });
    println!("{}", serde_json::to_string(&out).unwrap());
    0
}
