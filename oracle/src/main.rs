//! near-arena-oracle: judge-owned oracle for `near/pv86/receipt-transfer-batch/v0`.
//!
//! Scopes: `--scope v1` (default) = `near/pv86/receipt-transfer-batch/v0`
//! (challenge near-transfer-receipt-v1, unchanged); `--scope v2` =
//! `near/pv86/receipt-transfer-batch/v1` (challenge near-transfer-receipt-v2,
//! real post-state root incl. the bandwidth-scheduler write; src/v2.rs).
//!
//! Commands:
//!   gen    --seed S --valid N [--invalid M] --out DIR [--profiles p1,p2]
//!          Generate OracleCase directories (request.bin, witness.bin, claim.bin,
//!          state.bin, diagnostics.json); [--receipts N] fixes the receipt count
//!          (workload classes). Every case is executed by the real
//!          pinned nearcore `Runtime::apply`. `--profiles max_witness` (never
//!          part of the default profile list) generates the maximal in-domain
//!          witness class: 256 receipts (or `--receipts N`) whose recorded
//!          slice witness is calibrated to just under the 3 000 000-byte
//!          domain cap (src/maxwit.rs).
//!   replay --case DIR
//!          Re-run nearcore from state.bin + request.bin and check that claim.bin
//!          and witness.bin are reproduced byte for byte (exit 1 otherwise).
//!   params --out FILE
//!          Emit the runtime-config description whose JCS sha256 is the
//!          challenge's runtime_config_digest.
//!   check-request --request FILE [--challenge FILE]
//!          Fail-closed version gate: exit 0 iff the request's embedded
//!          protocol version / chain id are the ones this oracle is pinned to
//!          (and the challenge's), else exit 3.
//!
//! Every command accepts `--challenge FILE` (a ChallengeDefinition JSON) and
//! refuses to run (exit 3) unless the challenge pins exactly this oracle's
//! nearcore commit, protocol version and chain id: an oracle built for one
//! protocol version never serves a challenge for another
//! (docs/PROTOCOL_UPGRADES.md §3).

mod domain;
mod enc;
mod exec;
mod casegen;
mod maxwit;
mod v2;

use near_primitives::hash::hash;
use serde_json::json;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const NEARCORE_COMMIT: &str = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993";

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(String::as_str).unwrap_or("");
    if let Err(e) = check_challenge_pin(&args) {
        eprintln!("REFUSED (fail-closed): {e}");
        std::process::exit(3);
    }
    let scope = arg(&args, "--scope").unwrap_or_else(|| "v1".into());
    let code = match (cmd, scope.as_str()) {
        ("gen", "v1") => cmd_gen(&args),
        ("replay", "v1") => cmd_replay(&args),
        ("params", "v1") => cmd_params(&args),
        ("check-request", "v1") => cmd_check_request(&args),
        ("gen", "v2") => v2::cmd_gen(&args),
        ("replay", "v2") => v2::cmd_replay(&args),
        ("params", "v2") => v2::cmd_params(&args),
        _ => {
            eprintln!("usage: near-arena-oracle gen|replay|params|check-request [--scope v1|v2] ... (see src/main.rs)");
            2
        }
    };
    std::process::exit(code);
}

/// `--challenge FILE`: the challenge must pin this oracle's nearcore commit,
/// protocol version and chain id; anything else is refused.
fn check_challenge_pin(args: &[String]) -> Result<(), String> {
    let Some(p) = arg(args, "--challenge") else { return Ok(()) };
    let raw = std::fs::read(&p).map_err(|e| format!("{p}: {e}"))?;
    let c: serde_json::Value = serde_json::from_slice(&raw).map_err(|e| format!("{p}: {e}"))?;
    let pv = c["protocol_version"].as_u64();
    if pv != Some(domain::PROTOCOL_VERSION as u64) {
        return Err(format!(
            "challenge protocol_version {pv:?} != oracle protocol version {}",
            domain::PROTOCOL_VERSION
        ));
    }
    if c["chain_id"].as_str() != Some(domain::CHAIN_ID) {
        return Err(format!("challenge chain_id {} != oracle chain id {}", c["chain_id"], domain::CHAIN_ID));
    }
    if c["nearcore"]["commit"].as_str() != Some(NEARCORE_COMMIT) {
        return Err(format!("challenge nearcore commit {} != oracle nearcore commit {NEARCORE_COMMIT}", c["nearcore"]["commit"]));
    }
    Ok(())
}

/// Version gate on a request: the oracle only computes expected claims for
/// requests of its own protocol version and chain.
fn request_version_ok(req: &enc::Request) -> Result<(), String> {
    if req.protocol_version != domain::PROTOCOL_VERSION {
        return Err(format!(
            "request protocol_version {} != oracle protocol version {}",
            req.protocol_version,
            domain::PROTOCOL_VERSION
        ));
    }
    if req.chain_id != domain::CHAIN_ID {
        return Err(format!("request chain_id {} != oracle chain id {}", req.chain_id, domain::CHAIN_ID));
    }
    Ok(())
}

fn cmd_check_request(args: &[String]) -> i32 {
    let p = arg(args, "--request").expect("--request");
    let req = match enc::decode_request(&std::fs::read(&p).unwrap()) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("REFUSED (fail-closed): undecodable request: {e}");
            return 3;
        }
    };
    match request_version_ok(&req) {
        Ok(()) => {
            println!("REQUEST_OK protocol_version={} chain_id={}", req.protocol_version, req.chain_id);
            0
        }
        Err(e) => {
            eprintln!("REFUSED (fail-closed): {e}");
            3
        }
    }
}

/// RFC 8785 JCS for the integer/string/bool JSON we produce (keys sorted by
/// UTF-16 code units == bytes for ASCII keys; no floats).
fn jcs(v: &serde_json::Value) -> String {
    use serde_json::Value;
    match v {
        Value::Object(m) => {
            let mut ks: Vec<&String> = m.keys().collect();
            ks.sort_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
            let items: Vec<String> =
                ks.iter().map(|k| format!("{}:{}", serde_json::to_string(k).unwrap(), jcs(&m[*k]))).collect();
            format!("{{{}}}", items.join(","))
        }
        Value::Array(a) => format!("[{}]", a.iter().map(jcs).collect::<Vec<_>>().join(",")),
        Value::Number(n) => {
            assert!(!n.is_f64(), "float in canonical json");
            n.to_string()
        }
        _ => serde_json::to_string(v).unwrap(),
    }
}

/// params.bin: challenge-level public parameters handed to `prepare`.
fn params_bin(runtime_config_digest: &[u8; 32]) -> Vec<u8> {
    let mut w = enc::W::default();
    w.str("near-arena-params-v1")
        .str(enc::STATEMENT_ID)
        .u32(domain::PROTOCOL_VERSION)
        .str(domain::CHAIN_ID)
        .raw(runtime_config_digest);
    w.0
}

struct Layout {
    /// "claim.bin" (oracle layout) or "expected_claim.bin" (SDK fixtures layout)
    claim_name: &'static str,
}

fn write_case(dir: &Path, case: &casegen::Case, ex: &exec::Executed, seed: u64, idx: u64, layout: &Layout) -> bool {
    std::fs::create_dir_all(dir).unwrap();
    let req_bytes = ex.request.encode();
    let witness = enc::encode_witness(&ex.request.pre_state_root, &ex.witness_values);
    let kv: Vec<(Vec<u8>, Vec<u8>)> = case.state.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    std::fs::write(dir.join("request.bin"), &req_bytes).unwrap();
    std::fs::write(dir.join("witness.bin"), &witness).unwrap();
    std::fs::write(dir.join("state.bin"), enc::encode_state(&kv)).unwrap();

    let wbytes: usize = ex.witness_values.iter().map(|v| v.len()).sum();
    let dom = domain::check(&ex.request, &case.state, wbytes);
    let in_domain = dom.is_ok();
    let expected_in_domain = case.invalid_kind.is_none();
    // A valid case is only emitted with a claim if (a) the Rust domain check
    // accepts it and (b) nearcore behaved cleanly. Out-of-domain cases never get
    // a claim.bin: the judge must not issue them as jobs.
    let mut consistent = in_domain == expected_in_domain;
    if in_domain && !ex.clean {
        consistent = false; // domain predicate admitted a case nearcore treats differently
    }
    if in_domain {
        let c = ex.claim.as_ref().unwrap();
        std::fs::write(dir.join(layout.claim_name), c.encode()).unwrap();
        // round-trip the strict decoder
        assert_eq!(enc::Claim::decode(&c.encode()).unwrap(), *c);
        assert!(enc::decode_request(&req_bytes).is_ok());
        if let Ok(sim) = &dom {
            if sim.tokens_burnt_total != c.tokens_burnt_total || sim.refunds as u32 != c.refund_count {
                consistent = false;
            }
        }
    } else {
        let _ = std::fs::remove_file(dir.join(layout.claim_name));
    }
    let diag = json!({
        "schema": "near-arena-oracle-case-v1",
        "case_id": case.id,
        "generator": {"seed": seed, "index": idx, "profile": case.profile, "invalid_kind": case.invalid_kind},
        "nearcore_commit": NEARCORE_COMMIT,
        "synthetic_state": true,
        "in_domain": in_domain,
        "domain_reason": dom.as_ref().err(),
        "expected_in_domain": expected_in_domain,
        "consistent": consistent,
        "nearcore": ex.nearcore,
        "nearcore_problems": ex.problems,
        "claim": ex.claim.as_ref().filter(|_| in_domain).map(|c| c.to_json()),
        "sizes": {
            "request_bytes": req_bytes.len(),
            "witness_bytes": witness.len(),
            "receipts": ex.request.receipts.len(),
            "state_entries": kv.len(),
        },
        "digests": {
            "request.bin": format!("sha256:{}", hex::encode(hash(&req_bytes).0)),
            "witness.bin": format!("sha256:{}", hex::encode(hash(&witness).0)),
            "claim.bin": ex.claim.as_ref().filter(|_| in_domain).map(|c| format!("sha256:{}", hex::encode(hash(&c.encode()).0))),
        }
    });
    std::fs::write(dir.join("diagnostics.json"), serde_json::to_string_pretty(&diag).unwrap() + "\n").unwrap();
    if !consistent {
        eprintln!(
            "INCONSISTENT case {}: in_domain={in_domain} expected={expected_in_domain} reason={:?} problems={:?}",
            case.id,
            dom.as_ref().err(),
            ex.problems
        );
    }
    consistent
}

fn cmd_gen(args: &[String]) -> i32 {
    let seed: u64 = arg(args, "--seed").unwrap_or("1".into()).parse().unwrap();
    let nvalid: u64 = arg(args, "--valid").unwrap_or("10".into()).parse().unwrap();
    let ninvalid: u64 = arg(args, "--invalid").unwrap_or("0".into()).parse().unwrap();
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let profiles: Vec<String> = arg(args, "--profiles")
        .map(|s| s.split(',').map(String::from).collect())
        .unwrap_or_else(|| casegen::PROFILES.iter().map(|s| s.to_string()).collect());
    if let Some(r) = arg(args, "--receipts") {
        let r: usize = r.parse().expect("--receipts N");
        assert!((1..=domain::MAX_BATCH).contains(&r), "--receipts must be in 1..=256");
        casegen::FORCE_RECEIPTS.store(r, std::sync::atomic::Ordering::Relaxed);
    }
    let fixtures = args.iter().any(|a| a == "--fixtures-layout");
    let layout = Layout { claim_name: if fixtures { "expected_claim.bin" } else { "claim.bin" } };
    let case_root = if fixtures { out.join("cases") } else { out.clone() };
    let mut ok = true;
    let mut n_ok = 0;
    let t0 = std::time::Instant::now();
    if args.iter().any(|a| a == "--with-example") {
        for tier in ["A", "B"] {
            let case = casegen::example_case(tier);
            let ex = exec::run(case.request.clone(), &case.state);
            let good = write_case(&case_root.join(&case.id), &case, &ex, 0, 0, &layout);
            ok &= good;
            n_ok += good as u32;
        }
    }
    for i in 0..nvalid {
        let profile = &profiles[(i as usize) % profiles.len()];
        let case = casegen::gen_valid(seed, i, profile);
        let ex = exec::run(case.request.clone(), &case.state);
        let good = write_case(&case_root.join(&case.id), &case, &ex, seed, i, &layout);
        ok &= good;
        n_ok += good as u32;
    }
    for i in 0..ninvalid {
        let kind = casegen::INVALID_KINDS[(i as usize) % casegen::INVALID_KINDS.len()];
        let case = casegen::gen_invalid(seed, i, kind);
        let ex = exec::run(case.request.clone(), &case.state);
        let good = write_case(&case_root.join(&case.id), &case, &ex, seed, i, &layout);
        ok &= good;
        n_ok += good as u32;
    }
    if fixtures {
        let rc = runtime_config_json();
        let d = hash(jcs(&rc).as_bytes()).0;
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("params.bin"), params_bin(&d)).unwrap();
    }
    eprintln!(
        "generated {} cases ({} consistent) in {:?}",
        n_ok_total(nvalid, ninvalid, args),
        n_ok,
        t0.elapsed()
    );
    if ok { 0 } else { 1 }
}

fn cmd_replay(args: &[String]) -> i32 {
    let dir = PathBuf::from(arg(args, "--case").expect("--case"));
    let req = enc::decode_request(&std::fs::read(dir.join("request.bin")).unwrap()).unwrap();
    let kv: BTreeMap<Vec<u8>, Vec<u8>> =
        enc::decode_state(&std::fs::read(dir.join("state.bin")).unwrap()).unwrap().into_iter().collect();
    let want_root = req.pre_state_root;
    let claim_present = dir.join("claim.bin").exists() || dir.join("expected_claim.bin").exists();
    if claim_present {
        // An expected claim is only ever produced for this oracle's version.
        if let Err(e) = request_version_ok(&req) {
            eprintln!("REFUSED (fail-closed): {e}");
            return 3;
        }
    }
    let ex = exec::run(req, &kv);
    let mut ok = ex.request.pre_state_root == want_root;
    let w = enc::encode_witness(&ex.request.pre_state_root, &ex.witness_values);
    ok &= w == std::fs::read(dir.join("witness.bin")).unwrap();
    let claim_file = if dir.join("claim.bin").exists() { "claim.bin" } else { "expected_claim.bin" };
    match std::fs::read(dir.join(claim_file)) {
        Ok(cb) => ok &= ex.clean && ex.claim.map(|c| c.encode()) == Some(cb),
        Err(_) => {
            let wb: usize = ex.witness_values.iter().map(|v| v.len()).sum();
            ok &= domain::check(&ex.request, &kv, wb).is_err();
        }
    }
    println!("{} {}", if ok { "REPLAY_OK" } else { "REPLAY_MISMATCH" }, dir.display());
    if ok { 0 } else { 1 }
}

fn cmd_params(args: &[String]) -> i32 {
    let out = arg(args, "--out");
    let d = runtime_config_json();
    let digest = hash(jcs(&d).as_bytes()).0;
    eprintln!("runtime_config_digest = sha256:{}", hex::encode(digest));
    let s = serde_json::to_string_pretty(&d).unwrap() + "\n";
    match out {
        Some(p) => std::fs::write(p, s).unwrap(),
        None => print!("{s}"),
    }
    0
}

fn runtime_config_json() -> serde_json::Value {
    use near_parameters::{ActionCosts, RuntimeConfigStore};
    let nc = Path::new(env!("CARGO_MANIFEST_DIR")).join("vendor/nearcore");
    let store = RuntimeConfigStore::new(None);
    let cfg = store.get_config(domain::PROTOCOL_VERSION);
    let nar = cfg.fees.fee(ActionCosts::new_action_receipt).exec_fee();
    let tr = cfg.fees.fee(ActionCosts::transfer).exec_fee();
    assert_eq!(nar.gas.as_gas() + tr.gas.as_gas(), domain::GAS_PER_TRANSFER);
    assert_eq!(nar.compute + tr.compute, domain::GAS_PER_TRANSFER);
    assert_eq!(cfg.storage_amount_per_byte().as_yoctonear(), domain::STORAGE_AMOUNT_PER_BYTE);
    let view = near_parameters::RuntimeConfigView::from(cfg.as_ref().clone());
    let view_bytes = serde_json::to_vec(&view).unwrap();
    // parameter files as used by RuntimeConfigStore::new(None): base + diffs <= PV
    let dir = nc.join("core/parameters/res/runtime_configs");
    let mut files: Vec<(u32, String)> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let n = e.unwrap().file_name().into_string().unwrap();
            n.strip_suffix(".yaml").and_then(|v| v.parse::<u32>().ok()).map(|v| (v, n))
        })
        .filter(|(v, _)| *v <= domain::PROTOCOL_VERSION)
        .collect();
    files.sort();
    let mut fl = vec![];
    let base = std::fs::read(dir.join("parameters.yaml")).unwrap();
    fl.push(json!({"path": "core/parameters/res/runtime_configs/parameters.yaml", "sha256": hex::encode(hash(&base).0)}));
    for (_, n) in &files {
        let b = std::fs::read(dir.join(n)).unwrap();
        fl.push(json!({"path": format!("core/parameters/res/runtime_configs/{n}"), "sha256": hex::encode(hash(&b).0)}));
    }
    let d = json!({
        "schema": "near-arena-runtime-config-v1",
        "nearcore_commit": NEARCORE_COMMIT,
        "protocol_version": domain::PROTOCOL_VERSION,
        "config_source": "near_parameters::RuntimeConfigStore::new(None).get_config(86) (mainnet parameters)",
        "parameter_files": fl,
        "runtime_config_view_json_sha256": hex::encode(hash(&view_bytes).0),
        "slice_parameters": {
            "new_action_receipt_exec_gas": nar.gas.as_gas(),
            "new_action_receipt_exec_compute": nar.compute,
            "transfer_exec_gas_named_receiver": tr.gas.as_gas(),
            "transfer_exec_compute_named_receiver": tr.compute,
            "gas_per_transfer_receipt": domain::GAS_PER_TRANSFER,
            "storage_amount_per_byte": cfg.storage_amount_per_byte().as_yoctonear().to_string(),
            "zero_balance_account_storage_limit": domain::ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT,
            "min_gas_purchase_price": cfg.min_gas_purchase_price.as_yoctonear().to_string(),
            "gas_refund_penalty": format!("{}/{}", cfg.fees.gas_refund_penalty.numer(), cfg.fees.gas_refund_penalty.denom()),
            "min_gas_refund_penalty": cfg.fees.min_gas_refund_penalty.as_gas(),
            "burnt_gas_reward": format!("{}/{}", cfg.fees.burnt_gas_reward.numer(), cfg.fees.burnt_gas_reward.denom()),
            "main_storage_proof_size_soft_limit": cfg.witness_config.main_storage_proof_size_soft_limit,
            "trie_costs": {"node_cost": 50, "byte_of_key": 2, "byte_of_value": 1},
        }
    });
    d
}

fn n_ok_total(nvalid: u64, ninvalid: u64, args: &[String]) -> u64 {
    nvalid + ninvalid + if args.iter().any(|a| a == "--with-example") { 2 } else { 0 }
}
