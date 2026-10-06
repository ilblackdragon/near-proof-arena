//! Arena (judge) layout for the D1 / D2 / D3 generators (`gen --fixtures-layout`, `arena-layout`).
//!
//! The D1/D2/D3 chain loops write the difftest layout (`DIR/d<k>/`, `DIR/ood/`, `DIR/mutants/`,
//! each case `{claim.bin, witness.bin, meta.json}`). This module converts such a directory into the
//! layout `runners/worker` `NearV3Oracle` and `arena check-local` read (as the D0 generator writes
//! it directly):
//!
//! * `cases/<n>/{request.bin, witness.bin, expected_claim.bin, meta.json}`: honest chunks with
//!   `expected_rel_d<k> = true` (nearcore's validator accepts and the classifier puts the chunk in
//!   D<k>) of the selected workload class; request = expected claim = `claim.bin` (in v3 the claim is
//!   the job). With `accepted_mutants`, nearcore-accepted in-domain mutants too (class `any` only).
//! * `rejections/<n>/{request.bin, witness.bin, meta.json}`: everything with
//!   `expected_rel_d<k> = false`: nearcore-rejected mutants and honest chunks outside D<k>.
//!
//! The workload class of an honest case is a function of its `meta.json` only ([`class_of`]), so
//! public fixtures, held-out sets and judge sampling agree on it. Positives are taken round-robin
//! over the chains (case names `<chain>-h<height>-s<shard>`, sorted), so a target of `n` spreads a
//! batch over the chain parameter sets. Nothing here changes the cases' bytes.

use serde_json::Value;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Workload classes of a domain (`spec/workloads/near-chunk-validation-d<k>/`).
pub fn classes(domain: &str) -> &'static [&'static str] {
    match domain {
        "d1" => &["d1-transfers", "d1-mixed", "d1-receipts"],
        "d2" => &["d2-epoch", "d2-queues", "d2-actions"],
        "d3" => &["d3-maxgas", "d3-callbacks", "d3-calls", "d3-nonwasm"],
        _ => &[],
    }
}

/// `G_α` = 2^22 · 822 756 (`NearSpecV3.D3.gAlpha`).
pub const G_ALPHA: u128 = (1u128 << 22) * 822_756;

fn num(v: &Value) -> u128 {
    match v {
        Value::Number(n) => n.as_u64().map(u128::from).unwrap_or(0),
        Value::String(s) => s.parse().unwrap_or(0),
        _ => 0,
    }
}

/// The workload class of an honest in-domain case (first match in the order of [`classes`]).
///
/// * D1: `d1-transfers` = the last chunk has transactions and every one succeeds (incl. local
///   self-transfers); `d1-mixed` = transactions of which at least one fails validation or is
///   skipped (the crafted validity classes); `d1-receipts` = no transactions (incoming Transfer
///   receipts, `new_transactions` only, missing chunks).
/// * D2: `d2-epoch` = the segment spans an epoch boundary or applies a `ValidatorAccountsUpdate`;
///   `d2-queues` = a non-empty delayed-receipt queue or outgoing buffer before or after the chunk;
///   `d2-actions` = everything else (every non-WASM action, refunds, data/yield receipts).
/// * D3: `d3-maxgas` = chunk function-call gas ≥ G_α / 2 (the max-G_α class); `d3-callbacks` =
///   callbacks (`promise_then` / joins / promise results); `d3-calls` = other chunks executing
///   ≥ 1 function call (storage, logs, returns, promises without callbacks); `d3-nonwasm` = D3
///   chunks that execute no WASM (D2 traffic around D3 state).
pub fn class_of(domain: &str, m: &Value) -> &'static str {
    let f = &m["features"];
    match domain {
        "d1" => {
            let tr: Vec<&str> =
                m["tx_results"].as_array().map(|a| a.iter().filter_map(|x| x.as_str()).collect()).unwrap_or_default();
            if tr.is_empty() {
                "d1-receipts"
            } else if tr.iter().all(|r| r.starts_with("success")) {
                "d1-transfers"
            } else {
                "d1-mixed"
            }
        }
        "d2" => {
            if num(&f["n_epochs"]) > 1 || num(&f["validator_updates"]) > 0 {
                "d2-epoch"
            } else if num(&f["delayed_queue_pre"]) > 0
                || num(&f["delayed_queue_post"]) > 0
                || num(&f["buffered_pre"]) > 0
                || num(&f["buffered_post"]) > 0
            {
                "d2-queues"
            } else {
                "d2-actions"
            }
        }
        "d3" => {
            if num(&f["fc_gas_burnt_for_function_call"]) * 2 >= G_ALPHA {
                "d3-maxgas"
            } else if num(&f["n_callbacks"]) > 0 {
                "d3-callbacks"
            } else if num(&f["n_function_calls"]) > 0 {
                "d3-calls"
            } else {
                "d3-nonwasm"
            }
        }
        _ => "any",
    }
}

#[derive(Clone, Debug)]
pub struct ArenaOpts {
    /// `d1`, `d2` or `d3`.
    pub domain: String,
    /// A class of [`classes`], or `any`.
    pub class: String,
    pub positive_target: usize,
    pub rejection_target: usize,
    pub no_positives: bool,
    pub accepted_mutants: bool,
    /// At most this many positives per chain (0 = no cap).
    pub per_chain_cap: usize,
}

fn read_meta(d: &Path) -> Option<Value> {
    serde_json::from_slice(&std::fs::read(d.join("meta.json")).ok()?).ok()
}

fn list(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|r| r.filter_map(|e| e.ok()).map(|e| e.path()).filter(|p| p.is_dir()).collect())
        .unwrap_or_default();
    v.sort();
    v
}

fn chain_of(p: &Path) -> String {
    p.file_name().and_then(|n| n.to_str()).and_then(|n| n.split('-').next()).unwrap_or("").to_string()
}

fn write(out: &Path, sub: &str, src: &Path, positive: bool, mut meta: Value, class: Option<&str>) {
    let name = src.file_name().unwrap();
    let d = out.join(sub).join(name);
    std::fs::create_dir_all(&d).unwrap();
    let claim = std::fs::read(src.join("claim.bin")).unwrap();
    std::fs::write(d.join("request.bin"), &claim).unwrap();
    if positive {
        std::fs::write(d.join("expected_claim.bin"), &claim).unwrap();
    }
    std::fs::copy(src.join("witness.bin"), d.join("witness.bin")).unwrap();
    if let Some(c) = class {
        meta["workload_class"] = Value::String(c.to_string());
    }
    std::fs::write(d.join("meta.json"), serde_json::to_string_pretty(&meta).unwrap()).unwrap();
}

/// Convert the difftest-layout directory `raw` into the arena layout under `out`; returns
/// (positives, rejections) written.
pub fn convert(raw: &Path, out: &Path, o: &ArenaOpts) -> (usize, usize) {
    let key = format!("expected_rel_{}", o.domain);
    std::fs::create_dir_all(out.join("cases")).unwrap();
    std::fs::create_dir_all(out.join("rejections")).unwrap();
    // positives: honest in-domain cases of the class, round-robin over chains
    let mut by_chain: BTreeMap<String, Vec<(PathBuf, Value, &'static str)>> = BTreeMap::new();
    let mut rejections: Vec<(PathBuf, Value)> = vec![];
    for p in list(&raw.join(&o.domain)) {
        let Some(m) = read_meta(&p) else { continue };
        if m[&key].as_bool() == Some(true) {
            let c = class_of(&o.domain, &m);
            if o.class == "any" || o.class == c {
                by_chain.entry(chain_of(&p)).or_default().push((p, m, c));
            }
        } else {
            rejections.push((p, m));
        }
    }
    let mut accepted_mutants = vec![];
    for sub in ["ood", "mutants"] {
        for p in list(&raw.join(sub)) {
            let Some(m) = read_meta(&p) else { continue };
            if m[&key].as_bool() == Some(true) {
                if sub == "mutants" && o.accepted_mutants && o.class == "any" {
                    accepted_mutants.push((p, m));
                }
            } else {
                rejections.push((p, m));
            }
        }
    }
    let mut pos = 0usize;
    if !o.no_positives {
        let mut queues: Vec<std::collections::VecDeque<_>> =
            by_chain.into_values().map(|v| v.into_iter().collect()).collect();
        let mut taken: Vec<usize> = vec![0; queues.len()];
        'outer: loop {
            let mut any = false;
            for (i, q) in queues.iter_mut().enumerate() {
                if o.per_chain_cap > 0 && taken[i] >= o.per_chain_cap {
                    continue;
                }
                if let Some((p, m, c)) = q.pop_front() {
                    any = true;
                    if o.positive_target > 0 && pos >= o.positive_target {
                        break 'outer;
                    }
                    write(out, "cases", &p, true, m, Some(c));
                    taken[i] += 1;
                    pos += 1;
                }
            }
            if !any {
                break;
            }
        }
        for (p, m) in accepted_mutants {
            write(out, "cases", &p, true, m, None);
            pos += 1;
        }
    }
    // rejections: alternate honest out-of-domain chunks and mutants (sorted within each kind)
    let (mut ood, mut mu): (Vec<_>, Vec<_>) =
        rejections.into_iter().partition(|(_, m)| m["kind"].as_str() == Some("honest"));
    ood.reverse();
    mu.reverse();
    let mut rej = 0usize;
    while o.rejection_target == 0 || rej < o.rejection_target {
        let x = if rej % 2 == 0 { ood.pop().or_else(|| mu.pop()) } else { mu.pop().or_else(|| ood.pop()) };
        let Some((p, m)) = x else { break };
        write(out, "rejections", &p, false, m, None);
        rej += 1;
    }
    (pos, rej)
}

/// `args` for the raw (difftest-layout) run of `gen --fixtures-layout`: `--out RAW`, without the
/// arena-only options.
pub fn raw_args(args: &[String], raw: &Path) -> Vec<String> {
    let with_value = ["--out", "--class", "--d0-target", "--rejection-target", "--per-chain-cap"];
    let flags = ["--fixtures-layout", "--no-positives", "--accepted-mutants"];
    let mut v = vec![];
    let mut i = 0;
    while i < args.len() {
        if with_value.contains(&args[i].as_str()) {
            i += 2;
            continue;
        }
        if !flags.contains(&args[i].as_str()) {
            v.push(args[i].clone());
        }
        i += 1;
    }
    v.push("--out".into());
    v.push(raw.display().to_string());
    v
}

/// Parse the arena options shared by `gen --fixtures-layout` and `arena-layout`.
pub fn opts_from_args(args: &[String], domain: &str) -> ArenaOpts {
    let arg = |n: &str| args.iter().position(|a| a == n).and_then(|i| args.get(i + 1).cloned());
    let flag = |n: &str| args.iter().any(|a| a == n);
    let num = |n: &str| arg(n).map(|v| v.parse().unwrap_or_else(|_| panic!("{n}: not a number: {v}"))).unwrap_or(0);
    let class = arg("--class").unwrap_or_else(|| "any".into());
    if class != "any" && !classes(domain).contains(&class.as_str()) {
        panic!("--class: unknown {domain} class {class} (classes: {:?})", classes(domain));
    }
    ArenaOpts {
        domain: domain.to_string(),
        class,
        positive_target: num("--d0-target"),
        rejection_target: num("--rejection-target"),
        no_positives: flag("--no-positives"),
        accepted_mutants: flag("--accepted-mutants"),
        per_chain_cap: num("--per-chain-cap"),
    }
}

/// `arena-layout --domain d<k> --in RAW --out DIR [--class C] [--d0-target N] [--rejection-target R]
/// [--no-positives] [--accepted-mutants] [--per-chain-cap K]`: convert an existing difftest-layout
/// corpus (public fixtures from a published corpus).
pub fn cmd_arena_layout(args: &[String]) -> i32 {
    let arg = |n: &str| args.iter().position(|a| a == n).and_then(|i| args.get(i + 1).cloned());
    let domain = arg("--domain").expect("--domain d1|d2|d3");
    let raw = PathBuf::from(arg("--in").expect("--in"));
    let out = PathBuf::from(arg("--out").expect("--out"));
    let o = opts_from_args(args, &domain);
    let (p, r) = convert(&raw, &out, &o);
    eprintln!("arena layout: {p} positive(s), {r} rejection(s) -> {}", out.display());
    let mut s = serde_json::json!({
        "domain": domain.to_uppercase(), "source": raw.display().to_string(),
        "arena_layout": {"class": o.class, "positives": p, "rejections": r, "d0_target": o.positive_target,
            "rejection_target": o.rejection_target, "accepted_mutants": o.accepted_mutants,
            "per_chain_cap": o.per_chain_cap},
    });
    if let Ok(src) = std::fs::read(raw.join("summary.json")) {
        if let Ok(v) = serde_json::from_slice::<Value>(&src) {
            s["source_summary"] = v;
        }
    }
    std::fs::write(out.join("summary.json"), serde_json::to_string_pretty(&s).unwrap()).unwrap();
    if o.positive_target > 0 && p < o.positive_target || o.rejection_target > 0 && r < o.rejection_target {
        eprintln!("ERROR: targets not reached");
        return 3;
    }
    0
}

/// `gen ... --fixtures-layout`: run the difftest-layout generator into `OUT/.raw`, convert, and
/// remove the raw output. `run` gets the raw directory and returns the generator's exit code.
pub fn gen_fixtures(args: &[String], domain: &str, run: impl FnOnce(&Path) -> i32) -> i32 {
    let arg = |n: &str| args.iter().position(|a| a == n).and_then(|i| args.get(i + 1).cloned());
    let out = PathBuf::from(arg("--out").expect("--out"));
    let o = opts_from_args(args, domain);
    let raw = out.join(".raw");
    let _ = std::fs::remove_dir_all(&raw);
    std::fs::create_dir_all(&raw).unwrap();
    let code = run(&raw);
    if code != 0 {
        return code;
    }
    let (p, r) = convert(&raw, &out, &o);
    let mut s: Value = std::fs::read(raw.join("summary.json"))
        .ok()
        .and_then(|b| serde_json::from_slice(&b).ok())
        .unwrap_or(Value::Null);
    if !s.is_object() {
        s = serde_json::json!({});
    }
    s["arena_layout"] = serde_json::json!({
        "class": o.class, "positives": p, "rejections": r, "d0_target": o.positive_target,
        "rejection_target": o.rejection_target, "accepted_mutants": o.accepted_mutants,
        "per_chain_cap": o.per_chain_cap,
    });
    std::fs::write(out.join("summary.json"), serde_json::to_string_pretty(&s).unwrap()).unwrap();
    let _ = std::fs::remove_dir_all(&raw);
    if p < o.positive_target || r < o.rejection_target {
        eprintln!("arena layout: {p} positive(s) (target {}), {r} rejection(s) (target {})", o.positive_target, o.rejection_target);
        return 3;
    }
    0
}
