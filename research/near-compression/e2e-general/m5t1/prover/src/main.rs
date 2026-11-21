//! E2E lane F prover: the `rt` templates (enter `ENT`, resume = the M5-T1 runtime rows) on the main
//! PQ stack (lane B's harness, `../m5a/prover`, without the SHA-512 chip).
//!
//!   nearproof-e2e-m5t1 <air.json> <dump_dir> check|prove|mutant [out_dir]
//!
//! * the Lean AIR (`m5t1-tool air` / `air-ent`) is interpreted unchanged (`air.rs`): every
//!   constraint of `Table.allConstraints` and every interaction; the table names come from the
//!   dump's `tables.json` (default: the resume template's `SHA RNG SCHT MSG DG RX`);
//! * the `SHA` table's trace comes from the reference generator of `ZkFormal.Sha.Gen`
//!   (`sha256gen.rs`) over the dump's `sha_msgs.json`;
//! * `TAPE` (statement) and `XTAPE` (the T1 stand-ins for lanes A/B) are cached public tables, when
//!   the dump has them (the resume template; the enter template has none);
//! * the public values: the boundary pair (`BndLay.lean`: `BndRec.encode` bytes of `B_in`, `B_out`)
//!   and, for resume, the env / totals groups.
//!
//! **F-2 (pinned shape).** A dump with `template.json` (`{"params": {n_stack, log_blowup, w_stack,
//! pow_bits, degree}, "heights": {table: log}}`) is proved at lane D's base configuration
//! (`pq-chunk-e2e/src/profile.rs::shaped_params_geom`, non-final, `zk = 0`, first-order
//! certificates, list decoding m = 64, query grinding `pow_bits` = 24, `domain_odd_factor` 15, tight
//! heights floored to the full height) with every table at its pinned height (asserted), so one
//! template has one vk. `prove <out_dir>` saves `RT.proof` (`Proof::encode`), `RT.vk.json` (the
//! `SavedVk` envelope) and `statement.json` (per-AIR public values, heights, cached roots, and the
//! boundary digests `bdigest(B_in)`, `bdigest(B_out)` recomputed from the public values).
mod air;
#[allow(dead_code, clippy::all)]
mod sha384 {
    pub mod config;
    pub mod mb;
}
mod sha256gen;

use air::{ClassicalAir, E, JsonAir, TableSpec};
use openvm_cpu_backend::CpuBackend;
use openvm_stark_backend::{
    AirRef, CertSet, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    codec::Encode,
    interaction::LogUpSecurityParameters,
    keygen::types::MultiStarkVerifyingKey,
    prover::{AirProvingContext, ColMajorMatrix, CommittedTraceData, DeviceDataTransporter, ProvingContext},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use sha384::config::{F, Sha384Config, Sha384CpuEngine};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::Instant;

const RESUME: &[&str] = &["SHA", "RNG", "SCHT", "MSG", "DG", "RX"];
const P: u64 = 0x7800_0001;

fn set_levers() {
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = sha384::config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
}

/// The repo's first-order certificate set (`final-soundness/calc/dkt_certs_o2.json` minus the
/// exclusions `final-soundness/lean/DKTCertsO2_big.keys`), as `pq-chunk-e2e/src/profile.rs` reads it.
fn certs(cert_file: &str, exclusions: &str) -> CertSet {
    let parse = |s: &str| -> Option<(u64, u64, u64)> {
        let a: Vec<_> = s.trim().split(',').collect();
        if a.len() != 4 || a[3] != "1" {
            return None;
        }
        Some((a[0].parse().ok()?, a[1].parse().ok()?, a[2].parse().ok()?))
    };
    let v: serde_json::Value = serde_json::from_slice(&std::fs::read(cert_file).expect("cert file")).unwrap();
    let mut c: CertSet = v.as_object().unwrap().keys().filter_map(|k| parse(k)).collect();
    for l in std::fs::read_to_string(exclusions).expect("exclusions").lines() {
        if let Some(x) = parse(l) {
            c.remove(&x);
        }
    }
    assert!(!c.is_empty(), "no kernel-backed certificates");
    c
}

/// Lane D's base configuration (`shaped_params_geom`, non-final, `zk = 0`) at the template's
/// geometry, with the segment grinding `pow_bits` (24: lane D-8, "the segment prover's grinding
/// stays at 2^24"; never 32 with seg-v1, review-D8 I5). As lane B's B-T1 `base_params`.
fn base_params(n_stack: usize, log_blowup: usize, w_stack: usize, degree: usize, pow_bits: usize, cert_file: &str, exclusions: &str) -> SystemParams {
    let (l_skip, k) = (2, 4);
    assert!(l_skip + n_stack + log_blowup <= 27, "beyond the BabyBear two-adic domain");
    let extra = (l_skip + n_stack).saturating_sub(20);
    let levers = WhirLevers {
        k_first: 2,
        multiproof: true,
        keep_domain: true,
        gruen_gkr: true,
        gkr_derive_claims: true,
        next_mask: true,
        gruen_zerocheck: true,
        wide_query_pow: true,
        tight_heights: true,
        whir_y: true,
        zk: 0,
    };
    let cs = certs(cert_file, exclusions);
    let whir = WhirConfig::new_full(
        log_blowup,
        l_skip + n_stack,
        WhirParams {
            k,
            log_final_poly_len: 6 + extra,
            query_phase_pow_bits: pow_bits,
            folding_pow_bits: 0,
            mu_pow_bits: 0,
            proximity: WhirProximityStrategy::ListDecoding { m: 64 },
        },
        268,
        levers,
        15,
    )
    .with_first_order(log_blowup, l_skip + n_stack, 268, 50, 64, Some(&cs), 2);
    SystemParams {
        l_skip,
        n_stack,
        w_stack,
        log_blowup,
        whir,
        logup: LogUpSecurityParameters { max_interaction_count: 1 << 30, log_max_message_length: 7, pow_bits: 0 },
        max_constraint_degree: degree,
    }
}

/// seg-v1 shape (pq-state-port) with log message length 6 and the interaction budget 2^30 (the
/// M5-T1 measurement; not a template).
fn params(n_stack: usize, w_stack: usize, max_degree: usize) -> SystemParams {
    let (l_skip, log_blowup, k, k1, lf) = (2, 1, 4, 1, 7);
    let log_h = l_skip + n_stack;
    assert_eq!((log_h - k1 - lf) % k, 0, "n_stack must be 10, 14, 18 or 22");
    let levers = WhirLevers { k_first: k1, multiproof: true, keep_domain: true, whir_y: true, ..Default::default() };
    let whir = WhirConfig::new_full(
        log_blowup,
        log_h,
        WhirParams {
            k,
            log_final_poly_len: lf,
            query_phase_pow_bits: 24,
            proximity: WhirProximityStrategy::ListDecoding { m: 16 },
            folding_pow_bits: 0,
            mu_pow_bits: 0,
        },
        268,
        levers,
        1,
    );
    SystemParams {
        l_skip,
        n_stack,
        w_stack,
        log_blowup,
        whir,
        logup: LogUpSecurityParameters { max_interaction_count: 1 << 30, log_max_message_length: 6, pow_bits: 0 },
        max_constraint_degree: max_degree,
    }
}

fn deg(e: &E) -> usize {
    match e {
        E::C(_) | E::P(_) => 0,
        E::Col(..) | E::First | E::Last | E::Trans => 1,
        E::Add(a, b) => deg(a).max(deg(b)),
        E::Mul(a, b) => deg(a) + deg(b),
        E::Neg(a) => deg(a),
    }
}

fn read_trace(path: &std::path::Path) -> RowMajorMatrix<F> {
    let b = std::fs::read(path).unwrap_or_else(|e| panic!("{path:?}: {e}"));
    let u = |i: usize| u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap());
    let (log, w) = (u(0) as usize, u(1) as usize);
    let n = (1usize << log) * w;
    assert_eq!(b.len(), 8 + 4 * n, "{path:?}: size");
    RowMajorMatrix::new((0..n).map(|i| F::new(u(2 + i))).collect(), w)
}

type Key = (u16, Vec<u32>);

fn add(map: &mut BTreeMap<Key, u64>, k: Key, c: u64) {
    let e = map.entry(k).or_insert(0);
    *e = (*e + c) % P;
}

fn sel(r: usize, h: usize) -> [F; 3] {
    [
        if r == 0 { F::ONE } else { F::ZERO },
        if r + 1 == h { F::ONE } else { F::ZERO },
        if r + 1 == h { F::ZERO } else { F::ONE },
    ]
}

fn traffic(t: &TableSpec, m: &RowMajorMatrix<F>, pubs: &[F], map: &mut BTreeMap<Key, u64>) {
    let w = m.width;
    let h = m.values.len() / w;
    for r in 0..h {
        let cur = &m.values[r * w..(r + 1) * w];
        let nxt = &m.values[((r + 1) % h) * w..((r + 1) % h + 1) * w];
        let s = sel(r, h);
        for i in &t.inters {
            let mut c = F::ZERO;
            for (k, b) in i.mult.iter().enumerate() {
                c += b.eval_f(cur, nxt, pubs, s) * F::from_u64(1 << k);
            }
            if c == F::ZERO {
                continue;
            }
            let msg: Vec<u32> = i.msg.iter().map(|e| e.eval_f(cur, nxt, pubs, s).as_canonical_u32()).collect();
            let c = c.as_canonical_u32() as u64;
            add(map, (i.bus, msg), if i.send { c } else { (P - c) % P });
        }
    }
}

fn check_constraints(t: &TableSpec, m: &RowMajorMatrix<F>, pubs: &[F]) -> Result<(), String> {
    let w = m.width;
    let h = m.values.len() / w;
    for r in 0..h {
        let cur = &m.values[r * w..(r + 1) * w];
        let nxt = &m.values[((r + 1) % h) * w..((r + 1) % h + 1) * w];
        for (ci, c) in t.constraints.iter().enumerate() {
            if c.eval_f(cur, nxt, pubs, sel(r, h)) != F::ZERO {
                return Err(format!("{}: constraint {ci} fails on row {r}", t.name));
            }
        }
    }
    Ok(())
}

/// A harness table: one row per (key, net count); columns msg[0..W), cnt, sel[k].
fn harness(name: &str, map: &BTreeMap<Key, u64>, cached: bool) -> (TableSpec, RowMajorMatrix<F>) {
    let keys: Vec<(u16, usize)> = map.keys().map(|(b, m)| (*b, m.len())).collect::<BTreeSet<_>>().into_iter().collect();
    let wmsg = keys.iter().map(|k| k.1).max().unwrap_or(1).max(1);
    let width = wmsg + 1 + keys.len().max(1);
    let rows = map.iter().filter(|(_, c)| **c != 0).count();
    let h = rows.next_power_of_two().max(4);
    let mut v = vec![F::ZERO; h * width];
    for (r, ((b, m), c)) in map.iter().filter(|(_, c)| **c != 0).enumerate() {
        let row = &mut v[r * width..(r + 1) * width];
        for (j, x) in m.iter().enumerate() {
            row[j] = F::new(*x);
        }
        row[wmsg] = F::new(*c as u32);
        let k = keys.iter().position(|k| *k == (*b, m.len())).unwrap();
        row[wmsg + 1 + k] = F::ONE;
    }
    let spec = TableSpec {
        name: name.into(),
        width,
        max_log: 22,
        constraints: vec![],
        inters: vec![],
        harness: Some((wmsg, keys)),
        cached,
        num_pub: 0,
        prep: None,
    };
    (spec, RowMajorMatrix::new(v, width))
}

fn pad_rows(m: &RowMajorMatrix<F>, name: &str, log: usize) -> RowMajorMatrix<F> {
    let h = m.values.len() / m.width;
    assert!(h <= 1 << log, "{name}: {h} rows exceed the template's 2^{log}");
    let mut v = m.values.clone();
    v.resize((1 << log) * m.width, F::ZERO);
    RowMajorMatrix::new(v, m.width)
}

struct Inst {
    spec: Vec<TableSpec>,
    mats: Vec<RowMajorMatrix<F>>,
    pubs: Vec<F>,
    /// the statement tape and the T1 stand-in tape (public), as net message counts
    tapes: Vec<(String, BTreeMap<Key, u64>)>,
    tmpl: Option<serde_json::Value>,
}

fn pin_of(tmpl: &Option<serde_json::Value>, table: &str) -> Option<usize> {
    tmpl.as_ref().and_then(|t| t["heights"][table].as_u64()).map(|x| x as usize)
}

fn read_tape(path: &std::path::Path) -> Option<BTreeMap<Key, u64>> {
    let txt = std::fs::read_to_string(path).ok()?;
    let pm: serde_json::Value = serde_json::from_str(&txt).unwrap();
    let mut tape = BTreeMap::new();
    for x in pm.as_array().unwrap() {
        let bus = x[0].as_u64().unwrap() as u16;
        let send = x[1].as_bool().unwrap();
        let msg: Vec<u32> = x[2].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as u32).collect();
        add(&mut tape, (bus, msg), if send { 1 } else { P - 1 });
    }
    Some(tape)
}

fn load(air_path: &str, dir: &str) -> Inst {
    let text = std::fs::read_to_string(air_path).unwrap();
    let d = std::path::Path::new(dir);
    let tnames: Option<Vec<String>> =
        std::fs::read_to_string(d.join("tables.json")).ok().map(|t| serde_json::from_str(&t).expect("tables.json"));
    let tmpl: Option<serde_json::Value> =
        std::fs::read_to_string(d.join("template.json")).ok().map(|t| serde_json::from_str(&t).expect("template.json"));
    let owned: Vec<&str>;
    let names: &[&str] = if let Some(v) = &tnames {
        owned = v.iter().map(|x| x.as_str()).collect();
        &owned
    } else {
        RESUME
    };
    let cl = ClassicalAir::parse(&text, names);
    assert_eq!(cl.tables.len(), names.len());
    let pb = std::fs::read(d.join("pubs.bin")).unwrap();
    let pubs: Vec<F> = pb.chunks(4).map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap()))).collect();
    let (mut spec, mut mats) = (vec![], vec![]);
    for t in cl.tables.iter() {
        let mut m = if t.name == "SHA" {
            let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(d.join("sha_msgs.json")).unwrap()).unwrap();
            let msgs: Vec<sha256gen::Msg> = v
                .as_array()
                .unwrap()
                .iter()
                .map(|x| {
                    let hx = x["bytes"].as_str().unwrap();
                    let bytes = (0..hx.len() / 2).map(|i| u8::from_str_radix(&hx[2 * i..2 * i + 2], 16).unwrap()).collect();
                    sha256gen::Msg { id: x["id"].as_u64().unwrap() as u32, bytes, dmult: true }
                })
                .collect();
            let (cells, _nrows, _log) = sha256gen::sha_cells_pinned(&msgs, pin_of(&tmpl, &t.name));
            RowMajorMatrix::new(cells.iter().map(|&x| F::new(x as u32)).collect(), sha256gen::WIDTH)
        } else {
            read_trace(&d.join(format!("{}.bin", t.name)))
        };
        assert_eq!(m.width, t.width, "{}: width", t.name);
        if let Some(p) = pin_of(&tmpl, &t.name) {
            // the Lean tables accept zero padding rows (activity is a prefix; RNG is fixed at 2^8)
            m = pad_rows(&m, &t.name, p);
        }
        let h = m.values.len() / m.width;
        assert!(h.is_power_of_two() && h >= 4, "{}: height {h}", t.name);
        assert!(h.trailing_zeros() as usize <= t.max_log, "{}: maxLog", t.name);
        if let Some(p) = pin_of(&tmpl, &t.name) {
            assert_eq!(h, 1 << p, "{}: height differs from the template pin", t.name);
        } else if tmpl.is_some() {
            panic!("{}: no pinned height in template.json", t.name);
        }
        let mut t = t.clone();
        if t.name == "SCHT" {
            // [F-2] the schema entries are the preprocessed columns: the rows of `Scht.row` (the
            // schema's entries in order, then the last one repeated); the dump must agree
            let sp = std::path::Path::new(air_path).with_file_name("schema.json");
            let sch: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(sp).expect("schema.json next to the AIR")).unwrap();
            let ent = sch["entries"].as_array().unwrap();
            let ne = ent[0].as_array().unwrap().len();
            let mut v = vec![];
            for r in 0..h {
                let e = ent[r.min(ent.len() - 1)].as_array().unwrap();
                for (j, x) in e.iter().enumerate() {
                    let x = x.as_u64().unwrap() as u32;
                    assert_eq!(m.values[r * m.width + j], F::new(x), "SCHT row {r} col {j}: not the schema");
                    v.push(x);
                }
            }
            t.prep = Some((ne, v));
        }
        spec.push(t);
        mats.push(m);
    }
    let mut tapes = vec![];
    for name in ["TAPE", "XTAPE"] {
        if let Some(tape) = read_tape(&d.join(format!("{}.json", name.to_lowercase()))) {
            let (ts, mut tm) = harness(name, &tape, true);
            if let Some(p) = pin_of(&tmpl, name) {
                tm = pad_rows(&tm, name, p);
            } else if tmpl.is_some() {
                panic!("{name}: no pinned height in template.json");
            }
            spec.push(ts);
            mats.push(tm);
            tapes.push((name.to_string(), tape));
        }
    }
    Inst { spec, mats, pubs, tapes, tmpl }
}

fn precheck(inst: &Inst) -> Result<(), String> {
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if t.harness.is_none() {
            check_constraints(t, m, &inst.pubs)?;
        }
    }
    let mut net = BTreeMap::new();
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if t.harness.is_none() {
            traffic(t, m, &inst.pubs, &mut net);
        }
    }
    for (_, tape) in &inst.tapes {
        for (k, c) in tape.iter() {
            add(&mut net, k.clone(), *c);
        }
    }
    let bad: Vec<_> = net.iter().filter(|(_, c)| **c != 0).collect();
    if !bad.is_empty() {
        let mut by_bus: BTreeMap<u16, usize> = BTreeMap::new();
        for ((b, _), _) in &bad {
            *by_bus.entry(*b).or_default() += 1;
        }
        return Err(format!("{} unbalanced messages by bus {:?}; first {:?}", bad.len(), by_bus, &bad[..bad.len().min(3)]));
    }
    println!("PRECHECK OK: every constraint on every row; every bus balances ({} distinct messages)", net.len());
    Ok(())
}

fn airs(inst: &Inst) -> Vec<AirRef<Sha384Config>> {
    inst.spec.iter().map(|t| Arc::new(JsonAir { spec: t.clone() }) as AirRef<Sha384Config>).collect()
}

/// The commitment of a cached table (full height, no tight heights).
fn commit_cached(eng: &Sha384CpuEngine, m: &RowMajorMatrix<F>) -> (sha384::config::Digest, openvm_stark_backend::prover::stacked_pcs::StackedPcsData<F, sha384::config::Digest>) {
    use openvm_stark_backend::StarkProtocolConfig;
    let c = eng.config();
    let p = c.params();
    openvm_stark_backend::prover::stacked_pcs::stacked_commit_odd(
        c.hasher(),
        p.l_skip,
        p.n_stack,
        p.log_blowup,
        p.whir.k_first(),
        p.whir.domain_odd_factor,
        &[&ColMajorMatrix::from_row_major(m)],
        false,
    )
    .expect("cached commitment")
}

fn ctx(eng: &Sha384CpuEngine, inst: &Inst, mats: &[RowMajorMatrix<F>], pubs: &[F]) -> ProvingContext<CpuBackend<Sha384Config>> {
    let mut out = vec![];
    for (i, m) in mats.iter().enumerate() {
        let t = &inst.spec[i];
        let pv: Vec<F> = (0..t.num_pub).map(|k| pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        if let Some((pw, _)) = &t.prep {
            let w = m.width;
            let h = m.values.len() / w;
            let main: Vec<F> = (0..h).flat_map(|r| m.values[r * w + pw..(r + 1) * w].to_vec()).collect();
            out.push((i, AirProvingContext::simple(RowMajorMatrix::new(main, w - pw), pv)));
        } else if !t.cached {
            out.push((i, AirProvingContext::simple(m.clone(), pv)));
        } else {
            let (commitment, data) = commit_cached(eng, m);
            let cached = CommittedTraceData { commitment, trace: m.clone(), data: Arc::new(data) };
            let h = m.values.len() / m.width;
            let empty = RowMajorMatrix::new(vec![F::ZERO; h], 1);
            out.push((i, AirProvingContext { cached_mains: vec![cached], common_main: empty, public_values: pv }));
        }
    }
    ProvingContext::new(out)
}

/// The tight-height floor of a pinned template: every common main commits its full height.
fn full_floor(inst: &Inst) -> Vec<(usize, usize, usize)> {
    inst.spec
        .iter()
        .zip(&inst.mats)
        .map(|(t, m)| {
            let h = m.values.len() / m.width;
            (if t.cached { 1 } else { m.width - t.prep.as_ref().map(|p| p.0).unwrap_or(0) }, h.trailing_zeros() as usize, h)
        })
        .collect()
}

/// The verifier's statement check: each tape's commitment equals the one it recomputes from the
/// public messages, and the public values are the statement's.
fn check_statement(eng: &Sha384CpuEngine, inst: &Inst, want_pubs: &[F], proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> bool {
    let mut ok = true;
    for (name, tape) in &inst.tapes {
        let ti = inst.spec.iter().position(|t| &t.name == name).unwrap();
        let (_, mut tm) = harness(name, tape, true);
        if let Some(p) = pin_of(&inst.tmpl, name) {
            tm = pad_rows(&tm, name, p);
        }
        let want = commit_cached(eng, &tm).0;
        ok &= matches!(&proof.trace_vdata[ti], Some(v) if v.cached_commitments.len() == 1 && v.cached_commitments[0] == want);
    }
    let pv_ok = inst.spec.iter().enumerate().all(|(i, t)| {
        let pv: Vec<F> = (0..t.num_pub).map(|k| want_pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        proof.public_values[i] == pv
    });
    ok && pv_ok
}

// Upstream skips the extended-domain factor in VK serde; `pq-chunk-e2e` keeps it in an envelope.
#[derive(serde::Serialize)]
struct SavedVk<'a> {
    domain_odd_factor: usize,
    vk: &'a MultiStarkVerifyingKey<Sha384Config>,
}

/// `bdigest`: SHA-384 truncated to 42 bytes (lane E `Bnd.bdigest`).
fn bdigest(b: &[u8]) -> String {
    use sha2::Digest as _;
    let d = sha2::Sha384::digest(b);
    d[..42].iter().map(|x| format!("{x:02x}")).collect()
}

/// Save the proof and vk in the stack's format, and the statement (every AIR's public values,
/// `(log_height, tight_height)`, cached roots; the boundary digests from the public values).
fn save(out: &std::path::Path, inst: &Inst, vk: &MultiStarkVerifyingKey<Sha384Config>, proof: &openvm_stark_backend::proof::Proof<Sha384Config>, sz: usize, bnd: (usize, usize, usize)) {
    use sha2::Digest as _;
    std::fs::create_dir_all(out).unwrap();
    let mut b = vec![];
    proof.encode(&mut b).unwrap();
    assert_eq!(b.len(), sz);
    std::fs::write(out.join("RT.proof"), &b).unwrap();
    let vkb = serde_json::to_vec(&SavedVk { domain_odd_factor: vk.inner.params.whir.domain_odd_factor, vk }).unwrap();
    std::fs::write(out.join("RT.vk.json"), &vkb).unwrap();
    let airs: Vec<serde_json::Value> = inst
        .spec
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let v = proof.trace_vdata[i].as_ref();
            serde_json::json!({
                "name": t.name,
                "num_public_values": proof.public_values[i].len(),
                "log_height": v.map(|v| v.log_height),
                "tight_height": v.and_then(|v| v.tight_height),
                "cached_roots": v.map(|v| v.cached_commitments.iter().map(|c| format!("{c:?}")).collect::<Vec<_>>()),
            })
        })
        .collect();
    let (o, n_in, n_out) = bnd;
    let pbytes = |a: usize, n: usize| -> Vec<u8> { inst.pubs[a..a + n].iter().map(|x| x.as_canonical_u32() as u8).collect() };
    let st = serde_json::json!({
        "template": inst.tmpl,
        "proof_bytes": sz,
        "proof_sha256": format!("{:x}", sha2::Sha256::digest(&b)),
        "vk_sha256": format!("{:x}", sha2::Sha256::digest(&vkb)),
        "vk_pre_hash": format!("{:?}", vk.pre_hash),
        "d_in": bdigest(&pbytes(o, n_in)),
        "d_out": bdigest(&pbytes(o + n_in, n_out)),
        "public_values": inst.pubs.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
        "airs": airs,
    });
    std::fs::write(out.join("statement.json"), serde_json::to_vec_pretty(&st).unwrap()).unwrap();
    println!("SAVED {} (RT.proof {sz} B, RT.vk.json {} B); boundary d_in {} d_out {}", out.display(), vkb.len(), st["d_in"], st["d_out"]);
}

fn census(proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> (usize, String) {
    fn size<T: Encode>(x: &T) -> usize {
        let mut b = Vec::new();
        x.encode(&mut b).unwrap();
        b.len()
    }
    let lv = proof.whir_proof.levers;
    let (mut gk, mut rl) = (Vec::new(), Vec::new());
    proof.gkr_proof.encode_levers(&lv, &mut gk).unwrap();
    proof.batch_constraint_proof.encode_levers(&mut rl).unwrap();
    (
        size(proof),
        format!(
            "total={} gkr={} relations={} stacking={} whir={}",
            size(proof),
            gk.len(),
            rl.len(),
            size(&proof.stacking_proof),
            size(&proof.whir_proof)
        ),
    )
}

fn peak_rss_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).map(|l| l.split_whitespace().nth(1).unwrap().parse().unwrap()))
        .unwrap_or(0)
}

fn report(inst: &Inst) {
    let mut cells = 0usize;
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        let h = m.values.len() / m.width;
        cells += h * m.width;
        let d = t.constraints.iter().map(deg).max().unwrap_or(0);
        let ni = t.harness.as_ref().map(|h| h.1.len()).unwrap_or(t.inters.len());
        println!(
            "TABLE {:<6} width {:>5} height 2^{:<2} cells {:>9} constraints {:>5} interactions {:>5} deg {}",
            t.name, m.width, h.trailing_zeros(), h * m.width, t.constraints.len(), ni, d
        );
    }
    let pinned: Vec<String> = inst.spec.iter().zip(&inst.mats).map(|(t, m)| format!("\"{}\": {}", t.name, (m.values.len() / m.width).trailing_zeros())).collect();
    println!("HEIGHTS {{{}}}", pinned.join(", "));
    println!("CELLS committed {cells}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: {} <air.json> <dump_dir> check|prove|mutant [out_dir]", args[0]);
        std::process::exit(2);
    }
    let (air_path, dir, mode) = (&args[1], &args[2], args[3].as_str());
    set_levers();
    let t0 = Instant::now();
    let inst = load(air_path, dir);
    report(&inst);
    let pre = precheck(&inst);
    println!("TIME load+precheck {:.2}s", t0.elapsed().as_secs_f64());
    match (&pre, mode) {
        (Err(e), "mutant") => println!("PRECHECK FAIL: {e}"),
        (Err(e), _) => panic!("precheck: {e}"),
        _ => {}
    }
    if mode == "check" {
        return;
    }
    let total: usize = inst.mats.iter().map(|m| m.values.len()).sum();
    let maxh = inst.mats.iter().map(|m| m.values.len() / m.width).max().unwrap();
    let degree = inst.spec.iter().flat_map(|t| t.constraints.iter().map(deg)).max().unwrap_or(2).max(2);
    let prm = if let Some(t) = &inst.tmpl {
        let g = |k: &str| t["params"][k].as_u64().unwrap_or_else(|| panic!("template params.{k}")) as usize;
        let root = std::env::var("NEARPROOF_ROOT").unwrap_or_else(|_| "/data/illia/nearproof".into());
        let cert = std::env::var("NEARPROOF_CERTS").unwrap_or_else(|_| format!("{root}/research/near-compression/final-soundness/calc/dkt_certs_o2.json"));
        let excl = std::env::var("NEARPROOF_EXCL").unwrap_or_else(|_| format!("{root}/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys"));
        assert_eq!(g("degree"), degree, "template degree");
        base_params(g("n_stack"), g("log_blowup"), g("w_stack"), degree, g("pow_bits"), &cert, &excl)
    } else {
        let n_stack = [14usize, 18, 22].into_iter().find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24).unwrap_or(22);
        let w_stack = (total.div_ceil(1 << (n_stack + 2)) + 4).max(8);
        params(n_stack, w_stack, degree)
    };
    println!(
        "PARAMS n_stack {} w_stack {} log_blowup {} degree {} pow {} queries {:?}",
        prm.n_stack,
        prm.w_stack,
        prm.log_blowup,
        prm.max_constraint_degree,
        prm.whir.query_phase_pow_bits,
        prm.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>()
    );
    let eng = Sha384CpuEngine::new(prm);
    let airs = airs(&inst);
    let t1 = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    println!("TIME keygen {:.2}s", t1.elapsed().as_secs_f64());
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!("SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}", b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits);
    let d_pk = eng.device().transport_pk_to_device(&pk);
    if inst.tmpl.is_some() {
        openvm_stark_backend::prover::stacked_pcs::set_tight_floor(Some(full_floor(&inst)));
    }
    let t2 = Instant::now();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let p = eng.prove(&d_pk, ctx(&eng, &inst, &inst.mats, &inst.pubs)).ok()?;
        Some(p)
    }));
    let t_prove = t2.elapsed().as_secs_f64();
    let proof = match r {
        Ok(Some(p)) => p,
        Ok(None) => {
            println!("REJECTED (prover error) after {t_prove:.1}s");
            assert!(mode == "mutant");
            return;
        }
        Err(_) => {
            println!("REJECTED (prover panicked) after {t_prove:.1}s");
            assert!(mode == "mutant");
            return;
        }
    };
    let t3 = Instant::now();
    let ver = eng.verify(&vk, &proof);
    let t_verify = t3.elapsed().as_secs_f64();
    let (sz, cs) = census(&proof);
    println!("PROOF {cs}");
    // the statement: the Lean run's public values (`expected_pubs.bin`, independent of a mutant's
    // claimed ones) and the tapes
    let want_pubs: Vec<F> = match std::fs::read(std::path::Path::new(dir).join("expected_pubs.bin")) {
        Ok(pb) => pb.chunks(4).map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap()))).collect(),
        Err(_) => inst.pubs.clone(),
    };
    let st = check_statement(&eng, &inst, &want_pubs, &proof);
    println!("TIME prove {t_prove:.2}s verify {t_verify:.4}s threads {} peak_rss_kib {} proof_bytes {sz}", std::env::var("RAYON_NUM_THREADS").unwrap_or_default(), peak_rss_kib());
    if let (true, true, Some(out)) = (ver.is_ok(), st, args.get(4)) {
        // the boundary pair's offset in the public values (`bnd.json`: [offset, |B_in|, |B_out|])
        let bnd: Vec<usize> = serde_json::from_str(&std::fs::read_to_string(std::path::Path::new(dir).join("bnd.json")).expect("bnd.json")).unwrap();
        save(std::path::Path::new(out), &inst, &vk, &proof, sz, (bnd[0], bnd[1], bnd[2]));
    }
    match (ver.is_ok(), st) {
        (true, true) => {
            println!("VERIFY OK (native SWIRL verifier); statement check (tape roots + public values): OK");
            if mode == "mutant" {
                println!("ACCEPTED");
            }
        }
        (false, _) => {
            println!("REJECTED (native verifier: {:?})", ver.err());
            assert!(mode == "mutant", "honest proof failed to verify");
        }
        (true, false) => {
            println!("REJECTED (statement check)");
            assert!(mode == "mutant");
        }
    }
}
