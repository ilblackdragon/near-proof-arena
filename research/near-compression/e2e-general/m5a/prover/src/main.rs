//! E2E M5a prover: INTAKE + working-set tree + FINAL of one transition, on the main PQ stack.
//!
//!   nearproof-e2e-m5a <m5a.json> <dump_dir> check|prove|mutant
//!
//! * the Lean AIR (`m5a-tool air`) is interpreted unchanged (`air.rs`, the pq-state-port
//!   interpreter): every constraint of `Table.allConstraints` and every interaction;
//! * the `SHA` table's trace comes from the reference generator of `ZkFormal.Sha.Gen`
//!   (`sha256gen.rs`) over the dump's `sha_msgs.json`;
//! * the SHA-512 compression chip (`s384/`, native v4, the recursion chip) proves the dump's
//!   `comps.json`; the Lean bus `IF384` (16) is its interface bus (103);
//! * `TAPE` is the public tape (cached, committed by the verifier from the statement): the write
//!   log and the trie-root chain's ends `(0, prev_state_root)`, `(n, post_state_root)`.
//!
//! `check`: constraints + bus balance only.  `prove`: precheck, keygen, prove, native verify,
//! statement check.  `mutant`: the same without the precheck assertion; prints `REJECTED (…)` or
//! `ACCEPTED`.
//!
//! **B-T1 (templates).** A dump written by `tracegen.py --split` names its tables (`tables.json`)
//! and, with `--template`, carries `template.json`: the template's pinned per-table heights and its
//! parameters (lane D's base configuration: first-order certificates, list decoding m = 64, query
//! grinding 24 bits, `domain_odd_factor` 15, tight heights floored to the full height).  Every
//! table is padded to its pinned height, so one template has one vk and one shape.  `prove
//! <out_dir>` then saves the proof and vk in the stack's format (`STATE.proof`: `Proof::encode`;
//! `STATE.vk.json`: the `SavedVk` envelope with `domain_odd_factor`, as `pq-chunk-e2e` reads them)
//! and `statement.json` (per-AIR public values, cached roots, heights).
mod air;
#[allow(dead_code, clippy::all)]
mod sha384 {
    pub mod config;
    pub mod mb;
}
mod sha256gen;
#[allow(dead_code, clippy::all)]
mod s384 {
    pub mod air;
    pub mod reference;
    pub mod trace;
}

use air::{ClassicalAir, E, JsonAir, TableSpec};
use openvm_cpu_backend::CpuBackend;
use sha384::config::{F, Sha384Config, Sha384CpuEngine};
use openvm_stark_backend::{
    AirRef, CertSet, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    codec::Encode,
    interaction::LogUpSecurityParameters,
    keygen::types::MultiStarkVerifyingKey,
    prover::{AirProvingContext, ColMajorMatrix, CommittedTraceData, DeviceDataTransporter, ProvingContext},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::Instant;

const NAMES: &[&str] = &["SHA", "KEY", "BR", "SN", "KCMP", "WSB", "WSN", "WSA", "SNC", "RNG", "WSL", "WSP"];
/// M5b (`m5a-tool airb`): the M5a tables plus the STATE rows.
const NAMES_B: &[&str] =
    &["SHA", "KEY", "BR", "SN", "KCMP", "WSB", "WSN", "WSA", "SNC", "RNG", "WSL", "WSP", "SHAS", "STB", "STW"];
/// M5b after M5a-8: the STATE messages are hashed by the M5a `SHA` table (no `SHAS`; tracegen then
/// puts them in `sha_msgs.json`).
const NAMES_B8: &[&str] =
    &["SHA", "KEY", "BR", "SN", "KCMP", "WSB", "WSN", "WSA", "SNC", "RNG", "WSL", "WSP", "STB", "STW"];
const P: u64 = 0x7800_0001;
/// The execution side's buses (`St.lean`): `SREQ`, `HB`.
const B_SREQ: u16 = 28;
const B_HB: u16 = 29;
/// [B-T3] the cross-lane `stRoot` buses (`Stc.B_STMQ` / `B_STMA`)
const B_STMQ: u16 = 211;
const B_STMA: u16 = 212;
const LEAN_IF: u16 = 16;

fn set_levers() {
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = sha384::config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
}

fn map_bus(b: u16) -> u16 {
    if b == LEAN_IF { s384::air::BUS_IF } else { b }
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

/// [B-T1] Lane D's base configuration (`pq-chunk-e2e/src/profile.rs::shaped_params_geom`, non-final,
/// `zk = 0`: segments are inner tree children, plan §5.0.1 (2)) at the template's geometry, with the
/// segment grinding `pow_bits` (24, lane D-8: "the segment prover's grinding stays at 2^24").
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

/// seg-v1 shape (pq-state-port) with log message length 6 and the interaction budget 2^30.
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
    let mut keys: Vec<(u16, usize)> = map.keys().map(|(b, m)| (*b, m.len())).collect::<BTreeSet<_>>().into_iter().collect();
    // [B-T1] the execution side's message kinds are fixed per table, so its AIR (hence the vk) does
    // not depend on the segment's traffic: `HTAPE` = `SREQ` (7 cells) + `HB` (3); `HOSTTAPE` (the
    // stand-in for lane A's HOST rows) = `HOSTQ` (22) + `HOSTR` (8) + `HOSTB` (5)
    // [B-T3] with the `STC` table (`Stc.m5tSegC`) the stand-in also plays lane F's `stRoot` side:
    // `STMQ` (211, 29 cells) sent, `STMA` (212, 29) received
    let stc = keys.iter().any(|k| k.0 == B_STMQ || k.0 == B_STMA);
    let fixed: Option<Vec<(u16, usize)>> = match name {
        "HTAPE" if stc => Some(vec![(B_SREQ, 7), (B_HB, 3), (B_STMQ, 29), (B_STMA, 29)]),
        "HTAPE" => Some(vec![(B_SREQ, 7), (B_HB, 3)]),
        // [B-T3] (B2-4) with the call context: `CTXB` (215, 2 cells), `CTXL` (216, 1)
        "HOSTTAPE" if keys.iter().any(|k| k.0 == 215) => Some(vec![(208, 22), (209, 8), (210, 5), (215, 2), (216, 1)]),
        "HOSTTAPE" => Some(vec![(208, 22), (209, 8), (210, 5)]),
        _ => None,
    };
    if let Some(f) = fixed {
        assert!(keys.iter().all(|k| f.contains(k)), "{name}: unexpected message kinds {keys:?}");
        keys = f;
    }
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
    };
    (spec, RowMajorMatrix::new(v, width))
}

/// [B-T1] Pad a harness table to `2^log` rows (zero rows carry no message).  Its width is fixed by
/// its `(bus, length)` keys: for `HTAPE` the execution side's `SREQ` (7) and `HB` (3), so 9 + 1 + 2.
fn pad_harness(m: &RowMajorMatrix<F>, spec: &TableSpec, log: usize) -> RowMajorMatrix<F> {
    let h = m.values.len() / m.width;
    assert!(h <= 1 << log, "{}: {h} rows exceed the template's 2^{log}", spec.name);
    let mut v = m.values.clone();
    v.resize((1 << log) * m.width, F::ZERO);
    RowMajorMatrix::new(v, m.width)
}

enum Native {
    Sha512,
    Table,
}

struct Inst {
    spec: Vec<TableSpec>,
    mats: Vec<RowMajorMatrix<F>>,
    pubs: Vec<F>,
    tape: BTreeMap<Key, u64>,
    /// M5b: the execution side's public messages (empty for the M5a AIR); [B-T3] one map per cached
    /// stand-in table (`HTAPE`: the runtime's `SREQ`/`HB` and lane F's `STMQ`/`STMA`; `HOSTTAPE`: lane
    /// A's HOST rows and the call context)
    htapes: Vec<(String, BTreeMap<Key, u64>)>,
    native: Vec<(Native, RowMajorMatrix<F>)>,
    /// expected interface traffic of the native chip (bus 103), for the precheck
    chip_if: BTreeMap<Key, u64>,
    n_comps: usize,
    /// [B-T1] the template (`template.json` of a `--split --template` dump)
    tmpl: Option<serde_json::Value>,
}

/// [B-T1] A template's pinned log height of `table`, if any.
fn pin_of(tmpl: &Option<serde_json::Value>, table: &str) -> Option<usize> {
    tmpl.as_ref().and_then(|t| t["heights"][table].as_u64()).map(|x| x as usize)
}

fn load(air_path: &str, dir: &str) -> Inst {
    let text = std::fs::read_to_string(air_path).unwrap();
    let nt = serde_json::from_str::<serde_json::Value>(&text).unwrap()["tables"].as_array().unwrap().len();
    let d = std::path::Path::new(dir);
    // [B-T1] a split dump names its template's tables
    let tnames: Option<Vec<String>> =
        std::fs::read_to_string(d.join("tables.json")).ok().map(|t| serde_json::from_str(&t).expect("tables.json"));
    let tmpl: Option<serde_json::Value> =
        std::fs::read_to_string(d.join("template.json")).ok().map(|t| serde_json::from_str(&t).expect("template.json"));
    let owned: Vec<&str>;
    let names: &[&str] = if let Some(v) = &tnames {
        owned = v.iter().map(|x| x.as_str()).collect();
        &owned
    } else if nt == NAMES_B.len() {
        NAMES_B
    } else if nt == NAMES_B8.len() {
        NAMES_B8
    } else {
        NAMES
    };
    let mut cl = ClassicalAir::parse(&text, names);
    assert_eq!(cl.tables.len(), names.len());
    for t in cl.tables.iter_mut() {
        for i in t.inters.iter_mut() {
            i.bus = map_bus(i.bus);
        }
    }
    let pb = std::fs::read(d.join("pubs.bin")).unwrap();
    let pubs: Vec<F> = pb.chunks(4).map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap()))).collect();
    let (mut spec, mut mats) = (vec![], vec![]);
    for t in cl.tables.iter() {
        // `SHAS` (M5b before M5a-8): the second SHA-256 instance, over the STATE messages
        let m = if t.name == "SHA" || t.name == "SHAS" {
            let f = if t.name == "SHA" { "sha_msgs.json" } else { "sha_msgs_st.json" };
            let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(d.join(f)).unwrap()).unwrap();
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
        let h = m.values.len() / m.width;
        assert!(h.is_power_of_two() && h >= 4, "{}: height {h}", t.name);
        assert!(h.trailing_zeros() as usize <= t.max_log, "{}: maxLog", t.name);
        if let Some(p) = pin_of(&tmpl, &t.name) {
            assert_eq!(h, 1 << p, "{}: height differs from the template pin", t.name);
        }
        spec.push(t.clone());
        mats.push(m);
    }
    // the SHA-512 chip
    let cv: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(d.join("comps.json")).unwrap()).unwrap();
    let comps: Vec<s384::reference::Comp> = cv
        .as_array()
        .unwrap()
        .iter()
        .map(|x| {
            let w = |k: &str, i: usize| x[k][i].as_str().unwrap().parse::<u64>().unwrap();
            s384::reference::Comp { h: std::array::from_fn(|i| w("h", i)), block: std::array::from_fn(|i| w("block", i)) }
        })
        .collect();
    let mut h = s384::trace::main_height(comps.len());
    if let Some(p) = pin_of(&tmpl, "SHA512") {
        assert!(h <= 1 << p, "SHA512: {} compressions exceed the template's 2^{p} rows", comps.len());
        h = 1 << p;
    }
    let main = s384::trace::gen_main(&comps, h);
    let table = s384::trace::gen_table(&main, h);
    let native = vec![
        (Native::Sha512, RowMajorMatrix::new(main.iter().map(|&x| F::new(x)).collect(), s384::air::WIDTH)),
        (Native::Table, RowMajorMatrix::new(table.iter().map(|&x| F::new(x)).collect(), s384::air::T_WIDTH)),
    ];
    let mut chip_if = BTreeMap::new();
    for (s, c) in comps.iter().enumerate() {
        let out = s384::reference::sha2_compress(c);
        let ws: Vec<u64> = c.h.iter().chain(c.block.iter()).chain(out.iter()).copied().collect();
        for m in 0..16 {
            let mut msg = vec![(s * s384::air::ROWS) as u32, m as u32];
            for wv in [ws[2 * m], ws[2 * m + 1]] {
                for v in s384::air::limbs(wv) {
                    msg.push(v as u32);
                }
            }
            add(&mut chip_if, (s384::air::BUS_IF, msg), 1);
        }
    }
    // public tape (absent in a B-T1 template dump: its `TCH` ends are public values of `WSX`)
    let mut tape = BTreeMap::new();
    if let Ok(txt) = std::fs::read_to_string(d.join("tape.json")) {
        let pm: serde_json::Value = serde_json::from_str(&txt).unwrap();
        for x in pm.as_array().unwrap() {
            let bus = map_bus(x[0].as_u64().unwrap() as u16);
            let send = x[1].as_bool().unwrap();
            let msg: Vec<u32> = x[2].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as u32).collect();
            add(&mut tape, (bus, msg), if send { 1 } else { P - 1 });
        }
        let (ts, tm) = harness("TAPE", &tape, true);
        // the tape right after the M5a tables (as `tapeTable … :: extra` in Lean)
        spec.insert(NAMES.len(), ts);
        mats.insert(NAMES.len(), tm);
    }
    // M5b: the execution side's messages (`SREQ`, `HB`) on T1, a second public table (last);
    // [B-T1 item 3] or lane A's host-bus messages (`HOSTQ`/`HOSTR`/`HOSTB`, `hosttape.json`)
    let mut htapes = vec![];
    for (hname, hfile) in [("HTAPE", "htape.json"), ("HOSTTAPE", "hosttape.json")] {
        let txt = match std::fs::read_to_string(d.join(hfile)) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let mut htape = BTreeMap::new();
        let hv: serde_json::Value = serde_json::from_str(&txt).unwrap();
        for x in hv.as_array().unwrap() {
            let bus = map_bus(x[0].as_u64().unwrap() as u16);
            let send = x[1].as_bool().unwrap();
            let msg: Vec<u32> = x[2].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as u32).collect();
            add(&mut htape, (bus, msg), if send { 1 } else { P - 1 });
        }
        let (hs, mut hm) = harness(hname, &htape, true);
        if let Some(p) = pin_of(&tmpl, hname) {
            // [B-T1] the cached execution-side table at its pinned height (zero rows: no message)
            hm = pad_harness(&hm, &hs, p);
        }
        spec.push(hs);
        mats.push(hm);
        htapes.push((hname.to_string(), htape));
    }
    Inst { spec, mats, pubs, tape, htapes, native, chip_if, n_comps: comps.len(), tmpl }
}

fn precheck(inst: &Inst) -> Result<(), String> {
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if t.harness.is_none() {
            check_constraints(t, m, &inst.pubs)?;
        }
    }
    let mut net = inst.chip_if.clone();
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if t.harness.is_none() {
            traffic(t, m, &inst.pubs, &mut net);
        }
    }
    for (k, c) in inst.tape.iter().chain(inst.htapes.iter().flat_map(|h| h.1.iter())) {
        add(&mut net, k.clone(), *c);
    }
    let bad: Vec<_> = net.iter().filter(|(_, c)| **c != 0).collect();
    if !bad.is_empty() {
        let mut by_bus: BTreeMap<u16, usize> = BTreeMap::new();
        for ((b, _), _) in &bad {
            *by_bus.entry(*b).or_default() += 1;
        }
        return Err(format!("{} unbalanced messages by bus {:?}; first {:?}", bad.len(), by_bus, &bad[..bad.len().min(2)]));
    }
    println!("PRECHECK OK: every constraint on every row; every bus balances ({} distinct messages)", net.len());
    Ok(())
}

fn airs(inst: &Inst) -> Vec<AirRef<Sha384Config>> {
    let mut v: Vec<AirRef<Sha384Config>> =
        inst.spec.iter().map(|t| Arc::new(JsonAir { spec: t.clone() }) as AirRef<Sha384Config>).collect();
    v.push(Arc::new(s384::air::Sha512Air4));
    v.push(Arc::new(s384::air::TableAir4));
    v
}

/// The commitment of a cached table (full height, no tight heights), as `nv::circuit::
/// commit_program_part` / pq-state-port's `prove_base` commit it.
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
        if !t.cached {
            out.push((i, AirProvingContext::simple(m.clone(), pv)));
        } else {
            let (commitment, data) = commit_cached(eng, m);
            let cached = CommittedTraceData { commitment, trace: m.clone(), data: Arc::new(data) };
            let h = m.values.len() / m.width;
            let empty = RowMajorMatrix::new(vec![F::ZERO; h], 1);
            out.push((i, AirProvingContext { cached_mains: vec![cached], common_main: empty, public_values: pv }));
        }
    }
    let base = mats.len();
    for (j, (_, m)) in inst.native.iter().enumerate() {
        out.push((base + j, AirProvingContext::simple(m.clone(), vec![])));
    }
    ProvingContext::new(out)
}

/// [B-T1] The tight-height floor of a pinned template: every common main commits its full height,
/// so the proof's `(log_height, tight_height)` per AIR is the template's (lane D's `PinnedHeight`).
fn full_floor(inst: &Inst) -> Vec<(usize, usize, usize)> {
    let mut f = vec![];
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        let h = m.values.len() / m.width;
        let w = if t.cached { 1 } else { m.width };
        f.push((w, h.trailing_zeros() as usize, h));
    }
    for (_, m) in &inst.native {
        let h = m.values.len() / m.width;
        f.push((m.width, h.trailing_zeros() as usize, h));
    }
    f
}

/// The verifier's statement check: the TAPE commitment equals the one recomputed from the public
/// messages, and the public values are the statement's (`prev_state_root`).
fn check_statement(eng: &Sha384CpuEngine, inst: &Inst, want_pubs: &[F], proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> bool {
    let mut tape_ok = true;
    if let Some(ti) = inst.spec.iter().position(|t| t.name == "TAPE") {
        let (_, tm) = harness("TAPE", &inst.tape, true);
        let want = commit_cached(eng, &tm).0;
        tape_ok &= matches!(&proof.trace_vdata[ti], Some(v) if v.cached_commitments.len() == 1 && v.cached_commitments[0] == want);
    }
    for (hname, htape) in &inst.htapes {
        let hi = inst.spec.iter().position(|t| &t.name == hname).unwrap();
        let (hs, mut hm) = harness(hname, htape, true);
        if let Some(p) = pin_of(&inst.tmpl, hname) {
            hm = pad_harness(&hm, &hs, p);
        }
        let hw = commit_cached(eng, &hm).0;
        tape_ok &= matches!(&proof.trace_vdata[hi], Some(v) if v.cached_commitments.len() == 1 && v.cached_commitments[0] == hw);
    }
    let pv_ok = inst.spec.iter().enumerate().all(|(i, t)| {
        let pv: Vec<F> = (0..t.num_pub).map(|k| want_pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        proof.public_values[i] == pv
    });
    tape_ok && pv_ok
}

// Upstream skips the extended-domain factor in VK serde; `pq-chunk-e2e` keeps it in an envelope.
#[derive(serde::Serialize)]
struct SavedVk<'a> {
    domain_odd_factor: usize,
    vk: &'a MultiStarkVerifyingKey<Sha384Config>,
}

/// [B-T1] Save the proof and vk in the stack's format (`pq-chunk-e2e` `save_proof` / `save_vk`), and
/// the statement: every AIR's name, public values, `(log_height, tight_height)` and cached roots.
fn save(out: &std::path::Path, inst: &Inst, vk: &MultiStarkVerifyingKey<Sha384Config>, proof: &openvm_stark_backend::proof::Proof<Sha384Config>, sz: usize) {
    use sha2::Digest as _;
    std::fs::create_dir_all(out).unwrap();
    let mut b = vec![];
    proof.encode(&mut b).unwrap();
    assert_eq!(b.len(), sz);
    std::fs::write(out.join("STATE.proof"), &b).unwrap();
    let vkb = serde_json::to_vec(&SavedVk { domain_odd_factor: vk.inner.params.whir.domain_odd_factor, vk }).unwrap();
    std::fs::write(out.join("STATE.vk.json"), &vkb).unwrap();
    let mut names: Vec<String> = inst.spec.iter().map(|t| t.name.clone()).collect();
    names.push("SHA512".into());
    names.push("SHA512T".into());
    let airs: Vec<serde_json::Value> = names
        .iter()
        .enumerate()
        .map(|(i, n)| {
            let v = proof.trace_vdata[i].as_ref();
            serde_json::json!({
                "name": n,
                "public_values": proof.public_values[i].iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
                "log_height": v.map(|v| v.log_height),
                "tight_height": v.and_then(|v| v.tight_height),
                "cached_roots": v.map(|v| v.cached_commitments.iter().map(|c| format!("{c:?}")).collect::<Vec<_>>()),
            })
        })
        .collect();
    let st = serde_json::json!({
        "template": inst.tmpl,
        "proof_bytes": sz,
        "proof_sha256": format!("{:x}", sha2::Sha256::digest(&b)),
        "vk_sha256": format!("{:x}", sha2::Sha256::digest(&vkb)),
        "vk_pre_hash": format!("{:?}", vk.pre_hash),
        "statement": inst.pubs.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
        "airs": airs,
    });
    std::fs::write(out.join("statement.json"), serde_json::to_vec_pretty(&st).unwrap()).unwrap();
    println!("SAVED {} (STATE.proof {sz} B, STATE.vk.json {} B)", out.display(), vkb.len());
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
            "TABLE {:<6} width {:>4} height 2^{:<2} cells {:>9} constraints {:>5} interactions {:>5} deg {}",
            t.name, m.width, h.trailing_zeros(), h * m.width, t.constraints.len(), ni, d
        );
    }
    for (k, m) in &inst.native {
        let h = m.values.len() / m.width;
        cells += h * m.width;
        let nm = match k {
            Native::Sha512 => "SHA512",
            Native::Table => "SHA512T",
        };
        println!("TABLE {:<6} width {:>4} height 2^{:<2} cells {:>9} (native v4)", nm, m.width, h.trailing_zeros(), h * m.width);
    }
    let pinned: Vec<String> = inst.spec.iter().zip(&inst.mats).map(|(t, m)| format!("\"{}\": {}", t.name, (m.values.len() / m.width).trailing_zeros()))
        .chain(inst.native.iter().take(1).map(|(_, m)| format!("\"SHA512\": {}", (m.values.len() / m.width).trailing_zeros())))
        .collect();
    println!("HEIGHTS {{{}}}", pinned.join(", "));
    println!("CELLS {cells}; compressions {}", inst.n_comps);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: {} <m5a.json> <dump_dir> check|prove|mutant [out_dir]", args[0]);
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
    let total: usize = inst.mats.iter().chain(inst.native.iter().map(|(_, m)| m)).map(|m| m.values.len()).sum();
    let maxh = inst.mats.iter().chain(inst.native.iter().map(|(_, m)| m)).map(|m| m.values.len() / m.width).max().unwrap();
    let n_stack = [14usize, 18, 22].into_iter().find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24).unwrap_or(22);
    let w_stack = (total.div_ceil(1 << (n_stack + 2)) + 4).max(8);
    // M5a-7: overrides for the stacking-shape sweep (README §M5b, "+287 kB"); unset = the rule above
    let env_n = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<usize>().ok());
    let n_stack = env_n("N_STACK").unwrap_or(n_stack);
    let w_stack = env_n("W_STACK").unwrap_or(if env_n("N_STACK").is_some() { (total.div_ceil(1 << (n_stack + 2)) + 4).max(8) } else { w_stack });
    let degree = inst.spec.iter().flat_map(|t| t.constraints.iter().map(deg)).max().unwrap_or(2).max(s384::air::DEGREE);
    let prm = if let Some(t) = &inst.tmpl {
        // [B-T1] the template's pinned parameters (lane D's base configuration)
        let g = |k: &str| t["params"][k].as_u64().unwrap_or_else(|| panic!("template params.{k}")) as usize;
        let root = std::env::var("NEARPROOF_ROOT").unwrap_or_else(|_| "/data/illia/nearproof".into());
        let cert = std::env::var("NEARPROOF_CERTS").unwrap_or_else(|_| format!("{root}/research/near-compression/final-soundness/calc/dkt_certs_o2.json"));
        let excl = std::env::var("NEARPROOF_EXCL").unwrap_or_else(|_| format!("{root}/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys"));
        assert_eq!(g("degree"), degree, "template degree");
        base_params(g("n_stack"), g("log_blowup"), g("w_stack"), degree, g("pow_bits"), &cert, &excl)
    } else {
        params(n_stack, w_stack, degree)
    };
    println!(
        "PARAMS n_stack {} w_stack {} log_blowup {} degree {} pow {} queries {:?} k {:?}",
        prm.n_stack,
        prm.w_stack,
        prm.log_blowup,
        prm.max_constraint_degree,
        prm.whir.query_phase_pow_bits,
        prm.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
        (0..prm.whir.rounds.len()).map(|r| prm.whir.k_round(r)).collect::<Vec<_>>()
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
    // the statement: prev_state_root from the claim (here: the dump's public values)
    let st = check_statement(&eng, &inst, &inst.pubs, &proof);
    println!("TIME prove {t_prove:.2}s verify {t_verify:.4}s threads {} peak_rss_kib {} proof_bytes {sz}", std::env::var("RAYON_NUM_THREADS").unwrap_or_default(), peak_rss_kib());
    if let (true, true, Some(out)) = (ver.is_ok(), st, args.get(4)) {
        save(std::path::Path::new(out), &inst, &vk, &proof, sz);
    }
    match (ver.is_ok(), st) {
        (true, true) => {
            println!("VERIFY OK (native SWIRL verifier); statement check (cached roots + every AIR's public values): OK");
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
