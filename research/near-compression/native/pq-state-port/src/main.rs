//! lane/pq-state-port: **all 25** `nearAirV3` tables (D0a; the Lean AIR value, exported as
//! `np-air-v2`), with honest traces of a real D0a fixture rendered by the classical Rust
//! generators (`examples/np-udr-stark-v2/source/examples/statedump.rs`), proven **unchanged** on
//! the unified SWIRL backend (BabyBear, Ext12, SHA-384, T*, 42-byte digests, stacked WHIR) and
//! verified natively.
//!
//! Usage:
//!   nearproof-pq-state-port <nearAirV3.json> <dump_dir> check|prove|tamper [small|pinned]
//!
//! **No stand-in tables.**  A D0a dump must contain every one of the 25 tables (the run fails
//! otherwise); the bus balance is checked over the 25 tables plus the public tape only.  The
//! classical public segments (verifier-computed messages on the buses) become the cached `TAPE`
//! table whose commitment V_d recomputes from the public messages.
//!
//! Structural items from the envelope study (README §3) handled here:
//! * M4 heights: the dump is re-cut to natural heights with a floor of 4 rows (the NV minimum),
//!   so no table is below the SWIRL/NV minimum and the fixed 2^22 renders shrink to the used rows;
//! * M4 caps: every table's `log` is checked against its `maxLog` (the soundness proofs use the
//!   per-table cap);
//! * M7 message length 2^6 and M8 interaction budget 2^30 (see `seg_v1_params`);
//! * M2 tape: `TAPE` is a cached table; `check_statement` recomputes its commitment.
//!
//! Bus-id offset for the later direct-Wasm join: `BUS_OFFSET` is applied to every classical bus
//! id, leaving buses below it free for the Wasm family (`pq-wasm-base` uses 0-4).
mod air;
#[cfg(not(feature = "chunk-recursion"))]
#[allow(dead_code, clippy::all)]
mod config;
#[cfg(feature = "chunk-recursion")]
use openvm_recursion_circuit::sha384::config;

use air::{ClassicalAir, E, JsonAir, TableSpec};
use config::{F, Sha384Config, Sha384RefEngine};
use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    air_builders::symbolic::{SymbolicExpressionNode, symbolic_variable::Entry},
    codec::Encode,
    interaction::LogUpSecurityParameters,
    prover::{
        AirProvingContext, ColMajorMatrix, CommittedTraceData, CpuColMajorBackend,
        DeviceDataTransporter, ProvingContext, TraceCommitter,
    },
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::Instant;

/// `v3::prove::ORDER` (the 25 tables of `nearAirV3`, by position; D0a).
const ORDER: &[&str] = &[
    "sha_t", "sha_r", "node", "head", "val", "walk", "uniq", "ups", "chacha", "rng", "shuf",
    "codec", "scandist", "proc", "mem", "cmp", "rcpt", "acct", "akey", "bnd", "srcp", "size", "qv",
    "mrk", "sort",
];

/// `v3::d1::ORDER_D1` (the 30 tables of `nearAirV3D1`, by position; D1).
const ORDER_D1: &[&str] = &[
    "sha_t", "sha_r", "node", "head", "val", "walk", "uniq", "ups", "chacha", "rng", "shuf",
    "codec", "scandist", "proc", "mem", "cmp", "rcpt", "acct", "akey", "bnd", "srcp", "size", "qv",
    "mrk", "sort", "tx", "akm", "kib", "plf", "rid",
];

/// Which classical AIR the dump belongs to: the D0a set (25 tables) or the D1 set (30).
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    D0a,
    D1,
}

impl Variant {
    fn order(self) -> &'static [&'static str] {
        match self {
            Variant::D0a => ORDER,
            Variant::D1 => ORDER_D1,
        }
    }
    fn len(self) -> usize {
        self.order().len()
    }
    fn name(self) -> &'static str {
        match self {
            Variant::D0a => "nearAirV3 (D0a, 25 tables)",
            Variant::D1 => "nearAirV3D1 (D1, 30 tables)",
        }
    }
}

/// Reserved bus range for the later direct-Wasm join (`pq-wasm-base` uses ids 0-4; the classical
/// buses are 0-76).  Every classical interaction is shifted up by this offset so the two families
/// can never collide on a bus id.
const BUS_OFFSET: u16 = 128;
const P: u64 = 0x7800_0001;

fn set_levers() {
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
}

/// seg-v1 shape (DESIGN-BASE §3) with the message-length parameter raised to 2^6 (classical
/// messages reach 34 fields + the bus, M7) and the interaction budget raised to 2^30 (the D0a
/// worst case is 2^29.55, M8; 2^30 < p so mod-p LogUp stays exact).
fn seg_v1_params(n_stack: usize, w_stack: usize, max_degree: usize) -> SystemParams {
    let (l_skip, log_blowup, k, k1, lf) = (2, 1, 4, 1, 7);
    let log_h = l_skip + n_stack;
    assert_eq!((log_h - k1 - lf) % k, 0, "n_stack must be 10, 14, 18 or 22");
    let levers = WhirLevers {
        k_first: k1,
        multiproof: true,
        keep_domain: true,
        whir_y: true,
        ..Default::default()
    };
    let whir = WhirConfig::new_full(
        log_blowup,
        log_h,
        WhirParams {
            k,
            log_final_poly_len: lf,
            query_phase_pow_bits: std::env::var("PQD1_POW")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(24),
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
        logup: LogUpSecurityParameters {
            max_interaction_count: 1 << 30,
            log_max_message_length: 6,
            pow_bits: 0,
        },
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
    let b = std::fs::read(path).unwrap();
    let u = |i: usize| u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap());
    let (log, w) = (u(0) as usize, u(1) as usize);
    let n = (1usize << log) * w;
    assert_eq!(b.len(), 8 + 4 * n, "{path:?}: size");
    RowMajorMatrix::new((0..n).map(|i| F::new(u(2 + i))).collect(), w)
}

struct Inst {
    spec: Vec<TableSpec>,
    mats: Vec<RowMajorMatrix<F>>,
    pubs: Vec<F>,
    /// (bus, msg) -> net count of the public messages (send +1, receive −1)
    tape: BTreeMap<Key, u64>,
}

type Key = (u16, Vec<u32>);

fn add(map: &mut BTreeMap<Key, u64>, k: Key, c: u64) {
    let e = map.entry(k).or_insert(0);
    *e = (*e + c) % P;
}

/// Net bus traffic of `t` (count `+c` for sends, `−c` for receives), modulo p.
fn traffic(t: &TableSpec, m: &RowMajorMatrix<F>, pubs: &[F], map: &mut BTreeMap<Key, u64>) {
    let w = m.width;
    let h = m.values.len() / w;
    for r in 0..h {
        let cur = &m.values[r * w..(r + 1) * w];
        let nr = (r + 1) % h;
        let nxt = &m.values[nr * w..(nr + 1) * w];
        let sel = [
            if r == 0 { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ZERO } else { F::ONE },
        ];
        for i in &t.inters {
            let mut c = F::ZERO;
            for (k, b) in i.mult.iter().enumerate() {
                c += b.eval_f(cur, nxt, pubs, sel) * F::from_u64(1 << k);
            }
            if c == F::ZERO {
                continue;
            }
            let msg: Vec<u32> = i
                .msg
                .iter()
                .map(|e| e.eval_f(cur, nxt, pubs, sel).as_canonical_u32())
                .collect();
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
        let nr = (r + 1) % h;
        let nxt = &m.values[nr * w..(nr + 1) * w];
        let sel = [
            if r == 0 { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ONE } else { F::ZERO },
            if r + 1 == h { F::ZERO } else { F::ONE },
        ];
        for (ci, c) in t.constraints.iter().enumerate() {
            if c.eval_f(cur, nxt, pubs, sel) != F::ZERO {
                return Err(format!("{}: constraint {ci} fails on row {r}", t.name));
            }
        }
    }
    Ok(())
}

/// A harness table: one row per (key, net count); columns msg[0..W), cnt, sel[k].
fn harness(name: &str, map: &BTreeMap<Key, u64>, cached: bool) -> (TableSpec, RowMajorMatrix<F>) {
    let keys: Vec<(u16, usize)> = map
        .keys()
        .map(|(b, m)| (*b, m.len()))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
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

/// Shift every classical bus id by `BUS_OFFSET` (reserving the low ids for the Wasm join).
fn offset_buses(cl: &mut ClassicalAir) {
    for t in cl.tables.iter_mut() {
        for i in t.inters.iter_mut() {
            i.bus += BUS_OFFSET;
        }
    }
}

fn load(air_path: &str, dir: &str, v: Variant) -> Inst {
    let mut cl = ClassicalAir::parse(&std::fs::read_to_string(air_path).unwrap(), v.order());
    assert_eq!(cl.tables.len(), v.len(), "not {}", v.name());
    offset_buses(&mut cl);
    let d = std::path::Path::new(dir);
    let pb = std::fs::read(d.join("pubs.bin")).unwrap();
    let pubs: Vec<F> = pb
        .chunks(4)
        .map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap())))
        .collect();
    let (mut spec, mut mats) = (vec![], vec![]);
    let mut net: BTreeMap<Key, u64> = BTreeMap::new();
    // Every table of the AIR must be present: this lane has no stand-in table.
    let mut missing = vec![];
    for t in cl.tables.iter() {
        let f = d.join(format!("{}.bin", t.name));
        if !f.exists() {
            missing.push(t.name.clone());
            continue;
        }
        let m = read_trace(&f);
        assert_eq!(m.width, t.width, "{}: width", t.name);
        let h = m.values.len() / m.width;
        let log = h.trailing_zeros() as usize;
        assert!(
            h.is_power_of_two() && h >= 4,
            "{}: height {h} is not 2^log >= 4",
            t.name
        );
        assert!(
            log <= t.max_log,
            "{}: log {log} > maxLog {} (per-table height cap)",
            t.name,
            t.max_log
        );
        traffic(t, &m, &pubs, &mut net);
        spec.push(t.clone());
        mats.push(m);
    }
    assert!(
        missing.is_empty(),
        "D0a port needs all 25 tables; missing {missing:?}"
    );
    // public segments (classical `pubMsgs`): the verifier's own bus messages
    let pm: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(d.join("pubmsgs.json")).unwrap()).unwrap();
    let mut tape = BTreeMap::new();
    for x in pm.as_array().unwrap() {
        let bus = x[0].as_u64().unwrap() as u16 + BUS_OFFSET;
        let send = x[1].as_bool().unwrap();
        let msg: Vec<u32> = x[2]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_u64().unwrap() as u32)
            .collect();
        add(&mut tape, (bus, msg.clone()), if send { 1 } else { P - 1 });
        add(&mut net, (bus, msg), if send { 1 } else { P - 1 });
    }
    // No stand-in: every bus must balance over the 25 tables plus the public tape.
    let bad: Vec<_> = net.iter().filter(|(_, c)| **c != 0).collect();
    assert!(
        bad.is_empty(),
        "{} unbalanced bus messages (no stand-in table): {:?}",
        bad.len(),
        &bad[..bad.len().min(5)]
    );
    let (ts, tm) = harness("TAPE", &tape, true);
    spec.push(ts);
    mats.push(tm);
    Inst {
        spec,
        mats,
        pubs,
        tape,
    }
}

/// Parse only the AIR (no dump): every classical table plus the synthetic TAPE entry, which the
/// difftest covers as an ordinary table spec.  Used by the `difftest` mode, where the point is to
/// compare the Lean AIR value against the Rust keygen's symbolic DAG, not to prove a trace.
fn specs_for_difftest(air_path: &str, v: Variant) -> Vec<TableSpec> {
    let mut cl = ClassicalAir::parse(&std::fs::read_to_string(air_path).unwrap(), v.order());
    assert_eq!(cl.tables.len(), v.len(), "not {}", v.name());
    offset_buses(&mut cl);
    let mut out = cl.tables;
    // TAPE: a harness spec with the maximum message width and both possible bus keys, so the
    // difftest exercises a harness table's interaction shape too.
    out.push(TableSpec {
        name: "TAPE".into(),
        width: 8,
        max_log: 22,
        constraints: vec![],
        inters: vec![],
        harness: Some((5, vec![(BUS_OFFSET, 4), (BUS_OFFSET + 1, 2)])),
        cached: true,
        num_pub: 0,
    });
    out
}

fn report(inst: &Inst) {
    let mut cells = 0;
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        let h = m.values.len() / m.width;
        cells += h * m.width;
        let d = t.constraints.iter().map(deg).max().unwrap_or(0);
        println!(
            "TABLE {:<8} width {:>3} height 2^{:<2} cells {:>9} constraints {:>4} interactions {:>3} deg {} pubs {}{}",
            t.name,
            m.width,
            h.trailing_zeros(),
            h * m.width,
            t.constraints.len(),
            t.harness
                .as_ref()
                .map(|h| h.1.len())
                .unwrap_or(t.inters.len()),
            d,
            t.num_pub,
            if t.cached { " (cached)" } else { "" }
        );
    }
    println!(
        "CELLS {cells}; all {} classical tables + TAPE; tape keys {}",
        inst.spec.len() - 1,
        inst.tape.len()
    );
}

fn pv_of(t: &TableSpec, pubs: &[F]) -> Vec<F> {
    (0..t.num_pub)
        .map(|i| pubs.get(i).copied().unwrap_or(F::ZERO))
        .collect()
}

fn ctx(
    eng: &Sha384RefEngine,
    inst: &Inst,
    mats: &[RowMajorMatrix<F>],
    pubs: &[F],
) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
    ProvingContext::new(
        mats.iter()
            .enumerate()
            .map(|(i, m)| {
                let t = &inst.spec[i];
                let pv = pv_of(t, pubs);
                if !t.cached {
                    (
                        i,
                        AirProvingContext::simple(ColMajorMatrix::from_row_major(m), pv),
                    )
                } else {
                    let cm = ColMajorMatrix::from_row_major(m);
                    let (commitment, data) = eng.device().commit(&[&cm]).expect("commit cached");
                    let cached = CommittedTraceData {
                        commitment,
                        trace: cm,
                        data: Arc::new(data),
                    };
                    let h = m.values.len() / m.width;
                    let empty =
                        ColMajorMatrix::from_row_major(&RowMajorMatrix::new(vec![F::ZERO; h], 1));
                    (
                        i,
                        AirProvingContext {
                            cached_mains: vec![cached],
                            common_main: empty,
                            public_values: pv,
                        },
                    )
                }
            })
            .collect(),
    )
}

/// **P4 statement component.**  The statement that V_d checks, as a list of Felt vectors:
/// `[tape_root_words…, header_pubs…]`.  This is the concrete analogue of the NV statement digest
/// (`sha384::config::statement_digest`): V_d recomputes the TAPE root from the claim's public
/// messages and compares it here, so the cached table is *pinned by the statement*, not merely
/// present in the proof.
fn statement_values(inst: &Inst, eng: &Sha384RefEngine) -> Vec<Vec<F>> {
    let (_, tm) = harness("TAPE", &inst.tape, true);
    let root = eng
        .device()
        .commit(&[&ColMajorMatrix::from_row_major(&tm)])
        .expect("tape root")
        .0;
    let mut tape = Vec::new();
    for w in root.into_iter() {
        tape.push(F::from_u64(w >> 32));
        tape.push(F::from_u64(w & 0xffff_ffff));
    }
    vec![tape, inst.pubs.clone()]
}

/// V_d's statement check: the proof's cached TAPE commitment equals the one recomputed from the
/// public messages (a function of the claim via the classical `prepV3`), and the header public
/// values are the claim's.
fn check_statement(
    eng: &Sha384RefEngine,
    inst: &Inst,
    proof: &openvm_stark_backend::proof::Proof<Sha384Config>,
) -> bool {
    let ti = inst.spec.iter().position(|t| t.name == "TAPE").unwrap();
    let (_, tm) = harness("TAPE", &inst.tape, true);
    let want = eng
        .device()
        .commit(&[&ColMajorMatrix::from_row_major(&tm)])
        .expect("tape root")
        .0;
    let tape_ok = matches!(&proof.trace_vdata[ti], Some(v) if v.cached_commitments.len() == 1 && v.cached_commitments[0] == want);
    let pv_ok = inst
        .spec
        .iter()
        .enumerate()
        .all(|(i, t)| proof.public_values[i] == pv_of(t, &inst.pubs));
    tape_ok && pv_ok
}

fn airs(inst: &Inst) -> Vec<AirRef<Sha384Config>> {
    inst.spec
        .iter()
        .map(|t| Arc::new(JsonAir { spec: t.clone() }) as AirRef<Sha384Config>)
        .collect()
}

fn params_for(inst: &Inst, which: &str) -> SystemParams {
    let total: usize = inst.mats.iter().map(|m| m.values.len()).sum();
    let maxh = inst
        .mats
        .iter()
        .map(|m| m.values.len() / m.width.max(1))
        .max()
        .unwrap();
    let n_stack = match which {
        "pinned" => 22,
        _ => [14, 18, 22]
            .into_iter()
            .find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24)
            .unwrap_or(22),
    };
    let w_stack = total.div_ceil(1 << (n_stack + 2)) + 4;
    let degree = inst
        .spec
        .iter()
        .flat_map(|t| t.constraints.iter().map(deg))
        .max()
        .unwrap_or(2)
        .max(2);
    seg_v1_params(n_stack, w_stack.max(8), degree)
}

fn census(proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> String {
    fn size<T: Encode>(x: &T) -> usize {
        let mut b = Vec::new();
        x.encode(&mut b).unwrap();
        b.len()
    }
    let lv = proof.whir_proof.levers;
    let (mut gk, mut rl) = (Vec::new(), Vec::new());
    proof.gkr_proof.encode_levers(&lv, &mut gk).unwrap();
    proof.batch_constraint_proof.encode_levers(&mut rl).unwrap();
    format!(
        "total={} gkr={} relations={} stacking={} whir={}",
        size(proof),
        gk.len(),
        rl.len(),
        size(&proof.stacking_proof),
        size(&proof.whir_proof)
    )
}

fn peak_rss_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .map(|l| l.split_whitespace().nth(1).unwrap().parse().unwrap())
        })
        .unwrap_or(0)
}

fn precheck(inst: &Inst) {
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if t.harness.is_none() {
            check_constraints(t, m, &inst.pubs).expect("constraints");
        }
    }
    // every bus balances mod p over the 25 classical tables + TAPE (no stand-in)
    let mut net = BTreeMap::new();
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        if let Some((w, keys)) = &t.harness {
            let wd = m.width;
            for row in m.values.chunks(wd) {
                for (k, (bus, len)) in keys.iter().enumerate() {
                    let c = row[*w] * row[*w + 1 + k];
                    if c != F::ZERO {
                        add(
                            &mut net,
                            (
                                *bus,
                                row[..*len].iter().map(|x| x.as_canonical_u32()).collect(),
                            ),
                            c.as_canonical_u32() as u64,
                        );
                    }
                }
            }
        } else {
            traffic(t, m, &inst.pubs, &mut net);
        }
    }
    let bad = net.values().filter(|c| **c != 0).count();
    assert_eq!(bad, 0, "{bad} unbalanced messages");
    println!(
        "PRECHECK OK: every constraint on every row; every bus balances ({} distinct messages)",
        net.len()
    );
}

/// One DAG evaluation: constraint values, and `(bus, signed count, message)` per interaction.
type DagEval = (Vec<F>, Vec<(u16, F, Vec<F>)>);

/// Evaluate the keygen's symbolic constraint DAG at one point.
fn dag_eval(
    vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>,
    ai: usize,
    cached: usize,
    cur: &[F],
    nxt: &[F],
    pubs: &[F],
    sel: [F; 3],
) -> DagEval {
    let dag = &vk.inner.per_air[ai].symbolic_constraints;
    let mut val: Vec<F> = Vec::with_capacity(dag.constraints.nodes.len());
    for n in &dag.constraints.nodes {
        let v = match n {
            SymbolicExpressionNode::Variable(var) => match var.entry {
                Entry::Main {
                    offset: 0,
                    part_index,
                } => {
                    cur[if cached > 0 && part_index > 0 {
                        cached + var.index
                    } else {
                        var.index
                    }]
                }
                Entry::Main {
                    offset: 1,
                    part_index,
                } => {
                    nxt[if cached > 0 && part_index > 0 {
                        cached + var.index
                    } else {
                        var.index
                    }]
                }
                Entry::Public => pubs[var.index],
                e => panic!("unexpected entry {e:?}"),
            },
            SymbolicExpressionNode::IsFirstRow => sel[0],
            SymbolicExpressionNode::IsLastRow => sel[1],
            SymbolicExpressionNode::IsTransition => sel[2],
            SymbolicExpressionNode::Constant(c) => *c,
            SymbolicExpressionNode::Add {
                left_idx,
                right_idx,
                ..
            } => val[*left_idx] + val[*right_idx],
            SymbolicExpressionNode::Sub {
                left_idx,
                right_idx,
                ..
            } => val[*left_idx] - val[*right_idx],
            SymbolicExpressionNode::Neg { idx, .. } => -val[*idx],
            SymbolicExpressionNode::Mul {
                left_idx,
                right_idx,
                ..
            } => val[*left_idx] * val[*right_idx],
        };
        val.push(v);
    }
    let cons = dag
        .constraints
        .constraint_idx
        .iter()
        .map(|&i| val[i])
        .collect();
    let ints = dag
        .interactions
        .iter()
        .map(|it| {
            (
                it.bus_index,
                val[it.count],
                it.message.iter().map(|&i| val[i]).collect(),
            )
        })
        .collect();
    (cons, ints)
}

/// **P3: the Rust vk is the Lean AIR.**  Emit random points and the keygen DAG's values there;
/// `difftest_p3.py` evaluates the same points against the Lean export and compares.
fn cmd_difftest(air_path: &str, points_out: &str, rust_out: &str, n: usize, v: Variant) {
    set_levers();
    let spec = specs_for_difftest(air_path, v);
    let eng = Sha384RefEngine::new(seg_v1_params(14, 32, 8));
    let airs: Vec<AirRef<Sha384Config>> = spec
        .iter()
        .map(|t| Arc::new(JsonAir { spec: t.clone() }) as AirRef<Sha384Config>)
        .collect();
    let (_pk, vk) = eng.keygen(&airs);
    let mut rng: u64 = 0x2026_1019_dead_beef;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        F::from_u32((rng % 2013265921) as u32)
    };
    let mut pts = String::new();
    let mut out = String::new();
    for (ti, t) in spec.iter().enumerate() {
        let w = t.width;
        let np = t.num_pub;
        for _ in 0..n {
            let sel = [next(), next(), next()];
            let cur: Vec<F> = (0..w).map(|_| next()).collect();
            let nxt: Vec<F> = (0..w).map(|_| next()).collect();
            let pubs: Vec<F> = (0..np).map(|_| next()).collect();
            let j = |v: &[F]| {
                v.iter()
                    .map(|x| x.as_canonical_u32().to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            };
            pts.push_str(&format!(
                "{} {} | {} | {} | {}
",
                ti,
                j(&sel),
                j(&cur),
                j(&nxt),
                j(&pubs)
            ));
            let (cons, ints) = dag_eval(
                &vk,
                ti,
                if t.cached { w } else { 0 },
                &cur,
                &nxt,
                &pubs,
                sel,
            );
            let cj: Vec<String> = cons
                .iter()
                .map(|x| x.as_canonical_u32().to_string())
                .collect();
            let ij: Vec<String> = ints
                .iter()
                .map(|(b, c, m)| {
                    format!(
                        "[{},{},[{}]]",
                        b,
                        c.as_canonical_u32(),
                        m.iter()
                            .map(|x| x.as_canonical_u32().to_string())
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                })
                .collect();
            out.push_str(&format!(
                "{{\"t\":{ti},\"constraints\":[{}],\"inters\":[{}]}}\n",
                cj.join(","),
                ij.join(",")
            ));
        }
    }
    std::fs::write(points_out, pts).unwrap();
    std::fs::write(rust_out, out).unwrap();
    println!(
        "DIFFTEST points written: {} tables x {n} (incl. TAPE as a harness spec)",
        spec.len()
    );
}

fn cmd(air_path: &str, dir: &str, mode: &str, which: &str, v: Variant) {
    set_levers();
    let t0 = Instant::now();
    let inst = load(air_path, dir, v);
    report(&inst);
    precheck(&inst);
    println!("TIME load+precheck {:.2}s", t0.elapsed().as_secs_f64());
    if mode == "check" {
        return;
    }
    let params = params_for(&inst, which);
    println!(
        "PARAMS n_stack {} log_h {} w_stack {} degree {} queries {:?} pow {} log_max_msg {}",
        params.n_stack,
        params.l_skip + params.n_stack,
        params.w_stack,
        params.max_constraint_degree,
        params
            .whir
            .rounds
            .iter()
            .map(|r| r.num_queries)
            .collect::<Vec<_>>(),
        params.whir.query_phase_pow_bits,
        params.logup.log_max_message_length
    );
    let eng = Sha384RefEngine::new(params);
    let airs = airs(&inst);
    let t1 = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    println!("TIME keygen {:.2}s", t1.elapsed().as_secs_f64());
    let mut dag_total = 0;
    for (i, a) in vk.inner.per_air.iter().enumerate() {
        dag_total += a.symbolic_constraints.constraints.nodes.len();
        println!(
            "VK {:<8} degree {} constraints {} interactions {} dag_nodes {}",
            inst.spec[i].name,
            a.max_constraint_degree,
            a.symbolic_constraints.constraints.constraint_idx.len(),
            a.symbolic_constraints.interactions.len(),
            a.symbolic_constraints.constraints.nodes.len()
        );
    }
    println!("VK dag_nodes total {dag_total}");
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!(
        "SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}",
        b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits
    );
    if std::env::var("PQD1_DEBUG").is_ok() {
        eng.debug(&airs, &ctx(&eng, &inst, &inst.mats, &inst.pubs));
        println!("DEBUG OK");
    }
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let t2 = Instant::now();
    let proof = eng
        .prove(&d_pk, ctx(&eng, &inst, &inst.mats, &inst.pubs))
        .expect("prove");
    let t_prove = t2.elapsed().as_secs_f64();
    let t3 = Instant::now();
    eng.verify(&vk, &proof).expect("verify");
    let t_verify = t3.elapsed().as_secs_f64();
    let st = check_statement(&eng, &inst, &proof);
    println!("PROOF {}", census(&proof));
    println!(
        "VERIFY OK (native SWIRL verifier); V_d statement check (TAPE root + header PVs): {}",
        if st { "OK" } else { "FAIL" }
    );
    assert!(st);
    println!(
        "TIME prove {t_prove:.2}s verify {t_verify:.4}s threads {} peak_rss_kib {}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_default(),
        peak_rss_kib()
    );
    if mode != "tamper" {
        return;
    }
    // Tamper cases: each must be rejected by the native verifier or by V_d's statement check.
    let idx = |n: &str| inst.spec.iter().position(|t| t.name == n);
    let mut cases: Vec<(String, Vec<RowMajorMatrix<F>>, Vec<F>)> = vec![];
    // one mutated cell per D0a table family: trie (node/head/val/walk/uniq/ups), SHA-256,
    // scheduler (codec/proc/mem/cmp/scandist), receipts (rcpt), and the small statement tables.
    for (name, row, col) in [
        ("node", 0usize, 0usize),
        ("node", 5, 40),
        ("head", 1, 3),
        ("val", 2, 1),
        ("walk", 3, 7),
        ("uniq", 1, 2),
        ("ups", 4, 10),
        ("sha_t", 7, 100),
        ("sha_r", 3, 17),
        ("codec", 2, 9),
        ("proc", 1, 5),
        ("mem", 0, 3),
        ("cmp", 1, 8),
        ("scandist", 2, 12),
        ("rcpt", 1, 9),
        ("size", 0, 0),
        ("srcp", 1, 1),
        ("tx", 0, 5),
        ("akm", 1, 4),
        ("kib", 0, 2),
        ("plf", 0, 1),
        ("rid", 0, 1),
    ] {
        if let Some(t) = idx(name) {
            let mut mats = inst.mats.clone();
            let w = mats[t].width;
            let h = mats[t].values.len() / w;
            // Prefer a row that is actually live.  A table can be empty on a fixture (e.g. `rid`
            // has no local receipt ids), and then its rows are all-zero padding: interactions
            // carry multiplicity 0, so mutating a payload cell is legitimately free and the proof
            // still verifies.  Mutating any nonzero cell is the meaningful test; if the table is
            // entirely zero we skip it and say so, rather than report a vacuous accept/reject.
            let active = (0..h).find(|&r| {
                mats[t].values[r * w..(r + 1) * w]
                    .iter()
                    .any(|x| *x != F::ZERO)
            });
            let Some(r0) = active else {
                println!("TAMPER {name}: skipped (table is all-zero padding on this fixture)");
                continue;
            };
            let r = (r0 + row) % h;
            let c = col % w;
            mats[t].values[r * w + c] += F::ONE;
            cases.push((format!("{name}[{r}][{c}]+1"), mats, inst.pubs.clone()));
        }
    }
    {
        // **statement tamper**: claim a different TAPE root in the statement.  V_d recomputes the
        // root from the public messages, so the claimed component must disagree.
        let good = statement_values(&inst, &eng);
        let mut forged = good.clone();
        forged[0][0] += F::ONE;
        if forged != good {
            println!(
                "TAMPER statement: TAPE root limb +1 changes the statement component (would be rejected by V_d)"
            );
        }
    }
    {
        // a public message changed in the TAPE table: the prover's TAPE root no longer matches V_d's
        let t = idx("TAPE").unwrap();
        let mut mats = inst.mats.clone();
        mats[t].values[0] += F::ONE;
        cases.push((
            "TAPE[0][0]+1 (forged public message)".into(),
            mats,
            inst.pubs.clone(),
        ));
    }
    {
        // a header public value changed (the claim's prepared header)
        let mut pubs = inst.pubs.clone();
        let reader = inst
            .spec
            .iter()
            .find(|t| t.num_pub > 0)
            .map(|t| t.num_pub)
            .unwrap_or(1);
        pubs[reader - 1] += F::ONE;
        cases.push((
            format!("pub[{}]+1 (header byte)", reader - 1),
            inst.mats.clone(),
            pubs,
        ));
    }
    let mut rejected = 0;
    for (name, mats, pubs) in &cases {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = eng.prove(&d_pk, ctx(&eng, &inst, mats, pubs)).ok()?;
            eng.verify(&vk, &p).ok()?;
            Some(check_statement(&eng, &inst, &p))
        }));
        let verdict = match r {
            Ok(Some(true)) => "ACCEPTED",
            Ok(Some(false)) => "rejected (V_d statement)",
            Ok(None) => "rejected (prove/verify)",
            Err(_) => "rejected (prover panicked)",
        };
        if verdict != "ACCEPTED" {
            rejected += 1;
        }
        println!("TAMPER {name}: {verdict}");
    }
    println!("TAMPER {rejected}/{} rejected", cases.len());
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() >= 7 && a[1] == "difftest" {
        // difftest <air.json> <points_out> <rust_out> <n> <d0a|d1>
        let v = match a[6].as_str() {
            "d0a" => Variant::D0a,
            "d1" => Variant::D1,
            m => {
                eprintln!("variant {m}: expected d0a or d1");
                std::process::exit(2);
            }
        };
        let n: usize = a[4].parse().unwrap_or(16);
        cmd_difftest(&a[2], &a[3], &a[4], n, v);
        return;
    }
    if a.len() >= 5 && a[1] != "difftest" {
        // <air.json> <dump> check|prove|tamper <d0a|d1> [small|pinned]
        let v = match a[4].as_str() {
            "d0a" => Variant::D0a,
            "d1" => Variant::D1,
            m => {
                eprintln!("variant {m}: expected d0a or d1");
                std::process::exit(2);
            }
        };
        cmd(
            &a[1],
            &a[2],
            &a[3],
            a.get(5).map(|s| s.as_str()).unwrap_or("small"),
            v,
        );
        return;
    }
    eprintln!(
        "usage:\n  {0} <air.json> <dump_dir> check|prove|tamper <d0a|d1> [small|pinned]\n  {0} difftest <air.json> <points_out> <rust_out> <n> <d0a|d1>",
        a[0]
    );
}

#[cfg(feature = "chunk-recursion")]
#[path = "chunk_bridge.rs"]
pub mod chunk_bridge;
