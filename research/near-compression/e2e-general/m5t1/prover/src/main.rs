//! E2E M5-T1 prover: the runtime rows of a chunk's incoming FunctionCall receipts, on the main PQ
//! stack (lane B's harness, `../m5a/prover`, without the SHA-512 chip).
//!
//!   nearproof-e2e-m5t1 <m5t1.json> <dump_dir> check|prove|mutant
//!
//! * the Lean AIR (`m5t1-tool air`) is interpreted unchanged (`air.rs`): every constraint of
//!   `Table.allConstraints` and every interaction;
//! * the `SHA` table's trace comes from the reference generator of `ZkFormal.Sha.Gen`
//!   (`sha256gen.rs`) over the dump's `sha_msgs.json`;
//! * `TAPE` is the statement (cached, committed by the verifier from the public data): the receipt
//!   list digest (`w.appliedReceiptsHash`), each receipt's outcome leaf and outgoing refund hash;
//!   `XTAPE` (cached, public on T1) stands in for lane A's Wasm call and lane B's account read /
//!   write, the buses this template shares with them;
//! * the public values are the env (gas price, height, …) and the receipt state's totals in / out.
//!
//! `check`: constraints + bus balance only.  `prove`: precheck, keygen, prove, native verify,
//! statement check.  `mutant`: the same without the precheck assertion; prints `REJECTED (…)` or
//! `ACCEPTED`.
mod air;
#[allow(dead_code, clippy::all)]
mod config;
mod sha256gen;

use air::{ClassicalAir, E, JsonAir, TableSpec};
use config::{F, Sha384Config, Sha384RefEngine};
use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
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

fn set_levers() {
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
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
    };
    (spec, RowMajorMatrix::new(v, width))
}

const NAMES: &[&str] = &["SHA", "RNG", "SCHT", "MSG", "DG", "RX"];
const P: u64 = 0x7800_0001;

struct Inst {
    spec: Vec<TableSpec>,
    mats: Vec<RowMajorMatrix<F>>,
    pubs: Vec<F>,
    /// the statement tape and the T1 stand-in tape (public), as net message counts
    tapes: Vec<(String, BTreeMap<Key, u64>)>,
}

fn read_tape(path: &std::path::Path) -> BTreeMap<Key, u64> {
    let pm: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let mut tape = BTreeMap::new();
    for x in pm.as_array().unwrap() {
        let bus = x[0].as_u64().unwrap() as u16;
        let send = x[1].as_bool().unwrap();
        let msg: Vec<u32> = x[2].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as u32).collect();
        add(&mut tape, (bus, msg), if send { 1 } else { P - 1 });
    }
    tape
}

fn load(air_path: &str, dir: &str) -> Inst {
    let text = std::fs::read_to_string(air_path).unwrap();
    let cl = ClassicalAir::parse(&text, NAMES);
    assert_eq!(cl.tables.len(), NAMES.len());
    let d = std::path::Path::new(dir);
    let pb = std::fs::read(d.join("pubs.bin")).unwrap();
    let pubs: Vec<F> = pb.chunks(4).map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap()))).collect();
    let (mut spec, mut mats) = (vec![], vec![]);
    for t in cl.tables.iter() {
        let m = if t.name == "SHA" {
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
            let (cells, _nrows, _log) = sha256gen::sha_cells(&msgs);
            RowMajorMatrix::new(cells.iter().map(|&x| F::new(x as u32)).collect(), sha256gen::WIDTH)
        } else {
            read_trace(&d.join(format!("{}.bin", t.name)))
        };
        assert_eq!(m.width, t.width, "{}: width", t.name);
        let h = m.values.len() / m.width;
        assert!(h.is_power_of_two() && h >= 4, "{}: height {h}", t.name);
        assert!(h.trailing_zeros() as usize <= t.max_log, "{}: maxLog", t.name);
        spec.push(t.clone());
        mats.push(m);
    }
    let mut tapes = vec![];
    for name in ["TAPE", "XTAPE"] {
        let tape = read_tape(&d.join(format!("{}.json", name.to_lowercase())));
        let (ts, tm) = harness(name, &tape, true);
        spec.push(ts);
        mats.push(tm);
        tapes.push((name.to_string(), tape));
    }
    Inst { spec, mats, pubs, tapes }
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

fn ctx(eng: &Sha384RefEngine, inst: &Inst, mats: &[RowMajorMatrix<F>], pubs: &[F]) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
    let mut out = vec![];
    for (i, m) in mats.iter().enumerate() {
        let t = &inst.spec[i];
        let pv: Vec<F> = (0..t.num_pub).map(|k| pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        if !t.cached {
            out.push((i, AirProvingContext::simple(ColMajorMatrix::from_row_major(m), pv)));
        } else {
            let cm = ColMajorMatrix::from_row_major(m);
            let (commitment, data) = eng.device().commit(&[&cm]).expect("commit cached");
            let cached = CommittedTraceData { commitment, trace: cm, data: Arc::new(data) };
            let h = m.values.len() / m.width;
            let empty = ColMajorMatrix::from_row_major(&RowMajorMatrix::new(vec![F::ZERO; h], 1));
            out.push((i, AirProvingContext { cached_mains: vec![cached], common_main: empty, public_values: pv }));
        }
    }
    ProvingContext::new(out)
}

/// The verifier's statement check: each tape's commitment equals the one it recomputes from the
/// public messages, and the public values are the statement's.
fn check_statement(eng: &Sha384RefEngine, inst: &Inst, want_pubs: &[F], proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> bool {
    let mut ok = true;
    for (name, tape) in &inst.tapes {
        let ti = inst.spec.iter().position(|t| &t.name == name).unwrap();
        let (_, tm) = harness(name, tape, true);
        let want = eng.device().commit(&[&ColMajorMatrix::from_row_major(&tm)]).expect("tape root").0;
        ok &= matches!(&proof.trace_vdata[ti], Some(v) if v.cached_commitments.len() == 1 && v.cached_commitments[0] == want);
    }
    let pv_ok = inst.spec.iter().enumerate().all(|(i, t)| {
        let pv: Vec<F> = (0..t.num_pub).map(|k| want_pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        proof.public_values[i] == pv
    });
    ok && pv_ok
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
    let mut used = 0usize;
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        let h = m.values.len() / m.width;
        cells += h * m.width;
        let nz = (0..h).filter(|r| m.values[r * m.width..(r + 1) * m.width].iter().any(|v| *v != F::ZERO)).count();
        used += nz * m.width;
        let d = t.constraints.iter().map(deg).max().unwrap_or(0);
        let ni = t.harness.as_ref().map(|h| h.1.len()).unwrap_or(t.inters.len());
        println!(
            "TABLE {:<6} width {:>5} height 2^{:<2} rows-used {:>6} cells {:>9} constraints {:>5} interactions {:>5} deg {}",
            t.name, m.width, h.trailing_zeros(), nz, h * m.width, t.constraints.len(), ni, d
        );
    }
    println!("CELLS committed {cells} (non-zero rows x width {used})");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: {} <m5t1.json> <dump_dir> check|prove|mutant", args[0]);
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
    let n_stack = [14usize, 18, 22].into_iter().find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24).unwrap_or(22);
    let env_n = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<usize>().ok());
    let n_stack = env_n("N_STACK").unwrap_or(n_stack);
    let w_stack = env_n("W_STACK").unwrap_or((total.div_ceil(1 << (n_stack + 2)) + 4).max(8));
    let degree = inst.spec.iter().flat_map(|t| t.constraints.iter().map(deg)).max().unwrap_or(2);
    let prm = params(n_stack, w_stack, degree);
    println!("PARAMS n_stack {} w_stack {} degree {}", prm.n_stack, prm.w_stack, prm.max_constraint_degree);
    let eng = Sha384RefEngine::new(prm);
    let airs = airs(&inst);
    let t1 = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    println!("TIME keygen {:.2}s", t1.elapsed().as_secs_f64());
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!("SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}", b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits);
    let d_pk = eng.device().transport_pk_to_device(&pk);
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
    // claimed ones) and the two tapes
    let want_pubs: Vec<F> = match std::fs::read(std::path::Path::new(dir).join("expected_pubs.bin")) {
        Ok(pb) => pb.chunks(4).map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap()))).collect(),
        Err(_) => inst.pubs.clone(),
    };
    let st = check_statement(&eng, &inst, &want_pubs, &proof);
    println!("TIME prove {t_prove:.2}s verify {t_verify:.4}s threads {} peak_rss_kib {} proof_bytes {sz}", std::env::var("RAYON_NUM_THREADS").unwrap_or_default(), peak_rss_kib());
    match (ver.is_ok(), st) {
        (true, true) => {
            println!("VERIFY OK (native SWIRL verifier); statement check (TAPE/XTAPE roots + public values): OK");
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
