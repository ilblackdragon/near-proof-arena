//! E2E M5d prover (lane G): the FINAL / INIT template of one chunk, on the main PQ stack.
//!
//!   nearproof-e2e-m5d <air.json> <names.json> <dump_dir> check|prove|mutant
//!
//! A copy of lane B's M5a prover (`../../m5a/prover`, unchanged modules `air.rs`, `config.rs`,
//! `sha256gen.rs`, `s384/`) with the table list taken from `names.json` (`m5d-tool air-*`) and no
//! public tape:
//! * the Lean AIR is interpreted unchanged (`air.rs`): every constraint and every interaction;
//! * the `SHA` table's trace comes from the reference generator of `ZkFormal.Sha.Gen`
//!   (`sha256gen.rs`) over the dump's `sha_msgs.json` (absent for INIT, which has no `SHA`);
//! * the SHA-512 compression chip (`s384/`, native v4) proves the dump's `comps.json`; the Lean
//!   bus `IF384` (16) is its interface bus (103);
//! * the public values are the dump's `pubs.bin`; the statement check compares the proof's public
//!   values with `stmt_pubs.bin` (what the verifier / leaf computes from the public statement and
//!   the boundary; for a mutant, the honest values).
//!
//! `check`: constraints + bus balance only. `prove`: precheck, keygen, prove, native verify,
//! statement check. `mutant`: the same without the precheck assertion; prints `REJECTED (…)` or
//! `ACCEPTED`.
mod air;
#[allow(dead_code, clippy::all)]
mod config;
mod sha256gen;
#[allow(dead_code, clippy::all)]
mod s384 {
    pub mod air;
    pub mod reference;
    pub mod trace;
}

use air::{ClassicalAir, E, JsonAir, TableSpec};
use config::{F, Sha384Config, Sha384RefEngine};
use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    codec::Encode,
    interaction::LogUpSecurityParameters,
    prover::{AirProvingContext, ColMajorMatrix, CpuColMajorBackend, DeviceDataTransporter, ProvingContext},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::Instant;

const P: u64 = 0x7800_0001;
const LEAN_IF: u16 = 16;

fn set_levers() {
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
}

fn map_bus(b: u16) -> u16 {
    if b == LEAN_IF { s384::air::BUS_IF } else { b }
}

/// seg-v1 shape (pq-state-port, as lane B's M5a) with log message length 6 and the interaction
/// budget 2^30.
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

fn read_pubs(path: &std::path::Path) -> Vec<F> {
    let pb = std::fs::read(path).unwrap_or_else(|e| panic!("{path:?}: {e}"));
    pb.chunks(4).map(|c| F::new(u32::from_le_bytes(c.try_into().unwrap()))).collect()
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

enum Native {
    Sha512,
    Table,
}

struct Inst {
    spec: Vec<TableSpec>,
    mats: Vec<RowMajorMatrix<F>>,
    pubs: Vec<F>,
    stmt_pubs: Vec<F>,
    native: Vec<(Native, RowMajorMatrix<F>)>,
    chip_if: BTreeMap<Key, u64>,
    n_comps: usize,
}

fn load(air_path: &str, names_path: &str, dir: &str) -> Inst {
    let text = std::fs::read_to_string(air_path).unwrap();
    let nv: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(names_path).unwrap()).unwrap();
    let names: Vec<String> = nv["tables"].as_array().unwrap().iter().map(|x| x.as_str().unwrap().to_string()).collect();
    let nref: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
    let mut cl = ClassicalAir::parse(&text, &nref);
    assert_eq!(cl.tables.len(), names.len());
    for t in cl.tables.iter_mut() {
        for i in t.inters.iter_mut() {
            i.bus = map_bus(i.bus);
        }
    }
    let d = std::path::Path::new(dir);
    let pubs = read_pubs(&d.join("pubs.bin"));
    let stmt_pubs = read_pubs(&d.join("stmt_pubs.bin"));
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
    let h = s384::trace::main_height(comps.len());
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
    Inst { spec, mats, pubs, stmt_pubs, native, chip_if, n_comps: comps.len() }
}

fn precheck(inst: &Inst) -> Result<(), String> {
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        check_constraints(t, m, &inst.pubs)?;
    }
    let mut net = inst.chip_if.clone();
    for (t, m) in inst.spec.iter().zip(&inst.mats) {
        traffic(t, m, &inst.pubs, &mut net);
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

fn ctx(inst: &Inst) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
    let mut out = vec![];
    for (i, m) in inst.mats.iter().enumerate() {
        let t = &inst.spec[i];
        let pv: Vec<F> = (0..t.num_pub).map(|k| inst.pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        out.push((i, AirProvingContext::simple(ColMajorMatrix::from_row_major(m), pv)));
    }
    let base = inst.mats.len();
    for (j, (_, m)) in inst.native.iter().enumerate() {
        out.push((base + j, AirProvingContext::simple(ColMajorMatrix::from_row_major(m), vec![])));
    }
    ProvingContext::new(out)
}

/// The statement check: every table's public values are the statement's.
fn check_statement(inst: &Inst, proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> bool {
    inst.spec.iter().enumerate().all(|(i, t)| {
        let pv: Vec<F> = (0..t.num_pub).map(|k| inst.stmt_pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        proof.public_values[i] == pv
    })
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
        println!(
            "TABLE {:<6} width {:>4} height 2^{:<2} cells {:>9} constraints {:>5} interactions {:>5} deg {}",
            t.name, m.width, h.trailing_zeros(), h * m.width, t.constraints.len(), t.inters.len(), d
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
    println!("CELLS {cells}; compressions {}", inst.n_comps);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 5 {
        eprintln!("usage: {} <air.json> <names.json> <dump_dir> check|prove|mutant", args[0]);
        std::process::exit(2);
    }
    let (air_path, names_path, dir, mode) = (&args[1], &args[2], &args[3], args[4].as_str());
    set_levers();
    let t0 = Instant::now();
    let inst = load(air_path, names_path, dir);
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
    let degree = inst.spec.iter().flat_map(|t| t.constraints.iter().map(deg)).max().unwrap_or(2).max(s384::air::DEGREE);
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
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| eng.prove(&d_pk, ctx(&inst)).ok()));
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
    let st = check_statement(&inst, &proof);
    println!(
        "TIME prove {t_prove:.2}s verify {t_verify:.4}s threads {} peak_rss_kib {} proof_bytes {sz}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_default(),
        peak_rss_kib()
    );
    match (ver.is_ok(), st) {
        (true, true) => {
            println!("VERIFY OK (native SWIRL verifier); statement check (public values): OK");
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
