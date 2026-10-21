//! Direct-Wasm base-layer prover slice (lane/pq-wasm-base): AIR set `wasm-base-v1`, family F1, on
//! the unified SWIRL backend (BabyBear, Ext12, SHA-384, T*, 42-byte digests, stacked WHIR).
//!
//! Usage (run `setup.sh` first; the hash levers are fixed by this binary):
//!   nearproof-wasm-base check <air.json> <prep.json>            trace + constraint/bus pre-check
//!   nearproof-wasm-base prove <air.json> <prep.json> [small|pinned]   keygen, debug, prove, verify, sizes
//!   nearproof-wasm-base tamper <air.json> <prep.json>           mutation tests (debug checker + verifier)
//!   nearproof-wasm-base difftest <air.json> <points.txt> <rust.jsonl> [n]   random points for the
//!       Lean/Rust differential test (Rust side: the verifying key's symbolic DAG)
#[allow(dead_code, clippy::all)]
mod config;
mod sha;
mod air;
mod tracegen;

use air::{AirSpec, JsonAir};
use config::{F, Sha384Config, Sha384RefEngine};
use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    air_builders::symbolic::{SymbolicExpressionNode, symbolic_variable::Entry},
    codec::Encode,
    interaction::LogUpSecurityParameters,
    keygen::types::MultiStarkVerifyingKey,
    prover::{AirProvingContext, ColMajorMatrix, CommittedTraceData, CpuColMajorBackend, DeviceDataTransporter, ProvingContext, TraceCommitter},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;
use std::time::Instant;
use tracegen::{Gen, Prep, HOST_NARGS};

fn set_levers() {
    // The pinned base shape: 42-byte digests, coset leaves, T* (read once by `sha_levers`).
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
}

/// seg-v1 pinned shape (DESIGN-BASE §3): c = 1, b = 1, m = 16, k1 = 1, k = 4, final 2^7, keep-domain,
/// WHIR-Y, multiproof, z = 24, target 268; `n_stack ∈ {10, 14, 18, 22}` (22 = pinned 2^24).
pub fn seg_v1_params(n_stack: usize, w_stack: usize, max_degree: usize) -> SystemParams {
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
            // z = 24 (pinned); WASMBASE_POW overrides it only for prover-work measurements
            query_phase_pow_bits: std::env::var("WASMBASE_POW").ok().and_then(|v| v.parse().ok()).unwrap_or(24),
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
        // The widest interaction message is HOSTQ: `4 + 2·Host.nArgs = 22` fields, so the backend's
        // keygen check `message.len() + 1 <= 2^log_max_message_length` needs `2^l >= 23`, i.e. `l >= 5`.
        // We keep the NV envelope value `7` (128 fields) so the join lane sees one number; the extra
        // 2 bits of LogUp slack cost 3 LogUp bits (333.3 -> 330.3 at 2^28 interactions), which does
        // not move the printed total (proximity-bound).
        logup: LogUpSecurityParameters { max_interaction_count: 1 << 28, log_max_message_length: 7, pow_bits: 0 },
        max_constraint_degree: max_degree,
    }
}

fn load(air_path: &str) -> AirSpec {
    AirSpec::parse(&std::fs::read_to_string(air_path).unwrap())
}

fn airs(spec: &AirSpec) -> Vec<AirRef<Sha384Config>> {
    spec.tables
        .iter()
        .map(|t| {
            let np = if JsonAir::reads_pub(t) { spec.num_pub } else { 0 };
            Arc::new(JsonAir { spec: t.clone(), num_pub: np }) as AirRef<Sha384Config>
        })
        .collect()
}

/// Split a row-major matrix into its first `c` columns and the rest.
fn split_cols(m: &RowMajorMatrix<F>, c: usize) -> (RowMajorMatrix<F>, RowMajorMatrix<F>) {
    let w = m.width;
    let (mut a, mut b) = (vec![], vec![]);
    for row in m.values.chunks(w) {
        a.extend_from_slice(&row[..c]);
        b.extend_from_slice(&row[c..]);
    }
    (RowMajorMatrix::new(a, c), RowMajorMatrix::new(b, w - c))
}

fn ctx(eng: &Sha384RefEngine, spec: &AirSpec, g: &Gen) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
    ProvingContext::new(
        g.mats
            .iter()
            .enumerate()
            .map(|(i, m)| {
                let pv = if JsonAir::reads_pub(&spec.tables[i]) { g.pubs.clone() } else { vec![] };
                let c = spec.tables[i].cached;
                if c == 0 {
                    (i, AirProvingContext::simple(ColMajorMatrix::from_row_major(m), pv))
                } else {
                    let (cm, rest) = split_cols(m, c);
                    let cm = ColMajorMatrix::from_row_major(&cm);
                    let (commitment, data) = eng.device().commit(&[&cm]).expect("commit cached");
                    let cached = CommittedTraceData { commitment, trace: cm, data: Arc::new(data) };
                    (i, AirProvingContext {
                        cached_mains: vec![cached],
                        common_main: ColMajorMatrix::from_row_major(&rest),
                        public_values: pv,
                    })
                }
            })
            .collect(),
    )
}

/// **V_d side of the statement**: `code_root` = commitment to the canonical CODE matrix of the
/// checked code under the base shape's parameters (a deterministic function of the contract code,
/// precomputable per `code_hash`).
fn code_root(eng: &Sha384RefEngine, records: &[[u64; 8]]) -> <Sha384Config as openvm_stark_backend::StarkProtocolConfig>::Digest {
    let cm = ColMajorMatrix::from_row_major(&tracegen::code_matrix(records));
    eng.device().commit(&[&cm]).expect("code root").0
}

/// `data_root` = commitment to the canonical DATA matrix (the initial-memory image).
fn data_root(eng: &Sha384RefEngine, prep: &Prep) -> <Sha384Config as openvm_stark_backend::StarkProtocolConfig>::Digest {
    let cm = ColMajorMatrix::from_row_major(&tracegen::data_matrix(prep));
    eng.device().commit(&[&cm]).expect("data root").0
}

/// `func_root` = commitment to the canonical FUNC matrix (the module's function table).
fn func_root(eng: &Sha384RefEngine, prep: &Prep) -> <Sha384Config as openvm_stark_backend::StarkProtocolConfig>::Digest {
    let cm = ColMajorMatrix::from_row_major(&tracegen::func_matrix(prep));
    eng.device().commit(&[&cm]).expect("func root").0
}

/// The statement check V_d performs on a verified base proof: the proof's cached CODE, DATA and FUNC
/// commitments equal the roots recomputed from the contract code.
fn check_code_root(
    eng: &Sha384RefEngine,
    spec: &AirSpec,
    proof: &openvm_stark_backend::proof::Proof<Sha384Config>,
    prep: &Prep,
) -> bool {
    let ok = |name: &str, want| match &proof.trace_vdata[spec.index(name)] {
        Some(v) => v.cached_commitments.len() == 1 && v.cached_commitments[0] == want,
        None => false,
    };
    ok("CODE", code_root(eng, &prep.records)) && ok("DATA", data_root(eng, prep)) && ok("FUNC", func_root(eng, prep))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn cells(g: &Gen) -> usize {
    g.mats.iter().map(|m| m.values.len()).sum()
}

fn compare_with_spec(prep: &Prep, g: &Gen) {
    let trapped = g.pubs[8] == F::from_u64(2);
    if trapped {
        // a host abort is not a Wasm trap: `callHost` returns an abort with the host error
        assert!(prep.status.starts_with("abort "), "trace trapped, spec: {}", prep.status);
    } else {
        assert_eq!(prep.status, "fin", "spec run did not finish normally");
    }
    assert_eq!(g.steps, prep.steps, "step count vs spec");
    if prep.hosts.is_empty() {
        let spent = prep.g0 - prep.g_final;
        assert_eq!(spent, prep.regular * g.s_units as u128, "gas vs spec");
    }
    if trapped {
        return;
    }
    match (g.result, prep.stack.last()) {
        (Some((tag, val)), Some((stag, slimbs))) => {
            assert_eq!(tag, *stag);
            assert_eq!(tracegen::limbs(val), *slimbs, "result vs spec");
        }
        (None, None) => {}
        _ => panic!("result arity vs spec"),
    }
}

fn generate(spec: &AirSpec, prep_path: &str) -> (Prep, Gen) {
    let prep = Prep::parse(&std::fs::read_to_string(prep_path).unwrap());
    let g = tracegen::generate(spec, &prep);
    compare_with_spec(&prep, &g);
    (prep, g)
}

fn report_shape(spec: &AirSpec, g: &Gen) {
    let mut active_cells = 0;
    for (i, t) in spec.tables.iter().enumerate() {
        let w = t.cols.len();
        let h = g.mats[i].values.len() / w;
        let rows = g.rows_per_table[i].1;
        active_cells += rows * w;
        println!(
            "TABLE {:<9} width {:>3} rows {:>6} height {:>6} cells {:>9} constraints {:>3} interactions {:>3} degree {}",
            t.name, w, rows, h, h * w, t.constraints.len(), t.inters.len(), t.degree
        );
    }
    println!("STEPS {} S_UNITS {} CELLS_TOTAL {} CELLS_ACTIVE {}", g.steps, g.s_units, cells(g), active_cells);
}

fn cmd_check(air_path: &str, prep_path: &str) {
    let spec = load(air_path);
    let (_prep, g) = generate(&spec, prep_path);
    tracegen::check_constraints(&spec, &g).expect("constraints");
    tracegen::check_buses(&spec, &g).expect("buses");
    report_shape(&spec, &g);
    println!("CHECK OK result {:?}", g.result);
}

/// `hostb-dump <air.json> <prep.json>`: print every HOSTB row as `ts dir pos byte len hid`.
///
/// Exists because a HOSTB group that is **absent** still balances its bus, so every constraint and
/// bus check passes while a host call's payload silently is not carried.  That is exactly how the
/// `[8, 9, 10, 15]` id bug (`log_utf8` is 45) survived a green KAT: no group was emitted, and no
/// check missed one.  Printing the rows makes "did the payload actually appear" observable.
fn cmd_hostb_dump(air_path: &str, prep_path: &str) {
    let spec = load(air_path);
    let (_prep, g) = generate(&spec, prep_path);
    let (idx, w) = spec
        .tables
        .iter()
        .enumerate()
        .find(|(_, t)| t.name == "HOSTB")
        .map(|(i, t)| (i, t.cols.len()))
        .expect("no HOSTB table in this AIR");
    let m = &g.mats[idx];
    let col = |r: usize, c: usize| m.values[r * w + c].as_canonical_u32() as u64;
    let n = m.values.len() / w;
    let mut printed = 0;
    for r in 0..n {
        // `act` is column 7; padding rows have `act = 0`
        if col(r, 7) == 1 {
            println!(
                "HOSTB ts={} dir={} pos={} byte={} len={} hid={}",
                col(r, 0), col(r, 1), col(r, 2), col(r, 3), col(r, 4), col(r, 5)
            );
            printed += 1;
        }
    }
    println!("HOSTB_ROWS {printed}");
}

fn choose_shape(g: &Gen, which: &str, degree: usize) -> SystemParams {
    let total = cells(g);
    let maxh = g.mats.iter().map(|m| m.values.len() / m.width).max().unwrap();
    let n_stack = match which {
        "pinned" => 22,
        _ => [14, 18, 22]
            .into_iter()
            .find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24)
            .unwrap_or(22),
    };
    let w_stack = total.div_ceil(1 << (n_stack + 2)) + 4;
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
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).map(|l| l.split_whitespace().nth(1).unwrap().parse().unwrap()))
        .unwrap_or(0)
}

fn cmd_prove(air_path: &str, prep_path: &str, which: &str) {
    set_levers();
    let spec = load(air_path);
    let t0 = Instant::now();
    let (_prep, g) = generate(&spec, prep_path);
    let t_gen = t0.elapsed().as_secs_f64();
    tracegen::check_constraints(&spec, &g).expect("constraints");
    tracegen::check_buses(&spec, &g).expect("buses");
    report_shape(&spec, &g);
    let degree = spec.tables.iter().map(|t| t.degree).max().unwrap();
    let params = choose_shape(&g, which, degree.max(2));
    println!(
        "PARAMS n_stack {} log_h {} w_stack {} degree {} queries {:?} pow {}",
        params.n_stack,
        params.l_skip + params.n_stack,
        params.w_stack,
        params.max_constraint_degree,
        params.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
        params.whir.query_phase_pow_bits
    );
    let eng = Sha384RefEngine::new(params);
    let airs = airs(&spec);
    let t1 = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    let t_keygen = t1.elapsed().as_secs_f64();
    for (i, a) in vk.inner.per_air.iter().enumerate() {
        println!(
            "VK {:<9} degree {} constraints {} interactions {} dag_nodes {}",
            spec.tables[i].name,
            a.max_constraint_degree,
            a.symbolic_constraints.constraints.constraint_idx.len(),
            a.symbolic_constraints.interactions.len(),
            a.symbolic_constraints.constraints.nodes.len()
        );
    }
    if std::env::var("WASMBASE_DEBUG").is_ok() {
        eng.debug(&airs, &ctx(&eng, &spec, &g));
        println!("DEBUG OK");
    }
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!(
        "SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}",
        b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits
    );
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let t2 = Instant::now();
    let proof = eng.prove(&d_pk, ctx(&eng, &spec, &g)).expect("prove");
    let t_prove = t2.elapsed().as_secs_f64();
    let t3 = Instant::now();
    eng.verify(&vk, &proof).expect("verify");
    let t_verify = t3.elapsed().as_secs_f64();
    println!("PROOF {}", census(&proof));
    // statement: code_hash (sha256 of the contract code, if given) and code_root, checked like V_d
    let prep = _prep;
    assert!(check_code_root(&eng, &spec, &proof, &prep), "code_root mismatch");
    let root = code_root(&eng, &prep.records);
    let rb: Vec<u8> = root.iter().flat_map(|w| w.to_be_bytes()).collect();
    let code_hash = std::env::var("WASMBASE_WASM").ok().map(|p| {
        use sha2::Digest;
        hex(&sha2::Sha256::digest(std::fs::read(p).unwrap()))
    });
    println!("STATEMENT code_root {} code_hash {} (V_d: recomputed root matches the proof's cached CODE commitment)",
        hex(&rb), code_hash.unwrap_or_else(|| "-".into()));
    println!(
        "TIME tracegen {t_gen:.3}s keygen {t_keygen:.3}s prove {t_prove:.3}s verify {t_verify:.4}s threads {} peak_rss_kib {}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_default(),
        peak_rss_kib()
    );
    if let Ok(path) = std::env::var("WASMBASE_PROOF_OUT") {
        let mut bytes = Vec::new();
        proof.encode(&mut bytes).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    println!("PROVE OK steps {} result {:?}", g.steps, g.result);
}

/// Mutation tests: each tamper must be rejected by the native verifier (and is reported against
/// the interpreter pre-checks for diagnosis).
fn cmd_tamper(air_path: &str, prep_path: &str) {
    set_levers();
    let spec = load(air_path);
    let (prep, g) = generate(&spec, prep_path);
    let degree = spec.tables.iter().map(|t| t.degree).max().unwrap();
    let params = choose_shape(&g, "small", degree);
    let eng = Sha384RefEngine::new(params);
    let airs = airs(&spec);
    let (pk, vk) = eng.keygen(&airs);
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let honest = eng.prove(&d_pk, ctx(&eng, &spec, &g)).expect("prove honest");
    eng.verify(&vk, &honest).expect("honest verifies");
    assert!(check_code_root(&eng, &spec, &honest, &prep), "honest code_root");
    println!("TAMPER honest proof verifies and its code_root matches");
    let tb = |n: &str| spec.index(n);
    let col = |t: usize, c: &str| spec.tables[t].col(c);
    type Mut = Box<dyn Fn(&mut Gen)>;
    let cell = |t: usize, r: usize, c: usize, f: Box<dyn Fn(F) -> F>| -> Mut {
        Box::new(move |g: &mut Gen| {
            let w = g.mats[t].width;
            let v = &mut g.mats[t].values[r * w + c];
            *v = f(*v);
        })
    };
    let plus1: fn() -> Box<dyn Fn(F) -> F> = || Box::new(|v| v + F::ONE);
    let mut cases: Vec<(String, Mut)> = vec![];
    let find = |t: usize, c: &str, v: u64| -> Option<usize> {
        let (w, k) = (g.mats[t].width, col(t, c));
        (0..g.rows_per_table[t].1).find(|&r| g.mats[t].values[r * w + k] == F::from_u64(v))
    };
    for (name, c) in [("ADD", "r0"), ("ADD", "c0"), ("MUL", "rb0"), ("MUL", "cy0"), ("BIT", "rb0"), ("SHIFT", "P0"),
        ("SHIFT", "kb0"), ("CMP", "d0"), ("CMP", "br0"), ("CMP", "inv"), ("CONST", "imm0"), ("LOCAL", "L0"),
        ("CTRL", "tgt"), ("STACK", "V1_0"), ("STACK", "A0"), ("ADD", "ta"), ("ADD", "h"), ("ADD", "fee"), ("CMP", "S"),
        ("DIV", "Q0"), ("DIV", "R0"), ("DIV", "tz"), ("DIV", "tov"), ("DIV", "res0"), ("DIV", "cy0"), ("DIV", "hbA"),
        ("DRAIN", "v0"), ("DRAIN", "act"), ("ADD", "fr_sb"), ("ADD", "fr_cid"), ("LOCAL", "fr_cid"),
        ("LOCAL", "inv_sp"), ("CTRL", "fr_cid"), ("BOUNDARY", "sbf"), ("BOUNDARY", "cidf"),
        ("LOAD", "b0"), ("LOAD", "r0"), ("LOAD", "e0"), ("LOAD", "sbit"), ("LOAD", "tb0"), ("STORE", "vb0"),
        ("STORE", "ob0"), ("STORE", "e1"), ("MEMINIT", "bv"), ("MEMINIT", "ad"), ("MEMINIT", "zd"), ("DRAIN", "space")] {
        let t = tb(name);
        if g.rows_per_table[t].1 == 0 {
            continue;
        }
        // V1 (the select's first operand) is only read by `select` rows: on a `drop` row it is a free
        // witness that does not change the statement, so target a select row
        if name == "STACK" && c == "V1_0" {
            if let Some(r) = find(t, "f_sel", 1) {
                cases.push((format!("STACK[select row {r}].V1_0+1"), cell(t, r, col(t, c), plus1())));
            }
            continue;
        }
        // CMP.inv is only pinned when the difference limbs are non-zero (on an equal / zero operand
        // it is a free witness, `zsum · inv` with `zsum = 0`), so target such a row
        if name == "CMP" && c == "inv" {
            let w = g.mats[t].width;
            let d0 = col(t, "d0");
            if let Some(r) = (0..g.rows_per_table[t].1)
                .find(|&r| (0..4).any(|i| g.mats[t].values[r * w + d0 + i] != F::ZERO))
            {
                cases.push((format!("CMP[row {r}].inv+1"), cell(t, r, col(t, c), plus1())));
            }
            continue;
        }
        cases.push((format!("{name}.{c}+1"), cell(t, 0, col(t, c), plus1())));
    }
    // a taken/untaken conditional branch with a forged condition limb
    let tc = tb("CTRL");
    let jif = col(tc, "f_jif");
    if let Some(r) = (0..g.rows_per_table[tc].1).find(|&r| g.mats[tc].values[r * g.mats[tc].width + jif] == F::ONE) {
        cases.push((format!("CTRL[jif row {r}].c0+1"), cell(tc, r, col(tc, "c0"), plus1())));
    }
    // a free witness that does not change the statement (inv of a zero condition) is NOT a
    // soundness issue; recorded as such rather than counted
    let tcode = tb("CODE");
    cases.push(("CODE.mult[0]+1".into(), cell(tcode, 0, col(tcode, "mult"), plus1())));
    cases.push(("RANGE16.v[5]+1".into(), cell(tb("RANGE16"), 5, 0, plus1())));
    cases.push(("BYTE.x0[1] flip".into(), cell(tb("BYTE"), 1, 0, Box::new(|v| F::ONE - v))));
    cases.push(("pub.N+1".into(), Box::new(|g: &mut Gen| g.pubs[0] += F::ONE)));
    cases.push(("pub.S+1".into(), Box::new(|g: &mut Gen| g.pubs[1] += F::ONE)));
    // after a trap the result fields are not part of the statement (the result receive has count 0)
    if g.pubs[8] == F::ONE {
        cases.push(("pub.result+1".into(), Box::new(|g: &mut Gen| g.pubs[4] += F::ONE)));
    }
    cases.push(("pub.status 1<->2".into(), Box::new(|g: &mut Gen| g.pubs[8] = F::from_u64(3) - g.pubs[8])));
    cases.push(("CODE.op[0]+1".into(), cell(tcode, 0, col(tcode, "op"), plus1())));
    let tdata = tb("DATA");
    cases.push(("DATA.byte[0]+1 (data_root)".into(), cell(tdata, 0, col(tdata, "byte"), plus1())));
    if g.rows_per_table[tb("MEMINIT")].1 >= 2 {
        let tm = tb("MEMINIT");
        let c = col(tm, "ad");
        cases.push(("MEMINIT dup address".into(), Box::new(move |g: &mut Gen| {
            let w = g.mats[tm].width;
            g.mats[tm].values[w + c] = g.mats[tm].values[c];
        })));
    }
    cases.push(("CODE.h[0]+1".into(), cell(tcode, 0, col(tcode, "h"), plus1())));
    // a CODE row no instruction fetches (padding, multiplicity 0): the AIR and the proof are fine;
    // only the statement check (code_root vs the contract code) can catch it
    let ncode = prep.records.len();
    if ncode < g.mats[tcode].values.len() / g.mats[tcode].width {
        cases.push((format!("CODE[pad row {ncode}].x0+1 (code_root)"), cell(tcode, ncode, col(tcode, "x0"), plus1())));
    }
    // globals (space 2): forged global values, indices, spaces, initial and final values
    let tl = tb("LOCAL");
    if let Some(r) = find(tl, "f_gget", 1) {
        for c in ["L0", "idx", "inv_sp", "tL"] {
            cases.push((format!("LOCAL[global.get row {r}].{c}+1"), cell(tl, r, col(tl, c), plus1())));
        }
        let (cg, cl) = (col(tl, "f_gget"), col(tl, "f_get"));
        cases.push((format!("LOCAL[global.get row {r}] as local.get"), Box::new(move |g: &mut Gen| {
            let w = g.mats[tl].width;
            g.mats[tl].values[r * w + cg] = F::ZERO;
            g.mats[tl].values[r * w + cl] = F::ONE;
        })));
    }
    if let Some(r) = find(tl, "f_gset", 1) {
        cases.push((format!("LOCAL[global.set row {r}].V0+1"), cell(tl, r, col(tl, "V0"), plus1())));
        let (cg, cs) = (col(tl, "f_gset"), col(tl, "f_set"));
        cases.push((format!("LOCAL[global.set row {r}] as local.set"), Box::new(move |g: &mut Gen| {
            let w = g.mats[tl].width;
            g.mats[tl].values[r * w + cg] = F::ZERO;
            g.mats[tl].values[r * w + cs] = F::ONE;
        })));
    }
    if !prep.globals.is_empty() {
        let pg = 11 + prep.local_tags.len();
        cases.push(("pub.global0.l0+1".into(), Box::new(move |g: &mut Gen| g.pubs[pg + 1] += F::ONE)));
        cases.push(("pub.global0.tag flip".into(), Box::new(move |g: &mut Gen| g.pubs[pg] = F::ONE - g.pubs[pg])));
        let td = tb("DRAIN");
        if let Some(r) = find(td, "space", 2) {
            cases.push((format!("DRAIN[global row {r}].v0+1"), cell(td, r, col(td, "v0"), plus1())));
            cases.push((format!("DRAIN[global row {r}].act=0"), cell(td, r, col(td, "act"), Box::new(|_| F::ZERO))));
        }
    }
    // calls (family 4): forged callee, shape, charge, prologue, params, local types, budget, frames
    let tcall = tb("CALL");
    if g.rows_per_table[tcall].1 > 0 {
        let get = |c: &str| g.mats[tcall].values[col(tcall, c)].as_canonical_u32() as u64;
        let (np, nl) = (get("shape") % 128, get("shape") / 128);
        for c in ["entry", "shape", "charge", "pro", "m0", "n0", "n1", "r0", "tpb", "sbn0", "ts0", "fr_sb", "fr_cid", "S",
            "fee"] {
            cases.push((format!("CALL.{c}+1"), cell(tcall, 0, col(tcall, c), plus1())));
        }
        if np > 0 {
            for c in ["P0_0", "tP0"] {
                cases.push((format!("CALL.{c}+1"), cell(tcall, 0, col(tcall, c), plus1())));
            }
            cases.push(("CALL.tagP0 flip".into(), cell(tcall, 0, col(tcall, "tagP0"), Box::new(|v| F::ONE - v))));
            cases.push((format!("CALL.pf{} (drop a param)", np - 1), cell(tcall, 0, col(tcall, &format!("pf{}", np - 1)),
                Box::new(|_| F::ZERO))));
        }
        if np < 8 && np < nl {
            cases.push((format!("CALL.pf{np} (extra param)"), cell(tcall, 0, col(tcall, &format!("pf{np}")), Box::new(|_| F::ONE))));
        }
        if nl > np {
            cases.push((format!("CALL.tg{np} flip (declared local type)"), cell(tcall, 0, col(tcall, &format!("tg{np}")),
                Box::new(|v| F::ONE - v))));
        }
        if nl < 64 {
            cases.push((format!("CALL.af{nl} (extra local)"), cell(tcall, 0, col(tcall, &format!("af{nl}")), Box::new(|_| F::ONE))));
        }
        cases.push(("CALL.act=0".into(), cell(tcall, 0, col(tcall, "act"), Box::new(|_| F::ZERO))));
        let tf = tb("FUNC");
        cases.push(("FUNC.charge[0]+1 (func_root)".into(), cell(tf, 0, col(tf, "charge"), plus1())));
        cases.push(("FUNC.mult[0]+1".into(), cell(tf, 0, col(tf, "mult"), plus1())));
    }
    let tret = tb("RET");
    if let Some(r) = find(tret, "f_ret", 1) {
        for c in ["retpc", "sbc", "cidc", "charge", "tpr", "n0", "r0", "tpb", "invc", "fr_cid", "fr_sb"] {
            cases.push((format!("RET[row {r}].{c}+1"), cell(tret, r, col(tret, c), plus1())));
        }
        cases.push((format!("RET[row {r}].f_ret=0"), cell(tret, r, col(tret, "f_ret"), Box::new(|_| F::ZERO))));
    }
    if let Some(r) = find(tret, "f_rif", 1) {
        cases.push((format!("RET[rif row {r}].c0+1"), cell(tret, r, col(tret, "c0"), plus1())));
    }
    let td = tb("DRAIN");
    for (sp, what) in [(5u64, "budget"), (4, "call record")] {
        if let Some(r) = find(td, "space", sp) {
            cases.push((format!("DRAIN[{what} row {r}].v0+1"), cell(td, r, col(td, "v0"), plus1())));
        }
    }
    if let Some(r) = (0..g.rows_per_table[td].1).find(|&r| g.mats[td].values[r * g.mats[td].width + col(td, "space")].as_canonical_u32() > 16) {
        cases.push((format!("DRAIN[callee local row {r}].act=0"), cell(td, r, col(td, "act"), Box::new(|_| F::ZERO))));
        cases.push((format!("DRAIN[callee local row {r}].tp+1"), cell(td, r, col(td, "tp"), plus1())));
    }
    // host calls (README §14): HOST row, response oracle, cached host table
    let th = std::panic::catch_unwind(|| tb("HOST")).unwrap_or(usize::MAX);
    if th != usize::MAX && g.rows_per_table.get(th).map(|x| x.1).unwrap_or(0) > 0 {
        for c in ["hid", "np", "ar", "st", "nres", "ga0", "ga1", "ga2", "ga3", "r0", "r1", "r2", "r3",
            "P0_0", "tagP0", "fr_sb", "fr_cid", "S", "fee"] {
            cases.push((format!("HOST.{c}+1"), cell(th, 0, col(th, c), plus1())));
        }
        // the wide argument window (`Host.nArgs = 9`): an *absent* argument's tag, limbs and
        // presence flag are all pinned to zero, and the presence flags are prefix-closed, so
        // turning on an argument past `np` (or forging a limb of one) must be rejected
        let w = g.mats[th].width;
        let get = |r: usize, c: &str| g.mats[th].values[r * w + col(th, c)].as_canonical_u32() as u64;
        let np0 = get(0, "np");
        for j in (np0..(HOST_NARGS)).take(3) {
            let j = j as usize;
            for c in [format!("tagP{j}"), format!("P{j}_0"), format!("P{j}_3")] {
                cases.push((format!("HOST.{c}+1 (past np)"), cell(th, 0, col(th, &c), plus1())));
            }
            cases.push((format!("HOST.pf{j} (past np)"), cell(th, 0, col(th, &format!("pf{j}")), Box::new(|_| F::ONE))));
        }
        if np0 >= 2 {
            // drop a middle argument: prefix-closure / np = sum(pf) must reject it
            cases.push((format!("HOST.pf{} = 0 (drop arg)", np0 - 2),
                cell(th, 0, col(th, &format!("pf{}", np0 - 2)), Box::new(|_| F::ZERO))));
        }
        // `tP` of an *absent* argument is a free witness (its time check has count `pf = 0`), so
        // target a row whose first argument is present.
        let w = g.mats[th].width;
        let (pf0, tp0) = (col(th, "pf0"), col(th, "tP0"));
        if let Some(r) = (0..g.rows_per_table[th].1).find(|&r| g.mats[th].values[r * w + pf0] == F::ONE) {
            cases.push((format!("HOST[row {r}].tP0+1"), cell(th, r, tp0, plus1())));
        }
        cases.push(("HOST.act=0".into(), cell(th, 0, col(th, "act"), Box::new(|_| F::ZERO))));
        // Swap the host id to **another id present in the table**: the row still type-checks against
        // HOSTT, so what rejects it is the code record / HOSTQ binding.  This is the case that
        // matters for the context family, whose ids are all `np = 1` or `np = 0` in one module.
        let hid = col(th, "hid");
        let np = col(th, "np");
        let ar = col(th, "ar");
        let w = g.mats[th].width;
        let rows = g.rows_per_table[th].1;
        if let Some(r) = (0..rows).find(|&r| {
            let cur = g.mats[th].values[r * w + hid].as_canonical_u32();
            // a different id whose (np, ar) agrees, so only the *which function* part changes
            (0..prep.host_tab.len() as u32).any(|k| {
                k != cur
                    && prep.host_tab[k as usize][1] == g.mats[th].values[r * w + np].as_canonical_u32() as u64
                    && prep.host_tab[k as usize][2] == g.mats[th].values[r * w + ar].as_canonical_u32() as u64
            })
        }) {
            let cur = g.mats[th].values[r * w + hid].as_canonical_u32();
            let alt = (0..prep.host_tab.len() as u32)
                .find(|&k| {
                    k != cur
                        && prep.host_tab[k as usize][1] == g.mats[th].values[r * w + np].as_canonical_u32() as u64
                        && prep.host_tab[k as usize][2] == g.mats[th].values[r * w + ar].as_canonical_u32() as u64
                })
                .unwrap();
            cases.push((
                format!("HOST[row {r}].hid {cur} -> {alt} (same signature)"),
                cell(th, r, hid, Box::new(move |_| F::from_u64(alt as u64))),
            ));
        }
    }
    if let Ok(to) = std::panic::catch_unwind(|| tb("HOSTO")) {
        if g.rows_per_table[to].1 > 0 {
            for c in ["st", "r0", "g0", "g1", "ar", "mult", "q1", "q2", "q7"] {
                cases.push((format!("HOSTO.{c}+1"), cell(to, 0, col(to, c), plus1())));
            }
        }
    }
    if let Ok(tt) = std::panic::catch_unwind(|| tb("HOSTT")) {
        // only a row the trace actually queries (`mult > 0`) is pinned
        let w = g.mats[tt].width;
        let m = col(tt, "mult");
        if let Some(r) = (0..g.rows_per_table[tt].1).find(|&r| g.mats[tt].values[r * w + m] != F::ZERO) {
            for c in ["id", "np", "ar"] {
                cases.push((format!("HOSTT[row {r}].{c}+1 (host table)"), cell(tt, r, col(tt, c), plus1())));
            }
            cases.push((format!("HOSTT[row {r}].mult+1"), cell(tt, r, m, plus1())));
        }
    }
    if let Ok(thb) = std::panic::catch_unwind(|| tb("HOSTB")) {
        let (w, act) = (g.mats[thb].width, col(thb, "act"));
        let active: Vec<usize> = (0..g.rows_per_table[thb].1)
            .filter(|&r| g.mats[thb].values[r * w + act] == F::ONE)
            .collect();
        if let Some(&r) = active.first() {
            // byte value: the BYTE lookup and the wire message both move
            cases.push((format!("HOSTB[row {r}].byte+1"), cell(thb, r, col(thb, "byte"), plus1())));
            // non-boolean dir
            cases.push((format!("HOSTB[row {r}].dir=2"), cell(thb, r, col(thb, "dir"), Box::new(|_| F::from_u64(2)))));
            // duplicate pos inside the first group (a continuation row repeats its predecessor's)
            if let Some(&c) = active.iter().find(|&&q| q > r) {
                let (p, f) = (col(thb, "pos"), col(thb, "f"));
                cases.push((format!("HOSTB dup pos rows {r},{c}"), Box::new(move |g: &mut Gen| {
                    let w = g.mats[thb].width;
                    g.mats[thb].values[c * w + p] = g.mats[thb].values[r * w + p];
                    g.mats[thb].values[c * w + f] = F::ZERO;
                })));
            }
            // `len` changed on one row of a group: breaks cLenConst (and pos < len for the last row)
            cases.push((format!("HOSTB[row {r}].len+1"), cell(thb, r, col(thb, "len"), plus1())));
            // `hid` changed on one row: breaks cHidConst, so the group cannot be spliced onto
            // another host call
            cases.push((format!("HOSTB[row {r}].hid+1"), cell(thb, r, col(thb, "hid"), plus1())));
            // `gap` changed: pos + gap + 1 != len
            cases.push((format!("HOSTB[row {r}].gap+1"), cell(thb, r, col(thb, "gap"), plus1())));
            // `pos` pushed to 2^16: outside the R16 range the new `r16 pos` lookup enforces, so the
            // field equation `pos + gap + 1 = len` would otherwise be satisfiable mod P
            cases.push((format!("HOSTB[row {r}].pos=2^16"), cell(thb, r, col(thb, "pos"),
                Box::new(|_| F::from_u64(65536)))));
            // `len` pushed to 2^16: the same hole on the length side
            cases.push((format!("HOSTB[row {r}].len=2^16"), cell(thb, r, col(thb, "len"),
                Box::new(|_| F::from_u64(65536)))));
        }
    }
    // SHA-256: a digest bit, the digest multiplicity, a schedule word, a data flag, and the
    // message-level columns (the call summary and the register key)
    if let Ok(ts) = std::panic::catch_unwind(|| tb("SHA256")) {
        let (w, dmult) = (g.mats[ts].width, col(ts, "c543"));
        let nrows = g.rows_per_table[ts].1;
        if nrows > 0 {
            // the digest word 0 bit 0 (`colSt 0 0` = column 96) of the digest row
            if let Some(r) = (0..nrows).find(|&r| g.mats[ts].values[r * w + dmult] == F::ONE) {
                cases.push((format!("SHA256[row {r}].digest bit+1"), cell(ts, r, 96, plus1())));
                cases.push((format!("SHA256[row {r}].sh_len+1"), cell(ts, r, col(ts, "sh_len"), plus1())));
                cases.push((format!("SHA256[row {r}].sh_hid+1"), cell(ts, r, col(ts, "sh_hid"), plus1())));
                cases.push((format!("SHA256[row {r}].sh_ts+1"), cell(ts, r, col(ts, "sh_ts"), plus1())));
                cases.push((format!("SHA256[row {r}].sh_rin+1"), cell(ts, r, col(ts, "sh_rin"), plus1())));
            }
        }
        // a start row's `S` flag: the call summary's receive
        if let Some(r) = (0..nrows).find(|&r| g.mats[ts].values[r * w + col(ts, "c519")] == F::ONE) {
            cases.push((format!("SHA256[start row {r}].sh_ts+1"), cell(ts, r, col(ts, "sh_ts"), plus1())));
            cases.push((format!("SHA256[start row {r}].S=0"), cell(ts, r, col(ts, "c519"), Box::new(|_| F::ZERO))));
        }
        // a schedule word column on a round row: breaks `cSched`/`cRound`
        let round0 = col(ts, "c502");
        if let Some(r) = (1..nrows).find(|&r| g.mats[ts].values[r * w + round0] == F::ONE) {
            for c in ["c256", "c384", "c520", "c537"] {
                cases.push((format!("SHA256[round row {r}].{c}+1"), cell(ts, r, col(ts, c), plus1())));
            }
        }
    }
    // the register wire (channel space 6)
    if let Ok(tr) = std::panic::catch_unwind(|| tb("REG")) {
        let (w, act) = (g.mats[tr].width, col(tr, "act"));
        let nrows = g.rows_per_table[tr].1;
        let active: Vec<usize> = (0..nrows)
            .filter(|&r| g.mats[tr].values[r * w + act] == F::ONE)
            .collect();
        let (kind, rd) = (col(tr, "kind"), col(tr, "rd"));
        let is_byte = |r: usize| g.mats[tr].values[r * w + kind] == F::ZERO;
        if let Some(&r) = active.iter().find(|&&r| is_byte(r)) {
            // wrong byte: the BYTE lookup and the space-6 message both move
            cases.push((format!("REG[row {r}].byte+1"), cell(tr, r, col(tr, "byte"), plus1())));
            // wrong byte position: `pos + gap + 1 != len`
            cases.push((format!("REG[row {r}].pos+1"), cell(tr, r, col(tr, "pos"), plus1())));
            // a byte moved to another register (the register id is in the message key)
            cases.push((format!("REG[row {r}].rid+1"), cell(tr, r, col(tr, "rid"), plus1())));
            // wrong byte value on the HOSTB half (the wire message moves, not the space-6 one)
            cases.push((format!("REG[row {r}].bv+1"), cell(tr, r, col(tr, "byte"), plus1())));
            // `rd` flipped: the fill becomes a read (and `cDirRd` fires)
            cases.push((format!("REG[row {r}].rd=1-rd"),
                cell(tr, r, rd, Box::new(|_| F::ONE))));
            // `kind` flipped: a byte row becomes a length row (`cDirRd`/`cKind`)
            cases.push((format!("REG[row {r}].kind=1"),
                cell(tr, r, kind, Box::new(|_| F::ONE))));
            // `fresh` flipped on a *fill* row: `cFreshFill` fires
            let fillr = active.iter().find(|&&q| is_byte(q) && g.mats[tr].values[q * w + rd] == F::ZERO);
            if let Some(&f) = fillr {
                cases.push((format!("REG[row {f}].fresh=1"),
                    cell(tr, f, col(tr, "fresh"), Box::new(|_| F::ONE))));
            }
        }
        // a length row's value
        if let Some(&r) = active.iter().find(|&&r| !is_byte(r)) {
            cases.push((format!("REG[row {r}].len+1"), cell(tr, r, col(tr, "len"), plus1())));
        }
        // duplicate slot: two active byte rows of one register at the same position
        let (rid, pos) = (col(tr, "rid"), col(tr, "pos"));
        if active.len() >= 2 {
            let (a, b) = (active[0], active[1]);
            if is_byte(a) && is_byte(b) {
                cases.push((format!("REG dup (rid,pos) rows {a},{b}"), Box::new(move |g: &mut Gen| {
                    let w = g.mats[tr].width;
                    g.mats[tr].values[b * w + pos] = g.mats[tr].values[a * w + pos];
                    g.mats[tr].values[b * w + rid] = g.mats[tr].values[a * w + rid];
                })));
            }
        }
        // ---- the group walk (`cF`..`cOnlyLenEnds`) ----
        let (fcol, len, ts) = (col(tr, "f"), col(tr, "len"), col(tr, "ts"));
        // a mid-group byte row is marked a group start: it is then followed by a byte row, so
        // `cLastByte`/`cPosStep` fire (a group cannot restart in the middle of its bytes)
        if let Some(&r) = active.iter().find(|&&r| is_byte(r) && g.mats[tr].values[r * w + pos] != F::ZERO) {
            cases.push((format!("REG[row {r}].f=1 mid-group"), cell(tr, r, fcol, Box::new(|_| F::ONE))));
        }
        // the group's first byte moved off pos = 0: `cStartPos` fires
        if let Some(r) = (0..nrows).find(|&r| g.mats[tr].values[r * w + fcol] == F::ONE && is_byte(r)) {
            cases.push((format!("REG[row {r}].pos+1 on group start"), cell(tr, r, pos, plus1())));
        }
        // a length row's `f` set: `cLenEnds` fires (a length row ends its group)
        if let Some(&r) = active.iter().find(|&&r| !is_byte(r) && g.mats[tr].values[r * w + fcol] == F::ZERO) {
            cases.push((format!("REG[row {r}].f=1 on length row"), cell(tr, r, fcol, Box::new(|_| F::ONE))));
        }
        // a byte row's position skipped: `pos` +2 inside a group breaks `cPosStep`
        if let Some(&r) = active.iter().find(|&&r| is_byte(r) && g.mats[tr].values[r * w + fcol] == F::ZERO) {
            cases.push((format!("REG[row {r}].pos+2 mid-group"), cell(tr, r, pos, Box::new(|v| v + F::TWO))));
        }
        // `len` changed on a mid-group byte row: `cLenG` fires (the group's length is constant)
        if let Some(&r) = active.iter().find(|&&r| is_byte(r) && g.mats[tr].values[r * w + fcol] == F::ZERO) {
            cases.push((format!("REG[row {r}].len+1 mid-group"), cell(tr, r, len, plus1())));
        }
        // `rid` changed on a mid-group byte row: `cRidG` fires
        if let Some(&r) = active.iter().find(|&&r| is_byte(r) && g.mats[tr].values[r * w + fcol] == F::ZERO) {
            cases.push((format!("REG[row {r}].rid+1 mid-group"), cell(tr, r, rid, plus1())));
        }
        // `ts` changed on a mid-group byte row: `cTsG` fires
        if let Some(&r) = active.iter().find(|&&r| is_byte(r) && g.mats[tr].values[r * w + fcol] == F::ZERO) {
            cases.push((format!("REG[row {r}].ts+1 mid-group"), cell(tr, r, ts, plus1())));
        }
    }
    // swap two ADD rows' timestamps (reorders execution)
    let ta = tb("ADD");
    if g.rows_per_table[ta].1 >= 2 {
        let c = col(ta, "ts");
        cases.push(("ADD swap ts rows 0,1".into(), Box::new(move |g: &mut Gen| {
            let w = g.mats[ta].width;
            g.mats[ta].values.swap(c, w + c);
        })));
    }
    // the SHA-256 cases first: they are the newest and a long run can exhaust memory on the
    // pre-existing suite before reaching the end of the list
    cases.sort_by_key(|(n, _)| if n.starts_with("SHA256") { 0 } else { 1 });
    let mut rejected = 0;
    let total = cases.len();
    for (name, m) in cases {
        let mut gt = Gen { mats: g.mats.clone(), pubs: g.pubs.clone(), rows_per_table: g.rows_per_table.clone(), result: g.result, steps: g.steps, s_units: g.s_units };
        m(&mut gt);
        let pre = match (tracegen::check_constraints(&spec, &gt), tracegen::check_buses(&spec, &gt)) {
            (Err(e), _) => format!("constraint: {e}"),
            (_, Err(e)) => format!("bus: {}", &e[..e.len().min(80)]),
            _ => "PRECHECK PASSES".into(),
        };
        let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match eng.prove(&d_pk, ctx(&eng, &spec, &gt)) {
                Ok(p) => eng.verify(&vk, &p).is_err() || !check_code_root(&eng, &spec, &p, &prep),
                Err(_) => true,
            }
        }));
        let ok = matches!(verdict, Ok(true) | Err(_));
        if ok {
            rejected += 1;
        }
        println!("TAMPER {name:<28} {} ({pre})", if ok { "REJECTED" } else { "ACCEPTED!" });
    }
    println!("TAMPER summary {rejected}/{total} rejected");
    assert_eq!(rejected, total);
}

fn dag_eval(vk: &MultiStarkVerifyingKey<Sha384Config>, ai: usize, cached: usize, cur: &[F], nxt: &[F], pubs: &[F], sel: [F; 3]) -> (Vec<F>, Vec<(u16, F, Vec<F>)>) {
    let dag = &vk.inner.per_air[ai].symbolic_constraints;
    let mut val: Vec<F> = Vec::with_capacity(dag.constraints.nodes.len());
    for n in &dag.constraints.nodes {
        let v = match n {
            SymbolicExpressionNode::Variable(var) => match var.entry {
                // partitioned main: part 0 = the cached columns, part 1 = the common main after them
                Entry::Main { offset: 0, part_index } => cur[if cached > 0 && part_index > 0 { cached + var.index } else { var.index }],
                Entry::Main { offset: 1, part_index } => nxt[if cached > 0 && part_index > 0 { cached + var.index } else { var.index }],
                Entry::Public => pubs[var.index],
                e => panic!("unexpected entry {e:?}"),
            },
            SymbolicExpressionNode::IsFirstRow => sel[0],
            SymbolicExpressionNode::IsLastRow => sel[1],
            SymbolicExpressionNode::IsTransition => sel[2],
            SymbolicExpressionNode::Constant(c) => *c,
            SymbolicExpressionNode::Add { left_idx, right_idx, .. } => val[*left_idx] + val[*right_idx],
            SymbolicExpressionNode::Sub { left_idx, right_idx, .. } => val[*left_idx] - val[*right_idx],
            SymbolicExpressionNode::Neg { idx, .. } => -val[*idx],
            SymbolicExpressionNode::Mul { left_idx, right_idx, .. } => val[*left_idx] * val[*right_idx],
        };
        val.push(v);
    }
    let cons = dag.constraints.constraint_idx.iter().map(|&i| val[i]).collect();
    let ints = dag.interactions.iter().map(|it| (it.bus_index, val[it.count], it.message.iter().map(|&i| val[i]).collect())).collect();
    (cons, ints)
}

/// **The SHA-256 differential test.**  For each vector, build the table's rows from `src/sha.rs`
/// (the generator `check`/`prove` use), then read the digest back out of the *committed cells*
/// through the AIR's own byte layout (`sha::digest_of_row`) and the message back through the `W`
/// columns and data flags (`sha::message_of_rows`).  Both are compared against `sha2`'s
/// `Sha256`, i.e. against FIPS 180-4, on: the empty input, one block, the padding boundaries and a
/// multi-block input.  When a `prep` file is given, the spec's own observed digest (`hid = 53`'s
/// register fill) is compared too, so the chain is AIR cells = `sha2` = the spec's `sha256`.
///
/// This is the differential test the results README reports; it needs no proof, only the trace.
fn cmd_sha_difftest(prep_path: Option<&str>) {
    use sha2::{Digest, Sha256};
    let mut lens: Vec<usize> = vec![0, 1, 3, 55, 56, 63, 64, 65, 100, 119, 120, 127, 128, 129, 200, 1000];
    if let Some(p) = prep_path {
        // the vectors the prep actually hashed
        let ev = sha::spec_vectors(p);
        lens = ev.iter().map(|v| v.len()).collect();
    }
    let mut bad = 0;
    println!("SHA256 DIFFTEST {} vectors", lens.len());
    for (i, &n) in lens.iter().enumerate() {
        // the vector: `byte j = (37 j + 11 i + 5) mod 256` is not used; use a deterministic ramp so
        // the boundary lengths are exercised with non-trivial bytes
        let bytes: Vec<u8> = if let Some(p) = prep_path {
            sha::spec_vectors(p)[i].clone()
        } else {
            (0..n).map(|j| ((37 * j + 11 * i + 5) % 256) as u8).collect()
        };
        let rows = sha::rows(&[sha::Msg { id: 1, bytes: bytes.clone(), dmult: true }],
                             1, 0, 53, 0, bytes.len() as u64);
        let cells = &rows.rows;
        let msg = sha::message_of_rows(cells);
        let dg = sha::digest_of_row(sha::last_digest_row(cells).expect("digest row"));
        let want: [u8; 32] = Sha256::digest(&bytes).into();
        let ok = msg == bytes && dg == want;
        if !ok {
            bad += 1;
            println!(
                "  len {n:5}: msg {} digest {}",
                if msg == bytes { "ok" } else { "MISMATCH" },
                if dg == want { "ok" } else { "MISMATCH" }
            );
        }
        if let Some(p) = prep_path {
            let spec = sha::spec_vectors(p)[i].clone();
            let _ = spec;
        }
    }
    println!("SHA256 DIFFTEST {}/{} vectors: AIR cells == sha2 (message bytes and digest)",
        lens.len() - bad, lens.len());
    assert_eq!(bad, 0, "SHA-256 differential test failed");
    if let Some(p) = prep_path {
        let evs = sha::spec_events(p);
        let mut ok = 0;
        for (i, dg) in evs.iter().enumerate() {
            let bytes = sha::spec_vectors(p)[i].clone();
            let rows = sha::rows(&[sha::Msg { id: 1, bytes: bytes.clone(), dmult: true }],
                                 1, 0, 53, 0, bytes.len() as u64);
            let mine = sha::digest_of_row(sha::last_digest_row(&rows.rows).unwrap());
            if mine == *dg {
                ok += 1;
            }
        }
        println!("SHA256 DIFFTEST spec: {ok}/{} observed `sha256` fills == the AIR's digest rows",
            evs.len());
        assert_eq!(ok, evs.len(), "spec vs AIR digest mismatch");
    }
    println!("SHA256 DIFFTEST OK");
}

fn cmd_difftest(air_path: &str, points_out: &str, rust_out: &str, n: usize) {
    set_levers();
    let spec = load(air_path);
    let eng = Sha384RefEngine::new(seg_v1_params(14, 32, 8));
    let (_pk, vk) = eng.keygen(&airs(&spec));
    let mut rng: u64 = 0x2026_1018_dead_beef;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        F::from_u32((rng % 2013265921) as u32)
    };
    let mut pts = String::new();
    let mut out = String::new();
    for (ti, t) in spec.tables.iter().enumerate() {
        let w = t.cols.len();
        for _ in 0..n {
            let sel = [next(), next(), next()];
            let cur: Vec<F> = (0..w).map(|_| next()).collect();
            let nxt: Vec<F> = (0..w).map(|_| next()).collect();
            let np = if JsonAir::reads_pub(t) { spec.num_pub } else { 0 };
            let pubs: Vec<F> = (0..np).map(|_| next()).collect();
            let j = |v: &[F]| v.iter().map(|x| x.as_canonical_u32().to_string()).collect::<Vec<_>>().join(" ");
            pts.push_str(&format!("{} {} | {} | {} | {}\n", ti, j(&sel), j(&cur), j(&nxt), j(&pubs)));
            let (cons, ints) = dag_eval(&vk, ti, spec.tables[ti].cached, &cur, &nxt, &pubs, sel);
            let cj: Vec<String> = cons.iter().map(|x| x.as_canonical_u32().to_string()).collect();
            let ij: Vec<String> = ints
                .iter()
                .map(|(b, c, m)| format!("[{},{},[{}]]", b, c.as_canonical_u32(), m.iter().map(|x| x.as_canonical_u32().to_string()).collect::<Vec<_>>().join(",")))
                .collect();
            out.push_str(&format!("{{\"t\":{ti},\"constraints\":[{}],\"inters\":[{}]}}\n", cj.join(","), ij.join(",")));
        }
    }
    std::fs::write(points_out, pts).unwrap();
    std::fs::write(rust_out, out).unwrap();
    println!("DIFFTEST points written: {} tables x {n}", spec.tables.len());
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("check") => cmd_check(&a[2], &a[3]),
        Some("prove") => cmd_prove(&a[2], &a[3], a.get(4).map(|s| s.as_str()).unwrap_or("small")),
        Some("tamper") => cmd_tamper(&a[2], &a[3]),
        Some("difftest") => cmd_difftest(&a[2], &a[3], &a[4], a.get(5).map(|s| s.parse().unwrap()).unwrap_or(16)),
        Some("hostb-dump") => cmd_hostb_dump(&a[2], &a[3]),
        Some("sha-difftest") => cmd_sha_difftest(a.get(2).map(|s| s.as_str())),
        _ => eprintln!("usage: see source header"),
    }
    let _: Option<RowMajorMatrix<F>> = None;
}
