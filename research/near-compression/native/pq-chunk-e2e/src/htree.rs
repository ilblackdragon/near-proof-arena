//! [E2E-D M8] The heterogeneous tree (circuit side `openvm-recursion-circuit::nv::htree`): a
//! chunk proved as a sequence of segments of different templates, each wrapped by the generic
//! template leaf, aggregated by the D-7 / D-9 node shapes and wrapped once.
//!
//! * `m8-prove-a AIRSEG DUMP OUT [nsXXlbY]`: one lane A Wasm segment (`wasmBaseSegAirMP`, lane A's
//!   Lean-exported AIR interpreted by lane A's own `air.rs`, the SHA-512 chip v4 of `s384/`, the
//!   trace from lane A's `segdump`) proved under the verifier's backend and configuration (the
//!   stack's base configuration at the given geometry, default `ns18lb7`). Writes `TMPL.vk.json`,
//!   `TMPL.proof`, `INFO.json` (AIR names, public values, cached commitments as 18 limbs).
//! * `m8-prove-b M5A_JSON DUMP_DIR OUT [nsXXlbY]`: one lane B state proof (M5b AIR, `m5a-tool airb`,
//!   interpreted by the pq-state-port interpreter; SHA-256 table from the classical generator; the
//!   public TAPE / HTAPE as cached harness tables, as lane B's prover builds them). Same outputs.
//! * `m8-tree SPEC OUT`: the tree over the leaves listed in `SPEC` (`m8_spec.py`): every leaf is
//!   `htree::build_tmpl_leaf` of its template (or PAD); the pass-through values are derived by
//!   propagating the boundary record leaf by leaf, and the chain is checked natively before any
//!   proof; leaves at one pinned leaf geometry, `P_2` over the template set `{C_t} ∪ {C_padL}`,
//!   `P_*` / `PAD_N` above, the wrap (FINAL domain, zk-masked) exposing `D_wrap(H(S), 0)`.
//!   Writes `SETUP.json`, `WRAP.bundle` (`NPQHT01 | u32 n | S (n bytes, plan §3.4.1) | wrap proof`),
//!   `RESULT.json`.
//! * `m8-verify SETUP PIN BUNDLE`: V_d (pinned vk, program, heights, level;
//!   `ctx = claimDigest = bdigest(S)`, the 42-byte SHA-384 of the canonical statement bytes).
use super::*;
use openvm_recursion_circuit::{
    nv::{
        agg::RangeStmt,
        builder::Builder,
        circuit::{commit_program_part, program_commitment, prove_mats},
        htree::{self as h, CtxMode, LeafWitness, Src, TemplateSpec},
        tree::{self as t, build_node2, build_node_star_set, build_pad, build_pad_node, build_wrap_set},
    },
    sha384::config::{Digest, F},
};
use openvm_stark_backend::{
    AirRef, StarkProtocolConfig,
    prover::{AirProvingContext, CommittedTraceData, DeviceDataTransporter, ProvingContext},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;

#[path = "../../wasm-base/src/air.rs"]
#[allow(dead_code)]
mod wasm_air;
#[path = "../../pq-state-port/src/air.rs"]
#[allow(dead_code)]
mod state_air;

const MAGIC: &[u8; 8] = b"NPQHT01\0";
const SETUP_VERSION: u32 = 1;
const WRAP_LOG_ROWS: usize = 20;

fn root_of(p: &Proof<SC>) -> Digest {
    p.trace_vdata[0].as_ref().unwrap().cached_commitments[0]
}
fn secs(t0: std::time::Instant) -> f64 {
    t0.elapsed().as_secs_f64()
}
fn limbs(d: Digest) -> Vec<u32> {
    openvm_recursion_circuit::nv::fmt::digest_limbs(d).iter().map(|x| x.as_canonical_u32()).collect()
}

// ---------------------------------------------------------------------------------------------
// template provers
// ---------------------------------------------------------------------------------------------

/// A template proof's description for the spec builder (`m8_spec.py`).
#[derive(Serialize, Deserialize)]
struct Info {
    template: String,
    airs: Vec<String>,
    /// per AIR: its public values
    public_values: Vec<Vec<u32>>,
    /// per cached commitment (preamble order): (AIR index, AIR name, 18 limbs)
    cached: Vec<(usize, String, Vec<u32>)>,
    /// per AIR: (log height, tight height)
    heights: Vec<vd::PinnedHeight>,
    vk_sha256: String,
    proof_bytes: usize,
    prove_seconds: f64,
    params: (usize, usize, usize),
    queries: Vec<usize>,
    soundness_bits: f64,
}

fn finish_template(out: &Path, template: &str, names: Vec<String>, vk: &MultiStarkVerifyingKey<SC>, p: &Proof<SC>, secs: f64) {
    let engine = Sha384CpuEngine::new(vk.inner.params.clone());
    engine.verify(vk, p).expect("template proof verifies natively");
    save_vk(&out.join("TMPL.vk.json"), vk);
    let bytes = save_proof(&out.join("TMPL.proof"), p);
    // round trip through the saved forms
    let (v2, p2) = (read_vk(&out.join("TMPL.vk.json")), read_proof(&out.join("TMPL.proof")));
    engine.verify(&v2, &p2).expect("saved template proof verifies");
    let mut cached = vec![];
    for (a, td) in p.trace_vdata.iter().enumerate() {
        for &c in &td.as_ref().unwrap().cached_commitments {
            cached.push((a, names[a].clone(), limbs(c)));
        }
    }
    let prm = &vk.inner.params;
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(vk);
    let info = Info {
        template: template.into(),
        airs: names,
        public_values: p.public_values.iter().map(|v| v.iter().map(|x| x.as_canonical_u32()).collect()).collect(),
        cached,
        heights: vd::proof_heights(p).unwrap(),
        vk_sha256: {
            let envelope = SavedVk { domain_odd_factor: vk.inner.params.whir.domain_odd_factor, vk: vk.clone() };
            hash(&serde_json::to_vec(&envelope).unwrap())
        },
        proof_bytes: bytes,
        prove_seconds: secs,
        params: (prm.n_stack, prm.w_stack, prm.log_blowup),
        queries: prm.whir.rounds.iter().map(|r| r.num_queries).collect(),
        soundness_bits: b.total_bits,
    };
    std::fs::write(out.join("INFO.json"), serde_json::to_vec_pretty(&info).unwrap()).unwrap();
    println!(
        "M8_TEMPLATE_PROVED {template} bytes={bytes} seconds={secs:.1} params=(n_stack {}, w_stack {}, lb {}) queries={:?} bits={:.1}",
        prm.n_stack, prm.w_stack, prm.log_blowup, info.queries, b.total_bits
    );
}

/// The stack's base configuration at `geom`, with `w_stack` / degree from the template's cells.
fn template_params(geom: (usize, usize), total_cells: usize, degree: usize, certs: &str, exclusions: &str) -> SystemParams {
    let (n_stack, lb) = geom;
    let w_stack = (total_cells.div_ceil(1 << (n_stack + 2)) + 4).max(8);
    profile::shaped_params_lb(false, n_stack, w_stack, degree, lb, certs, exclusions)
}

fn ctx_of(engine: &Sha384CpuEngine, m: &RowMajorMatrix<F>, cached_cols: usize, pv: Vec<F>) -> AirProvingContext<openvm_cpu_backend::CpuBackend<SC>> {
    use p3_matrix::Matrix;
    if cached_cols == 0 {
        return AirProvingContext::simple(m.clone(), pv);
    }
    let (w, hgt) = (m.width, m.height());
    let mut a = Vec::with_capacity(hgt * cached_cols);
    let mut b = Vec::with_capacity(hgt * (w - cached_cols).max(1));
    for row in m.values.chunks(w) {
        a.extend_from_slice(&row[..cached_cols]);
        if cached_cols < w {
            b.extend_from_slice(&row[cached_cols..]);
        } else {
            b.push(F::ZERO);
        }
    }
    let cm = RowMajorMatrix::new(a, cached_cols);
    let (commitment, data) = commit_program_part(engine.config(), openvm_stark_backend::prover::ColMajorMatrix::from_row_major(&cm));
    AirProvingContext {
        cached_mains: vec![CommittedTraceData { commitment, trace: cm, data: Arc::new(data) }],
        common_main: RowMajorMatrix::new(b, (w - cached_cols).max(1)),
        public_values: pv,
    }
}

/// Lane A: one `segdump` file (M4c "NPTD" format) proved under the verifier's backend.
/// A template proof a lane saved itself (vk in the `SavedVk` envelope, the stack's proof codec):
/// verified natively here, copied to `OUT/TMPL.{vk.json,proof}` and described in `INFO.json`.
/// `NAMES` is a comma-separated AIR name list or `-` (then `air<i>`).
pub fn import_template(vk_path: &str, proof_path: &str, out: &Path, template: &str, names: &str) {
    std::fs::create_dir_all(out).unwrap();
    let vk = read_vk(Path::new(vk_path));
    let p = read_proof(Path::new(proof_path));
    let n = vk.inner.per_air.len();
    let names: Vec<String> = if names == "-" { (0..n).map(|i| format!("air{i}")).collect() } else { names.split(',').map(String::from).collect() };
    assert_eq!(names.len(), n, "AIR names");
    finish_template(out, template, names, &vk, &p, 0.0);
}

pub fn prove_lane_a(air_seg: &str, dump: &str, out: &Path, geom: (usize, usize), certs: &str, exclusions: &str) {
    use crate::s384;
    use wasm_air::{AirSpec, JsonAir};
    std::fs::create_dir_all(out).unwrap();
    let spec = AirSpec::parse(&std::fs::read_to_string(air_seg).unwrap());
    let b = std::fs::read(dump).unwrap();
    let u = |i: usize| u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap());
    assert_eq!((u(0), u(1)), (0x4454504E, 1), "NPTD v1 dump");
    let npub = u(2) as usize;
    let pubs: Vec<F> = (0..npub).map(|i| F::from_u32(u(3 + i))).collect();
    let mut o = 3 + npub;
    let nt = u(o) as usize;
    o += 1;
    assert_eq!(nt, spec.tables.len(), "dump tables vs AIR");
    let mut mats = vec![];
    for _ in 0..nt {
        let (hgt, w) = (u(o) as usize, u(o + 1) as usize);
        o += 2;
        mats.push(RowMajorMatrix::new((0..hgt * w).map(|k| F::from_u32(u(o + k))).collect(), w));
        o += hgt * w;
    }
    let nc = u(o) as usize;
    o += 1;
    let mut comps = vec![];
    for k in 0..nc {
        assert_eq!(u(o) as usize, 128 * k, "chip compression id");
        o += 1;
        let w: Vec<u64> = (0..24).map(|i| u(o + 2 * i) as u64 | ((u(o + 2 * i + 1) as u64) << 32)).collect();
        o += 48;
        comps.push(s384::reference::Comp { h: w[..8].try_into().unwrap(), block: w[8..].try_into().unwrap() });
    }
    assert_eq!(4 * o, b.len(), "dump length");
    let hc = s384::trace::main_height(comps.len());
    let main = s384::trace::gen_main(&comps, hc);
    let table = s384::trace::gen_table(&main, hc);
    let chip = [
        RowMajorMatrix::new(main.iter().map(|&x| F::from_u32(x as u32)).collect(), s384::air::WIDTH),
        RowMajorMatrix::new(table.iter().map(|&x| F::from_u32(x as u32)).collect(), s384::air::T_WIDTH),
    ];
    let mut airs: Vec<AirRef<SC>> = spec
        .tables
        .iter()
        .map(|t| {
            let np = if JsonAir::reads_pub(t) { spec.num_pub } else { 0 };
            Arc::new(JsonAir { spec: t.clone(), num_pub: np }) as AirRef<SC>
        })
        .collect();
    airs.push(Arc::new(s384::air::Sha512Air4));
    airs.push(Arc::new(s384::air::TableAir4));
    let mut names: Vec<String> = spec.tables.iter().map(|t| t.name.clone()).collect();
    names.extend(["SHA512".into(), "SHA512T".into()]);
    let total: usize = mats.iter().chain(chip.iter()).map(|m| m.values.len()).sum();
    let degree = spec.tables.iter().map(|t| t.degree).max().unwrap().max(s384::air::DEGREE);
    let params = template_params(geom, total, degree, certs, exclusions);
    let engine = Sha384CpuEngine::new(params);
    let t0 = std::time::Instant::now();
    let (pk, vk) = engine.keygen(&airs);
    let mut ctxs = vec![];
    for (i, m) in mats.iter().enumerate() {
        let t = &spec.tables[i];
        let pv = if JsonAir::reads_pub(t) { pubs.clone() } else { vec![] };
        ctxs.push((i, ctx_of(&engine, m, t.cached, pv)));
    }
    for (j, m) in chip.iter().enumerate() {
        ctxs.push((nt + j, AirProvingContext::simple(m.clone(), vec![])));
    }
    println!("M8_LANE_A cells={total} tables={} chip_comps={} degree={degree}", nt + 2, comps.len());
    let proof = engine.prove(&engine.device().transport_pk_to_device(&pk), ProvingContext::new(ctxs)).expect("lane A segment prove");
    finish_template(out, "wasm_seg", names, &vk, &proof, secs(t0));
}

/// Lane B: the M5b state proof of one dump directory (lane B's `tracegen.py` output), proved
/// under the verifier's backend. The instance is built as lane B's prover builds it
/// (`e2e-general/m5a/prover/src/main.rs::load`, adapted here: the pq-state-port interpreter with
/// the per-table `maxLog` cap, the SHA-256 table from the classical generator).
pub fn prove_lane_b(m5a_json: &str, dir: &str, out: &Path, geom: (usize, usize), certs: &str, exclusions: &str) {
    use crate::s384;
    use state_air::{ClassicalAir, JsonAir, TableSpec};
    use std::collections::{BTreeMap, BTreeSet};
    std::fs::create_dir_all(out).unwrap();
    const P: u64 = 0x7800_0001;
    const LEAN_IF: u16 = 16;
    const NAMES_B: &[&str] = &["SHA", "KEY", "BR", "SN", "KCMP", "WSB", "WSN", "WSA", "SNC", "RNG", "WSL", "WSP", "SHAS", "STB", "STW"];
    const NAMES_B8: &[&str] = &["SHA", "KEY", "BR", "SN", "KCMP", "WSB", "WSN", "WSA", "SNC", "RNG", "WSL", "WSP", "STB", "STW"];
    const N_M5A: usize = 12;
    type Key = (u16, Vec<u32>);
    let add = |map: &mut BTreeMap<Key, u64>, k: Key, c: u64| {
        let e = map.entry(k).or_insert(0);
        *e = (*e + c) % P;
    };
    let map_bus = |b: u16| if b == LEAN_IF { s384::air::BUS_IF } else { b };
    let harness = |name: &str, map: &BTreeMap<Key, u64>| -> (TableSpec, RowMajorMatrix<F>) {
        let keys: Vec<(u16, usize)> = map.keys().map(|(b, m)| (*b, m.len())).collect::<BTreeSet<_>>().into_iter().collect();
        let wmsg = keys.iter().map(|k| k.1).max().unwrap_or(1).max(1);
        let width = wmsg + 1 + keys.len().max(1);
        let rows = map.iter().filter(|(_, c)| **c != 0).count();
        let hh = rows.next_power_of_two().max(4);
        let mut v = vec![F::ZERO; hh * width];
        for (r, ((b, m), c)) in map.iter().filter(|(_, c)| **c != 0).enumerate() {
            let row = &mut v[r * width..(r + 1) * width];
            for (j, x) in m.iter().enumerate() {
                row[j] = F::from_u32(*x);
            }
            row[wmsg] = F::from_u32(*c as u32);
            let k = keys.iter().position(|k| *k == (*b, m.len())).unwrap();
            row[wmsg + 1 + k] = F::ONE;
        }
        let spec = TableSpec { name: name.into(), width, max_log: 22, constraints: vec![], inters: vec![], harness: Some((wmsg, keys)), cached: true, num_pub: 0 };
        (spec, RowMajorMatrix::new(v, width))
    };
    let text = std::fs::read_to_string(m5a_json).unwrap();
    let nt = serde_json::from_str::<serde_json::Value>(&text).unwrap()["tables"].as_array().unwrap().len();
    let names: &[&str] = if nt == NAMES_B.len() { NAMES_B } else if nt == NAMES_B8.len() { NAMES_B8 } else { panic!("not an M5b AIR ({nt} tables)") };
    let mut cl = ClassicalAir::parse(&text, names);
    for tb in cl.tables.iter_mut() {
        for i in tb.inters.iter_mut() {
            i.bus = map_bus(i.bus);
        }
    }
    let d = Path::new(dir);
    let pb = std::fs::read(d.join("pubs.bin")).unwrap();
    let pubs: Vec<F> = pb.chunks(4).map(|c| F::from_u32(u32::from_le_bytes(c.try_into().unwrap()))).collect();
    let read_trace = |p: &Path| -> RowMajorMatrix<F> {
        let b = std::fs::read(p).unwrap_or_else(|e| panic!("{p:?}: {e}"));
        let u = |i: usize| u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap());
        let (log, w) = (u(0) as usize, u(1) as usize);
        let n = (1usize << log) * w;
        assert_eq!(b.len(), 8 + 4 * n, "{p:?}: size");
        RowMajorMatrix::new((0..n).map(|i| F::from_u32(u(2 + i))).collect(), w)
    };
    let (mut spec, mut mats): (Vec<TableSpec>, Vec<RowMajorMatrix<F>>) = (vec![], vec![]);
    for tb in cl.tables.iter() {
        let m = if tb.name == "SHA" || tb.name == "SHAS" {
            let f = if tb.name == "SHA" { "sha_msgs.json" } else { "sha_msgs_st.json" };
            let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(d.join(f)).unwrap()).unwrap();
            let msgs: Vec<npudr::sha::Msg> = v
                .as_array()
                .unwrap()
                .iter()
                .map(|x| {
                    let hx = x["bytes"].as_str().unwrap();
                    let bytes = (0..hx.len() / 2).map(|i| u8::from_str_radix(&hx[2 * i..2 * i + 2], 16).unwrap()).collect();
                    npudr::sha::Msg { id: x["id"].as_u64().unwrap() as u32, bytes, dmult: true }
                })
                .collect();
            let (cells, _, _) = npudr::sha::sha_cells(&msgs);
            RowMajorMatrix::new(cells.iter().map(|&x| F::from_u32(x as u32)).collect(), npudr::sha::WIDTH)
        } else {
            read_trace(&d.join(format!("{}.bin", tb.name)))
        };
        assert_eq!(m.width, tb.width, "{}: width", tb.name);
        spec.push(tb.clone());
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
    let hc = s384::trace::main_height(comps.len());
    let main = s384::trace::gen_main(&comps, hc);
    let table = s384::trace::gen_table(&main, hc);
    let chip = [
        RowMajorMatrix::new(main.iter().map(|&x| F::from_u32(x as u32)).collect(), s384::air::WIDTH),
        RowMajorMatrix::new(table.iter().map(|&x| F::from_u32(x as u32)).collect(), s384::air::T_WIDTH),
    ];
    let tape_of = |f: &str| -> Option<BTreeMap<Key, u64>> {
        let txt = std::fs::read_to_string(d.join(f)).ok()?;
        let pm: serde_json::Value = serde_json::from_str(&txt).unwrap();
        let mut tape = BTreeMap::new();
        for x in pm.as_array().unwrap() {
            let bus = map_bus(x[0].as_u64().unwrap() as u16);
            let send = x[1].as_bool().unwrap();
            let msg: Vec<u32> = x[2].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as u32).collect();
            add(&mut tape, (bus, msg), if send { 1 } else { P - 1 });
        }
        Some(tape)
    };
    let (ts, tm) = harness("TAPE", &tape_of("tape.json").expect("tape.json"));
    spec.insert(N_M5A, ts);
    mats.insert(N_M5A, tm);
    if let Some(ht) = tape_of("htape.json") {
        let (hs, hm) = harness("HTAPE", &ht);
        spec.push(hs);
        mats.push(hm);
    }
    let mut airs: Vec<AirRef<SC>> = spec.iter().map(|tb| Arc::new(JsonAir { spec: tb.clone() }) as AirRef<SC>).collect();
    airs.push(Arc::new(s384::air::Sha512Air4));
    airs.push(Arc::new(s384::air::TableAir4));
    let mut tnames: Vec<String> = spec.iter().map(|tb| tb.name.clone()).collect();
    tnames.extend(["SHA512".into(), "SHA512T".into()]);
    let total: usize = mats.iter().chain(chip.iter()).map(|m| m.values.len()).sum();
    fn deg(e: &state_air::E) -> usize {
        use state_air::E;
        match e {
            E::C(_) | E::P(_) => 0,
            E::Col(..) | E::First | E::Last | E::Trans => 1,
            E::Add(a, b) => deg(a).max(deg(b)),
            E::Mul(a, b) => deg(a) + deg(b),
            E::Neg(a) => deg(a),
        }
    }
    let degree = spec.iter().flat_map(|tb| tb.constraints.iter().map(deg)).max().unwrap_or(2).max(s384::air::DEGREE);
    let params = template_params(geom, total, degree, certs, exclusions);
    let engine = Sha384CpuEngine::new(params);
    let t0 = std::time::Instant::now();
    let (pk, vk) = engine.keygen(&airs);
    let mut ctxs = vec![];
    for (i, m) in mats.iter().enumerate() {
        let tb = &spec[i];
        let pv: Vec<F> = (0..tb.num_pub).map(|k| pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        ctxs.push((i, ctx_of(&engine, m, if tb.cached { m.width } else { 0 }, pv)));
    }
    for (j, m) in chip.iter().enumerate() {
        ctxs.push((mats.len() + j, AirProvingContext::simple(m.clone(), vec![])));
    }
    println!("M8_LANE_B cells={total} tables={} chip_comps={} degree={degree} pubs={}", mats.len() + 2, comps.len(), pubs.len());
    let proof = engine.prove(&engine.device().transport_pk_to_device(&pk), ProvingContext::new(ctxs)).expect("lane B state prove");
    finish_template(out, "state", tnames, &vk, &proof, secs(t0));
}

// ---------------------------------------------------------------------------------------------
// the tree
// ---------------------------------------------------------------------------------------------

/// A record-cell source in the spec JSON: `["pv", air, j]`, `["cached", k, l]`, `["stmt", k]`,
/// `["pass", j]`, `["const", c]`.
fn src_of(v: &serde_json::Value) -> Src {
    let a = v.as_array().expect("source");
    let n = |i: usize| a[i].as_u64().unwrap() as usize;
    match a[0].as_str().unwrap() {
        "pv" => Src::Pv(n(1), n(2)),
        "cached" => Src::Cached(n(1), n(2)),
        "stmt" => Src::Stmt(n(1)),
        "pass" => Src::Pass(n(1)),
        "const" => Src::Const(n(1) as u32),
        o => panic!("source kind {o}"),
    }
}

fn template_of_json(v: &serde_json::Value) -> TemplateSpec {
    let srcs = |k: &str| -> Vec<Src> { v[k].as_array().unwrap().iter().map(src_of).collect() };
    let nums = |x: &serde_json::Value| -> Vec<usize> { x.as_array().unwrap().iter().map(|y| y.as_u64().unwrap() as usize).collect() };
    TemplateSpec {
        name: v["name"].as_str().unwrap().into(),
        phase_in: v["phase_in"].as_u64().unwrap() as u32,
        phase_out: v["phase_out"].as_u64().unwrap() as u32,
        rec_in: srcs("rec_in"),
        rec_out: srcs("rec_out"),
        stmt_len: v["stmt_len"].as_u64().unwrap() as usize,
        ctx_mode: match &v["ctx"] {
            serde_json::Value::String(m) if m == "witness" => CtxMode::Witness,
            serde_json::Value::String(m) if m == "hash_stmt" => CtxMode::HashStmt,
            serde_json::Value::Array(a) => CtxMode::Src(a.iter().map(src_of).collect()),
            o => panic!("ctx mode {o}"),
        },
        n_pass: v["n_pass"].as_u64().unwrap() as usize,
        pv_equal: v["pv_equal"].as_array().unwrap().iter().map(nums).collect(),
        pv_const: v["pv_const"].as_array().unwrap().iter().map(|x| { let y = nums(x); (y[0], y[1], y[2] as u32) }).collect(),
        cached_const: vec![],
    }
}

/// The audit content of a heterogeneous-tree setup (V_d reads none of it).
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct HTemplate {
    pub name: String,
    pub phase_in: u32,
    pub phase_out: u32,
    /// sha256 of the template child's vk (saved form); None for a statement-only template
    pub vk_sha256: Option<String>,
    /// the child's pinned heights (log, tight) per AIR
    pub heights: Option<Vec<vd::PinnedHeight>>,
    pub c_leaf: Digest,
}

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct HShape {
    pub arity: usize,
    pub depth: usize,
    pub n_rec: usize,
    pub stmt_len: usize,
    pub templates: Vec<HTemplate>,
    pub leaf: super::tree::Geom,
    pub node: super::tree::Geom,
    pub c_pad_leaf: Digest,
    pub c_node2: Digest,
    pub c_pad_node: Digest,
    pub c_node_star: Option<Digest>,
    pub leaf_params: (usize, usize),
    pub tree_geom: (usize, usize),
}

#[derive(Serialize, Deserialize)]
pub struct HSetup {
    pub version: u32,
    pub domain_odd_factor: usize,
    pub final_vk: MultiStarkVerifyingKey<SC>,
    pub program: Vec<[u32; 4]>,
    pub level: u32,
    pub final_heights: Vec<vd::PinnedHeight>,
    pub tree: HShape,
}

struct Leaf {
    spec: Option<TemplateSpec>,
    child: Option<(MultiStarkVerifyingKey<SC>, Proof<SC>)>,
    w: LeafWitness,
    stmt: RangeStmt,
    /// PAD: its state
    pad: Option<Vec<F>>,
}

impl Leaf {
    fn body(&self, b: &mut Builder) -> RangeStmt {
        match &self.spec {
            Some(s) => h::build_tmpl_leaf(b, s, self.child.as_ref().map(|(v, p)| (v, p)), &self.w),
            None => build_pad(b, &self.w.ctx, self.w.a, self.pad.as_ref().unwrap()),
        }
    }
}

struct Item {
    vk: MultiStarkVerifyingKey<SC>,
    p: Proof<SC>,
    stmt: RangeStmt,
}

pub fn tree_prove(spec_path: &str, out: &Path, certs: &str, exclusions: &str) {
    std::fs::create_dir_all(out).unwrap();
    let t_all = std::time::Instant::now();
    let sj: serde_json::Value = serde_json::from_slice(&std::fs::read(spec_path).unwrap()).unwrap();
    let arity = sj["arity"].as_u64().unwrap() as usize;
    let depth = sj["depth"].as_u64().unwrap() as usize;
    let n_rec = sj["n_rec"].as_u64().unwrap() as usize;
    // the stub templates' statement cells (private record sources) and the canonical statement
    // bytes S (plan §3.4.1): ctx = claimDigest = bdigest(S), the only public input
    let stmt: Vec<F> = sj["stmt"].as_array().unwrap().iter().map(|x| F::from_u32(x.as_u64().unwrap() as u32)).collect();
    let hx = sj["claim_s_hex"].as_str().expect("claim_s_hex");
    let claim_s: Vec<u8> = (0..hx.len() / 2).map(|i| u8::from_str_radix(&hx[2 * i..2 * i + 2], 16).unwrap()).collect();
    let ctx = h::claim_ctx(&claim_s);
    println!("M8_CLAIM_S bytes={} claimDigest={}", claim_s.len(), h::claim_ctx_bytes(&ctx).iter().map(|b| format!("{b:02x}")).collect::<String>());
    let specs: Vec<TemplateSpec> = sj["templates"].as_array().unwrap().iter().map(template_of_json).collect();
    let tparams = profile::params_geom(false, certs, exclusions, profile::tree_geom());
    let cap_log = tparams.l_skip + tparams.n_stack;
    let parent = Sha384CpuEngine::new(tparams);
    let final_engine = Sha384CpuEngine::new_final(profile::params(true, certs, exclusions));
    let k = parent.config().params().k_whir();
    let leaf_geom = profile::parse_geom(&std::env::var("NEARPROOF_TREE_LEAF_PARAMS").unwrap_or_else(|_| "ns20lb2".into()));
    let lparams = profile::params_geom(false, certs, exclusions, leaf_geom);
    assert_eq!((lparams.l_skip + lparams.n_stack, lparams.k_whir()), (cap_log, k), "leaf geometry: stacked height and fold must equal the tree layer's");
    let leaf_engine = Sha384CpuEngine::new(lparams);
    let margin = super::tree::node_margin(arity);
    println!("M8_TREE arity={arity} depth={depth} n_rec={n_rec} stmt_len={} templates={} node_margin={margin}", stmt.len(), specs.len());
    let mut seconds = serde_json::Map::new();
    // ---- leaves: load template proofs, derive pass-through values by propagating the record
    let mut leaves: Vec<Leaf> = vec![];
    let mut cur: Option<Vec<F>> = None; // the record after the previous leaf
    let mut phase = t::PHASE_INIT;
    for (i, lj) in sj["leaves"].as_array().unwrap().iter().enumerate() {
        let a = F::from_usize(i);
        let name = lj["template"].as_str().unwrap();
        if name == "PAD" {
            assert_eq!(phase, t::PHASE_DONE, "leaf {i}: PAD before DONE");
            let w = LeafWitness { stmt: vec![], ctx: ctx.clone(), pass: vec![], a };
            let s = h::done_state();
            let stmt_l = RangeStmt { ctx: ctx.clone(), a, e: a + F::ONE, s_a: s.clone(), s_e: s.clone() };
            leaves.push(Leaf { spec: None, child: None, w, stmt: stmt_l, pad: Some(s) });
            continue;
        }
        let spec = specs.iter().find(|s| s.name == name).unwrap_or_else(|| panic!("template {name}")).clone();
        let child = lj["dir"].as_str().map(|d| {
            let d = Path::new(d);
            let (v, p) = (read_vk(&d.join("TMPL.vk.json")), read_proof(&d.join("TMPL.proof")));
            Sha384CpuEngine::new(v.inner.params.clone()).verify(&v, &p).unwrap_or_else(|e| panic!("leaf {i} ({name}): template proof: {e:?}"));
            (v, p)
        });
        let n = spec.check(child.as_ref().map(|c| &c.0), child.as_ref().map(|c| &c.1)).unwrap_or_else(|e| panic!("leaf {i}: {e}"));
        assert!(n == n_rec || n == 0, "leaf {i}: record length {n} != {n_rec}");
        assert_eq!(spec.phase_in, phase, "leaf {i} ({name}): phase");
        // pass values from the current record
        let mut pass = vec![F::ZERO; spec.n_pass];
        for (p, s) in spec.rec_in.iter().enumerate() {
            if let Src::Pass(j) = *s {
                pass[j] = cur.as_ref().expect("a pass-through needs a previous record")[p];
            }
        }
        let w = LeafWitness { stmt: if spec.stmt_len > 0 { stmt.clone() } else { vec![] }, ctx: if spec.ctx_mode == CtxMode::Witness { ctx.clone() } else { vec![] }, pass, a };
        assert!(spec.stmt_len == 0 || spec.stmt_len == stmt.len(), "leaf {i}: statement length");
        let (pvs, cached) = match &child {
            Some((_, p)) => (p.public_values.clone(), h::proof_cached(p)),
            None => (vec![], vec![]),
        };
        let rin = h::record_values(&spec.rec_in, &pvs, &cached, &w);
        if let Some(c) = &cur {
            if let Some(p) = (0..n_rec).find(|&p| rin[p] != c[p]) {
                panic!("leaf {i} ({name}): B_in cell {p} = {} differs from the previous B_out's {} (the chain does not hold natively)", rin[p], c[p]);
            }
        }
        let rout = h::record_values(&spec.rec_out, &pvs, &cached, &w);
        let st = h::leaf_statement(&spec, child.as_ref().map(|c| &c.1), &w);
        assert_eq!(st.ctx, ctx, "leaf {i} ({name}): its ctx is not the chunk's claimDigest");
        println!("M8_LEAF {i} template={name} phase {}->{} child={}", spec.phase_in, spec.phase_out, child.is_some());
        phase = spec.phase_out;
        cur = if rout.is_empty() { None } else { Some(rout) };
        leaves.push(Leaf { spec: Some(spec), child, w, stmt: st, pad: None });
    }
    assert_eq!(phase, t::PHASE_DONE, "the last leaf must reach DONE");
    while leaves.len() % arity != 0 || leaves.len() < arity.pow(depth as u32) / arity.pow(depth as u32 - 1) {
        let a = F::from_usize(leaves.len());
        let s = h::done_state();
        leaves.push(Leaf { spec: None, child: None, w: LeafWitness { stmt: vec![], ctx: ctx.clone(), pass: vec![], a }, stmt: RangeStmt { ctx: ctx.clone(), a, e: a + F::ONE, s_a: s.clone(), s_e: s.clone() }, pad: Some(s) });
    }
    let all: Vec<RangeStmt> = leaves.iter().map(|l| l.stmt.clone()).collect();
    let chunk_stmt = RangeStmt::compose(&all).expect("leaf statements chain natively");
    assert_eq!((chunk_stmt.s_a[0], chunk_stmt.s_e[0]), (F::from_u32(t::PHASE_INIT), F::from_u32(t::PHASE_DONE)));
    println!("M8_CHAIN_OK leaves={} (natively: ctx, indices, boundary digests)", leaves.len());
    // ---- leaf geometry: the max over every leaf program's shape pin (one family)
    let lg2 = |x: usize| x.max(1).next_power_of_two().trailing_zeros() as usize;
    let probe = super::tree::circ(k, cap_log - 1, cap_log - 2, 1, cap_log, None);
    let mut pins = vec![];
    let mut c_leaf: Vec<(String, Digest)> = vec![];
    let mut rows_max = 0usize;
    for (i, l) in leaves.iter().enumerate() {
        let t0 = std::time::Instant::now();
        let (mats, b) = probe.generate_with(|b| {
            l.body(b);
        });
        assert!(b.failures.is_empty(), "leaf {i}: {:?}", b.failures);
        let (pin, _) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
        rows_max = rows_max.max(b.instrs.len());
        println!("M8_LEAF_PROBE {i} rows={} pin={pin:?} s={:.1}", b.instrs.len(), secs(t0));
        pins.push(pin);
    }
    let pl = lg2(rows_max);
    let mut h_l = super::tree::max_pin(&pins);
    let lr = lg2(h_l[0].1.unwrap()).max(pl + 1);
    // the NvAir height is the circuit's 2^log_rows (the probe ran at the largest geometry)
    h_l[0].0 = lr;
    let leaf_g = super::tree::Geom { log_rows: lr, prog_log: pl, sha_instances: 1, heights: h_l.clone() };
    println!("M8_LEAF_GEOM {leaf_g:?}");
    // M8_CHECK_ONLY=1: stop after the native chain check and the leaf program probes (no proof)
    if std::env::var("M8_CHECK_ONLY").is_ok_and(|v| v == "1") {
        println!("M8_CHECK_ONLY_DONE");
        return;
    }
    let lc = super::tree::circ(k, lr, pl, 1, cap_log, Some(&h_l));
    // M8_PROGRAMS_ONLY=1 (lane A A-T2): print every template leaf's program root at the leaf
    // geometry and stop (no proof): leaves of one template with equal child heights share a program
    if std::env::var("M8_PROGRAMS_ONLY").is_ok_and(|v| v == "1") {
        for (i, l) in leaves.iter().enumerate() {
            let (mats, b) = lc.generate_with(|b| {
                l.body(b);
            });
            assert!(b.failures.is_empty(), "leaf {i}: {:?}", b.failures);
            let c = program_commitment(leaf_engine.config(), &mats[0]);
            let name = l.spec.as_ref().map_or("PAD".to_string(), |s| s.name.clone());
            println!("M8_LEAF_PROGRAM {i} template={name} rows={} root={:x}{:x}", b.instrs.len(), c[0], c[1]);
        }
        println!("M8_PROGRAMS_ONLY_DONE");
        return;
    }
    // M8_REUSE=DIR: take a proof from an earlier run of the same spec when it is the same proof
    // (native verification under the vk of this circuit, pinned heights, statement, program root
    // checked by the caller); a measurement aid after a failure late in a run
    let reuse_dir = std::env::var("M8_REUSE").ok().map(std::path::PathBuf::from);
    let reuse = |file: &str, eng: &Sha384CpuEngine, c: &NvCircuit, h: &[vd::PinnedHeight], st: &RangeStmt| -> Option<(MultiStarkVerifyingKey<SC>, Proof<SC>)> {
        let f = reuse_dir.as_ref()?.join(file);
        if !f.exists() {
            return None;
        }
        let p = read_proof(&f);
        let (_, vk) = eng.keygen(&c.airs::<SC>());
        let ok = eng.verify(&vk, &p).is_ok()
            && vd::proof_heights(&p).as_deref() == Some(h)
            && openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], st);
        println!("M8_REUSE {file} {}", if ok { "reused" } else { "NOT reusable" });
        ok.then_some((vk, p))
    };
    // ---- prove the leaves
    let mut items: Vec<Item> = vec![];
    let mut n_proofs = 0usize;
    let mut kinds: std::collections::BTreeMap<String, Vec<f64>> = Default::default();
    for (i, l) in leaves.iter().enumerate() {
        let t0 = std::time::Instant::now();
        if let Some((v, p)) = reuse(&format!("LEAF{i}.proof"), &leaf_engine, &lc, &h_l, &l.stmt) {
            let name = l.spec.as_ref().map_or("PAD".to_string(), |s| s.name.clone());
            let c = root_of(&p);
            if !c_leaf.iter().any(|(_, x)| *x == c) {
                c_leaf.push((name, c));
            }
            save_proof(&out.join(format!("LEAF{i}.proof")), &p);
            n_proofs += 1;
            items.push(Item { vk: v, p, stmt: l.stmt.clone() });
            continue;
        }
        let (mats, b) = lc.generate_with(|b| {
            l.body(b);
        });
        assert!(b.failures.is_empty(), "leaf {i}: {:?}", b.failures);
        let c = program_commitment(leaf_engine.config(), &mats[0]);
        let (v, p, _) = prove_mats(&lc, &leaf_engine, mats, &b);
        assert_eq!(vd::proof_heights(&p).unwrap(), h_l, "leaf {i}: heights");
        assert_eq!(root_of(&p), c);
        assert!(openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], &l.stmt), "leaf {i}: statement");
        let name = l.spec.as_ref().map_or("PAD".to_string(), |s| s.name.clone());
        if !c_leaf.iter().any(|(_, x)| *x == c) {
            c_leaf.push((name.clone(), c));
        }
        let bytes = save_proof(&out.join(format!("LEAF{i}.proof")), &p);
        let sec = secs(t0);
        println!("M8_LEAF_PROVED {i} template={name} rows={} bytes={bytes} seconds={sec:.1}", b.instrs.len());
        seconds.insert(format!("leaf{i}_{name}"), sec.into());
        kinds.entry(if name == "PAD" { "pad_leaf".into() } else { format!("leaf_{name}") }).or_default().push(sec);
        if i == 0 {
            save_vk(&out.join("LEAF.vk.json"), &v);
        }
        n_proofs += 1;
        items.push(Item { vk: v, p, stmt: l.stmt.clone() });
    }
    // the template set: one program per template leaf seen (a template whose children differ in
    // heights has several), then PAD_L last
    let pad_pos = c_leaf.iter().position(|(n, _)| n == "PAD").expect("a PAD_L program");
    let (_, c_pad_leaf) = c_leaf.remove(pad_pos);
    let mut set: Vec<Digest> = c_leaf.iter().map(|x| x.1).collect();
    set.push(c_pad_leaf);
    println!("M8_TEMPLATE_SET {}", c_leaf.iter().map(|(n, c)| format!("{n}:{:x}", c[0])).collect::<Vec<_>>().join(" "));
    let templates: Vec<HTemplate> = specs
        .iter()
        .flat_map(|s| {
            leaves.iter().filter(|l| l.spec.as_ref().is_some_and(|x| x.name == s.name)).map(|l| {
                let (vk_sha256, heights) = match &l.child {
                    Some((v, p)) => (Some(hash(&serde_json::to_vec(&SavedVk { domain_odd_factor: v.inner.params.whir.domain_odd_factor, vk: v.clone() }).unwrap())), Some(vd::proof_heights(p).unwrap())),
                    None => (None, None),
                };
                (s.name.clone(), s.phase_in, s.phase_out, vk_sha256, heights)
            })
        })
        .zip(0..)
        .map(|((name, pi, po, v, hh), _)| (name, pi, po, v, hh))
        .collect::<Vec<_>>()
        .into_iter()
        .fold(vec![], |mut acc: Vec<HTemplate>, (name, pi, po, v, hh)| {
            // one entry per distinct (template, child vk, heights): its leaf program
            if !acc.iter().any(|e| e.name == name && e.vk_sha256 == v && e.heights == hh) {
                acc.push(HTemplate { name, phase_in: pi, phase_out: po, vk_sha256: v, heights: hh, c_leaf: [0; 6] });
            }
            acc
        });
    // attach the program roots (template order of first appearance in the leaves)
    let mut templates = templates;
    for e in templates.iter_mut() {
        let i = leaves
            .iter()
            .position(|l| {
                l.spec.as_ref().is_some_and(|x| x.name == e.name)
                    && l.child.as_ref().map(|(v, _)| hash(&serde_json::to_vec(&SavedVk { domain_odd_factor: v.inner.params.whir.domain_odd_factor, vk: v.clone() }).unwrap())) == e.vk_sha256
                    && l.child.as_ref().map(|(_, p)| vd::proof_heights(p).unwrap()) == e.heights
            })
            .unwrap();
        e.c_leaf = root_of(&items[i].p);
    }
    // ---- node geometry: P_2 over the first `arity` leaves, at the largest geometry, then the
    // smallest holding it with the margin (depth >= 2)
    let m = if depth >= 2 { margin } else { 1.0 };
    let gen_p2 = |c: &NvCircuit, grp: &[Item]| -> (Vec<RowMajorMatrix<F>>, Builder, RangeStmt) {
        let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = grp.iter().map(|x| (&x.vk, &x.p)).collect();
        let pre: Vec<RangeStmt> = grp.iter().map(|x| x.stmt.clone()).collect();
        let mut s = None;
        let (mm, b) = c.generate_with(|b| {
            s = Some(build_node2(b, &refs, &pre, &set));
        });
        (mm, b, s.unwrap())
    };
    let node_g = {
        let maxg = super::tree::circ(k, cap_log, cap_log - 1, openvm_recursion_circuit::nv::circuit::MAX_SHA_INSTANCES, cap_log, None);
        let (mut rows, mut nv_used, mut sha_used) = (0usize, 0usize, 0usize);
        for grp in items.chunks(arity) {
            let (mats, b, _) = gen_p2(&maxg, grp);
            let used = openvm_recursion_circuit::nv::circuit::natural_tight_heights(&mats, 2);
            let su: usize = (0..openvm_recursion_circuit::nv::circuit::MAX_SHA_INSTANCES).map(|j| used[openvm_recursion_circuit::nv::circuit::sha_air_index(j)]).sum();
            rows = rows.max(b.instrs.len());
            nv_used = nv_used.max(used[0]);
            sha_used = sha_used.max(su);
        }
        let lgf = |x: f64| (x.ceil() as usize).next_power_of_two().trailing_zeros() as usize;
        let mut pl = lgf(rows as f64 * m).max(19);
        let mut lr = lgf(nv_used as f64 * m).max(pl + 1);
        let mut ks = ((sha_used as f64 * m) / (1usize << cap_log) as f64).ceil().max(1.0) as usize;
        println!("M8_NODE2_SIZES rows={rows} nv_used={nv_used} sha_used={sha_used} -> ({lr},{pl},{ks})");
        loop {
            let c = super::tree::circ(k, lr, pl, ks, cap_log, None);
            let mut pins = vec![];
            let mut rws = 0usize;
            for grp in items.chunks(arity) {
                let (mats, b, _) = gen_p2(&c, grp);
                let (pin, _) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
                rws = rws.max(b.instrs.len());
                pins.push(pin);
            }
            let pin = super::tree::max_pin(&pins);
            let sha_total: usize = (0..ks).map(|j| pin[openvm_recursion_circuit::nv::circuit::sha_air_index(j)].1.unwrap()).sum();
            if (rws as f64 * m) > (1usize << pl) as f64 {
                pl += 1;
            } else if (pin[0].1.unwrap() as f64 * m) > (1usize << lr) as f64 {
                lr += 1;
            } else if (sha_total as f64 * m) > (ks << cap_log) as f64 {
                ks += 1;
            } else {
                break super::tree::Geom { log_rows: lr, prog_log: pl, sha_instances: ks, heights: super::tree::grow_pin(&pin, m, ks, cap_log) };
            }
            if pl >= lr {
                lr = pl + 1;
            }
            assert!(lr <= cap_log, "no node geometry fits");
        }
    };
    println!("M8_NODE_GEOM {node_g:?}");
    let h_n = node_g.heights.clone();
    let nc = super::tree::circ(k, node_g.log_rows, node_g.prog_log, node_g.sha_instances, cap_log, Some(&h_n));
    let probe_n = super::tree::circ(k, node_g.log_rows, node_g.prog_log, node_g.sha_instances, cap_log, None);
    let done = h::done_state();
    let (mats, _) = probe_n.generate_with(|b| {
        build_pad_node(b, &ctx, F::from_usize(arity), &done, 2);
    });
    let c_pad_node = program_commitment(parent.config(), &mats[0]);
    let (mats, _, _) = gen_p2(&probe_n, &items[..arity]);
    let c_node2 = program_commitment(parent.config(), &mats[0]);
    let mut c_star: Option<Digest> = None;
    for lvl in 2..=depth as u32 + 1 {
        if lvl >= 3 {
            while items.len() % arity != 0 {
                let t0 = std::time::Instant::now();
                let a = items.last().unwrap().stmt.e.as_canonical_u32() as usize;
                let j = items.len();
                let pst = RangeStmt { ctx: ctx.clone(), a: F::from_usize(a), e: F::from_usize(a + 1), s_a: done.clone(), s_e: done.clone() };
                if let Some((v, p)) = reuse(&format!("PADN{}_{j}.proof", lvl - 1), &parent, &nc, &h_n, &pst) {
                    assert_eq!(root_of(&p), c_pad_node);
                    save_proof(&out.join(format!("PADN{}_{j}.proof", lvl - 1)), &p);
                    n_proofs += 1;
                    items.push(Item { vk: v, p, stmt: pst });
                    continue;
                }
                let mut s = None;
                let (mats, b) = nc.generate_with(|b| {
                    s = Some(build_pad_node(b, &ctx, F::from_usize(a), &done, lvl - 1));
                });
                let (v, p, _) = prove_mats(&nc, &parent, mats, &b);
                assert_eq!(root_of(&p), c_pad_node);
                let j = items.len();
                save_proof(&out.join(format!("PADN{}_{j}.proof", lvl - 1)), &p);
                let sec = secs(t0);
                println!("M8_PAD_NODE_PROVED L{}_{j} seconds={sec:.1}", lvl - 1);
                seconds.insert(format!("padn{}_{j}", lvl - 1), sec.into());
                kinds.entry("pad_node".into()).or_default().push(sec);
                n_proofs += 1;
                items.push(Item { vk: v, p, stmt: s.unwrap() });
            }
        }
        let mut next = vec![];
        for (j, grp) in items.chunks(arity).enumerate() {
            let t0 = std::time::Instant::now();
            let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = grp.iter().map(|x| (&x.vk, &x.p)).collect();
            let pre: Vec<RangeStmt> = grp.iter().map(|x| x.stmt.clone()).collect();
            let gen_node = |c: &NvCircuit, s: &mut Option<RangeStmt>| {
                c.generate_with(|b| {
                    *s = Some(if lvl == 2 { build_node2(b, &refs, &pre, &set) } else { build_node_star_set(b, &refs, &pre, &[c_node2], c_pad_node) });
                })
            };
            let cst = RangeStmt::compose(&pre).expect("children chain");
            if let Some((v, p)) = reuse(&format!("NODE{lvl}_{j}.proof"), &parent, &nc, &h_n, &cst) {
                let r = root_of(&p);
                if lvl == 2 {
                    assert_eq!(r, c_node2);
                } else {
                    assert!(c_star.is_none_or(|c| c == r));
                    c_star = Some(r);
                }
                save_proof(&out.join(format!("NODE{lvl}_{j}.proof")), &p);
                n_proofs += 1;
                next.push(Item { vk: v, p, stmt: cst });
                continue;
            }
            let mut s = None;
            let (pm, pb) = gen_node(&probe_n, &mut s);
            let (npin, _) = shape_pinned_heights(&pm, &pb, 2, FINAL_PIN_EPS_BITS);
            drop(pm);
            assert!(super::tree::fits(&npin, &h_n), "node L{lvl}_{j}: shape pin {npin:?} exceeds the node pin {h_n:?}");
            let (mats, b) = gen_node(&nc, &mut s);
            assert!(b.failures.is_empty(), "node L{lvl}_{j}: {:?}", b.failures);
            let rows = b.instrs.len();
            let (v, p, _) = prove_mats(&nc, &parent, mats, &b);
            assert_eq!(p.public_values[0][0], F::from_u32(lvl));
            let r = root_of(&p);
            if lvl == 2 {
                assert_eq!(r, c_node2, "P_2 programs differ across template mixes");
            } else {
                assert!(c_star.is_none_or(|c| c == r));
                c_star = Some(r);
            }
            save_proof(&out.join(format!("NODE{lvl}_{j}.proof"), ), &p);
            let sec = secs(t0);
            println!("M8_NODE_PROVED L{lvl}_{j} kind={} rows={rows} seconds={sec:.1}", if lvl == 2 { "P2" } else { "Pstar" });
            seconds.insert(format!("node{lvl}_{j}"), sec.into());
            kinds.entry(if lvl == 2 { "node2" } else { "node_star" }.into()).or_default().push(sec);
            n_proofs += 1;
            next.push(Item { vk: v, p, stmt: s.unwrap() });
        }
        items = next;
    }
    assert_eq!(items.len(), 1);
    let root = items.pop().unwrap();
    assert_eq!(root.stmt, RangeStmt { e: root.stmt.e, ..chunk_stmt.clone() }, "the root's statement is the chunk's");
    // ---- wrap
    let t0 = std::time::Instant::now();
    let wrap_prog_log = 18;
    let mut wc = NvCircuit::new(k, WRAP_LOG_ROWS, 1);
    wc.prog_log = wrap_prog_log;
    let c_roots = if depth == 1 { vec![c_node2] } else { vec![c_star.unwrap()] };
    let root_level = 1 + depth as u32;
    let wbody = |b: &mut Builder| {
        build_wrap_set(b, &root.vk, &root.p, root_level, &c_roots, &root.stmt);
    };
    let fparams = final_engine.config().params().clone();
    let (mm, bb) = wc.generate_with(wbody);
    let (wh, _) = shape_pinned_heights(&mm, &bb, fparams.l_skip, FINAL_PIN_EPS_BITS);
    drop(mm);
    wc.heights = Some(wh.iter().map(|&(l, _)| 1usize << l).collect());
    wc.tight_floor = Some(wh.iter().map(|&(l, tt)| tt.unwrap_or(1 << l)).collect());
    let (mats, b) = wc.generate_with(wbody);
    assert!(b.failures.is_empty(), "wrap: {:?}", b.failures);
    let wrap_rows = b.instrs.len();
    let (fv, fp, _) = prove_mats(&wc, &final_engine, mats, &b);
    assert_eq!(vd::proof_heights(&fp).as_ref(), Some(&wh));
    let wsec = secs(t0);
    seconds.insert("wrap".into(), wsec.into());
    kinds.entry("wrap".into()).or_default().push(wsec);
    n_proofs += 1;
    let program: Vec<[u32; 4]> = b.instrs.iter().map(|i| i.words()).collect();
    let shape = HShape {
        arity,
        depth,
        n_rec,
        stmt_len: stmt.len(),
        templates,
        leaf: leaf_g,
        node: node_g,
        c_pad_leaf,
        c_node2,
        c_pad_node,
        c_node_star: c_star,
        leaf_params: leaf_geom,
        tree_geom: profile::tree_geom(),
    };
    let setup = HSetup { version: SETUP_VERSION, domain_odd_factor: 15, final_vk: fv, program, level: t::LEVEL_WRAP, final_heights: wh.clone(), tree: shape };
    let setup_bytes = serde_json::to_vec(&setup).unwrap();
    let pin = hash(&setup_bytes);
    std::fs::write(out.join("SETUP.json"), &setup_bytes).unwrap();
    std::fs::write(out.join("SETUP.sha256"), &pin).unwrap();
    let proof_bytes = save_proof(&out.join("WRAP.proof"), &fp);
    let mut packet = MAGIC.to_vec();
    packet.extend_from_slice(&(claim_s.len() as u32).to_le_bytes());
    packet.extend_from_slice(&claim_s);
    fp.encode(&mut packet).unwrap();
    std::fs::write(out.join("WRAP.bundle"), &packet).unwrap();
    // native V_d and controls
    let vds = VdSetup { vk_final: setup.final_vk.clone(), program: setup.program.clone(), level: setup.level, heights: Some(wh.clone()) };
    vd::verify_wrap(&vds, &final_engine, &ctx, 0, &fp).expect("V_d (wrap)");
    let mut s2 = claim_s.clone();
    s2[0] ^= 1;
    assert!(vd::verify_wrap(&vds, &final_engine, &h::claim_ctx(&s2), 0, &fp).is_err(), "another statement accepted");
    let mut bad = vds.clone();
    bad.program[0][0] ^= 1;
    assert!(vd::verify_wrap(&bad, &final_engine, &ctx, 0, &fp).is_err());
    println!("M8_WRAP_NEGATIVE_CONTROLS_OK other_statement changed_program");
    let kind_stats: serde_json::Map<String, serde_json::Value> =
        kinds.iter().map(|(k, v)| (k.clone(), serde_json::json!({"n": v.len(), "mean_s": v.iter().sum::<f64>() / v.len() as f64}))).collect();
    let result = serde_json::json!({
        "scope": "E2E-D M8 prototype: heterogeneous tree (generic template leaf, template set of several kinds, stub INIT / FINAL) over T1-shaped segments (lane A Wasm segments, lane B state proof, re-proved under the verifier's backend at the stack's base configuration) + wrap",
        "security_established": false,
        "zero_knowledge_established": false,
        "zero_knowledge_scope": "not claimed for the prototype: the packet is S (plan 3.4.1) + the zk-masked wrap and nothing else leaves the tree, but the prototype's setup is per run (its template set lists this run's template leaf programs at the segments' natural heights, not pinned template shapes) and the stub INIT / FINAL are not sound templates",
        "arity": arity, "depth": depth, "leaves": leaves.len(), "tree_proofs": n_proofs,
        "templates": setup.tree.templates.iter().map(|e| e.name.clone()).collect::<Vec<_>>(),
        "template_set_size": set.len(),
        "wrap_proof_bytes": proof_bytes, "statement_bytes": claim_s.len(), "stub_statement_cells": stmt.len(), "bundle_bytes": packet.len(),
        "setup_bytes": setup_bytes.len(), "setup_sha256": pin,
        "leaf_geom": setup.tree.leaf, "node_geom": setup.tree.node, "wrap_heights": wh, "wrap_program_rows": wrap_rows,
        "seconds": seconds, "seconds_by_kind": kind_stats, "total_seconds": secs(t_all),
    });
    std::fs::write(out.join("RESULT.json"), serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    println!("M8_TREE_WRAP_VERIFIED {result}");
}

fn verify_checked(setup_path: &str, pin: &str, bundle: &str) -> Result<(usize, f64), String> {
    let setup_bytes = std::fs::read(setup_path).map_err(|e| format!("setup: {e}"))?;
    if hash(&setup_bytes) != pin {
        return Err("untrusted setup: hash differs from the operator's pin".into());
    }
    let mut setup: HSetup = serde_json::from_slice(&setup_bytes).map_err(|e| format!("setup json: {e}"))?;
    if (setup.version, setup.domain_odd_factor) != (SETUP_VERSION, 15) {
        return Err("setup version / domain".into());
    }
    setup.final_vk.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
    let packet = std::fs::read(bundle).map_err(|e| format!("bundle: {e}"))?;
    if packet.len() < 12 || &packet[..8] != MAGIC {
        return Err("bundle framing".into());
    }
    let n = u32::from_le_bytes(packet[8..12].try_into().unwrap()) as usize;
    if packet.len() < 12 + n {
        return Err("truncated statement".into());
    }
    // ctx = claimDigest = bdigest(S) of the canonical statement bytes (plan §3.4.1); V_d does not
    // decode S (the claim-v3 decoder is the relation's, not the wrap's)
    let ctx = h::claim_ctx(&packet[12..12 + n]);
    let body = &packet[12 + n..];
    let fp = std::panic::catch_unwind(|| {
        let mut c = Cursor::new(body);
        let p = Proof::<SC>::decode(&mut c).map_err(|e| format!("proof codec: {e:?}"))?;
        if c.position() as usize != body.len() {
            return Err("trailing proof bytes".to_string());
        }
        Ok(p)
    })
    .map_err(|_| "proof codec panicked".to_string())??;
    let engine = Sha384CpuEngine::new_final(setup.final_vk.inner.params.clone());
    let t_v = std::time::Instant::now();
    let vds = VdSetup { vk_final: setup.final_vk, program: setup.program, level: setup.level, heights: Some(setup.final_heights) };
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| vd::verify_wrap(&vds, &engine, &ctx, 0, &fp)))
        .map_err(|_| "wrap verifier panicked on the proof".to_string())?
        .map_err(|e| format!("wrap verifier: {e}"))?;
    Ok((packet.len(), t_v.elapsed().as_secs_f64() * 1e3))
}

pub fn tree_verify(setup_path: &str, pin: &str, bundle: &str) {
    let t_all = std::time::Instant::now();
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = verify_checked(setup_path, pin, bundle);
    std::panic::set_hook(hook);
    match r {
        Ok((len, ms)) => {
            println!("VERIFY_PROFILE_MS total={:.2} wrap_verify={ms:.2}", t_all.elapsed().as_secs_f64() * 1e3);
            println!("INDEPENDENT_HTREE_VERIFY_OK bundle_bytes={len}");
        }
        Err(e) => {
            println!("HTREE_VERIFY_REJECT {e}");
            std::process::exit(1);
        }
    }
}
