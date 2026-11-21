//! E2E M5d prover (lane G): the FINAL / INIT template of one chunk, on the main PQ stack.
//!
//!   nearproof-e2e-m5d <air.json> <names.json> <dump_dir> check|prove|mutant [out_dir]
//!
//! A copy of lane B's M5a prover (`../../m5a/prover`, B-T1 version; unchanged modules `air.rs`,
//! `sha384/{config,mb}.rs`, `sha256gen.rs`, `s384/`) with the table list taken from `names.json`
//! (`m5d-tool air-*`) and no public tape:
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
//!
//! **G-2 (templates, as lane B's B-T1).** A dump written by `tracegen.py --template T` carries
//! `template.json` (the class's pinned per-table log heights, `SHA` and `SHA512` included, and its
//! parameters). Then every table is at its pinned height (the Lean tables padded by tracegen; the
//! `SHA` table and the chip padded here by their generators), the tight-height floor is the full
//! height, and the parameters are lane D's base configuration (`shaped_params_geom`: first-order
//! certificates, list decoding m = 64, `k_first` 2, `domain_odd_factor` 15, logup message length 7,
//! `zk = 0`) with query grinding 24 bits and the template's `(n_stack, log_blowup, w_stack)`, built
//! against the verifier's backend (lane D's frozen `pq-e2e-d9` copy) with `Sha384CpuEngine`.
//! `prove <out_dir>` saves `STATE.proof` (`Proof::encode`), `STATE.vk.json` (the `SavedVk` envelope
//! with `domain_odd_factor`) and `statement.json`, which lane D's `nearproof-chunk-e2e fs-count`
//! reads. Without `template.json` the old seg-v1 parameters are used (natural heights), now on the
//! same backend.
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
use openvm_stark_backend::{
    AirRef, CertSet, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    codec::Encode,
    interaction::LogUpSecurityParameters,
    keygen::types::MultiStarkVerifyingKey,
    prover::{AirProvingContext, DeviceDataTransporter, ProvingContext},
};
use sha384::config::{F, Sha384Config, Sha384CpuEngine};
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
    /// [G-2] the template (`template.json` of a `tracegen.py --template` dump)
    tmpl: Option<serde_json::Value>,
}

/// [G-2] A template's pinned log height of `table`, if any.
fn pin_of(tmpl: &Option<serde_json::Value>, table: &str) -> Option<usize> {
    tmpl.as_ref().and_then(|t| t["heights"][table].as_u64()).map(|x| x as usize)
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
    let tmpl: Option<serde_json::Value> =
        std::fs::read_to_string(d.join("template.json")).ok().map(|t| serde_json::from_str(&t).expect("template.json"));
    if let Some(t) = &tmpl {
        // every table of the export (and the chip) has a pin: one template, one shape, one vk
        for n in names.iter().map(|s| s.as_str()).chain(["SHA512"]) {
            assert!(t["heights"][n].is_u64(), "template has no pin for {n}");
        }
    }
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
        // [G-2] the chip at its pinned height: `gen_main` fills the rows past the last compression
        // with the generator's padding rows
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
    Inst { spec, mats, pubs, stmt_pubs, native, chip_if, n_comps: comps.len(), tmpl }
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

fn ctx(inst: &Inst) -> ProvingContext<CpuBackend<Sha384Config>> {
    let mut out = vec![];
    for (i, m) in inst.mats.iter().enumerate() {
        let t = &inst.spec[i];
        let pv: Vec<F> = (0..t.num_pub).map(|k| inst.pubs.get(k).copied().unwrap_or(F::ZERO)).collect();
        out.push((i, AirProvingContext::simple(m.clone(), pv)));
    }
    let base = inst.mats.len();
    for (j, (_, m)) in inst.native.iter().enumerate() {
        out.push((base + j, AirProvingContext::simple(m.clone(), vec![])));
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

/// [G-2] (as B-T1) The tight-height floor of a pinned template: every common main commits its full height,
/// so the proof's `(log_height, tight_height)` per AIR is the template's (lane D's `PinnedHeight`).
fn full_floor(inst: &Inst) -> Vec<(usize, usize, usize)> {
    let mut f = vec![];
    for (_t, m) in inst.spec.iter().zip(&inst.mats) {
        let h = m.values.len() / m.width;
        f.push((m.width, h.trailing_zeros() as usize, h));
    }
    for (_, m) in &inst.native {
        let h = m.values.len() / m.width;
        f.push((m.width, h.trailing_zeros() as usize, h));
    }
    f
}

// Upstream skips the extended-domain factor in VK serde; `pq-chunk-e2e` keeps it in an envelope.
#[derive(serde::Serialize)]
struct SavedVk<'a> {
    domain_odd_factor: usize,
    vk: &'a MultiStarkVerifyingKey<Sha384Config>,
}

/// [G-2] (as B-T1) Save the proof and vk in the stack's format (`pq-chunk-e2e` `save_proof` / `save_vk`), and
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
        eprintln!("usage: {} <air.json> <names.json> <dump_dir> check|prove|mutant [out_dir]", args[0]);
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
    if let (true, true, Some(out)) = (ver.is_ok(), st, args.get(5)) {
        save(std::path::Path::new(out), &inst, &vk, &proof, sz);
    }
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
