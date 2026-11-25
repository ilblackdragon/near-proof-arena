//! E2E A-T3: the PREP leaf (`wasmbase-tool airPrep`, `WasmBase/PrepAir.lean`).
//!
//!   nearproof-wasm-base prepleaf       <airPrep.json> <code.wasm> <prep.json> <template.json> <out_dir>
//!   nearproof-wasm-base prepleafverify <airPrep.json> <out_dir> [<seg_leaf_dir> <n_seg>]
//!   nearproof-wasm-base preptamper     <airPrep.json> <code.wasm> <prep.json> <template.json> <out_dir> <seg_leaf_dir> <n_seg>
//!
//! PREP proves, for the contract code `c` (the SHA-256 message of its `SHA256` table), that
//! `SHA-256(c)` is the public code hash (32 bytes + the length; `PrepSound.prep_sha_sound` [K]), and commits the
//! padded CODE / FUNC record matrices as cached traces with the **segment AIR's own** `CODE` / `FUNC`
//! tables, at the segment template's height and commitment parameters.  Its cached commitments are
//! therefore exactly the segment leaves' `code_root` / `func_root` (R1, `a-t1/README.md` §4); the
//! tree compares them (`prepleafverify` with a segment leaf directory does the same comparison).
//! The decode / validate / instrument certificate tying the records to `c` is not in this AIR yet
//! (`TmplPrep.RecordsCert`).  Heights are pinned exactly as `segleaf` pins them (A-T2: every common
//! main committed at its full template height), so the PREP leaf is one lane D leaf program.
use crate::air::{AirSpec, JsonAir};
use crate::config::{F, Sha384Config, Sha384RefEngine};
use crate::seg;
use crate::segcmd::{full_tight_floor, load, proof_heights, read_template, read_vk, save_vk, sha256_hex, template_params};
use crate::sha;
use crate::tracegen::{self, Prep};
use openvm_stark_backend::{
    AirRef, StarkEngine,
    codec::{Decode, Encode},
    prover::{AirProvingContext, ColMajorMatrix, CommittedTraceData, CpuColMajorBackend, DeviceDataTransporter, ProvingContext, TraceCommitter},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;
use std::time::Instant;

const HID: u64 = 53;
const MID: u64 = 1;

/// The public values: the 32 code-hash bytes, then the length (`PrepAir.lean`: `pubHash`, `pubLen`).
pub fn prep_pubs(code: &[u8]) -> Vec<F> {
    let d = sha::digest_bytes(code);
    let mut v: Vec<F> = d.iter().map(|&b| F::from_u64(b as u64)).collect();
    v.push(F::from_u64(code.len() as u64));
    v
}

/// `PrepSound.hashOf`: the hex of the 32 hash bytes the publics carry.
fn hash_hex(pubs: &[u64]) -> String {
    pubs[..32].iter().map(|x| format!("{:02x}", x & 0xff)).collect()
}

/// What a PREP trace is built from (each field can be tampered independently).
#[derive(Clone)]
pub struct PrepIn {
    /// the SHA-256 message (the code bytes)
    pub msg: Vec<u8>,
    /// the length announced in the summary (`PHDR` reads it from the public values)
    pub pubs: Vec<F>,
    /// the CODE / FUNC record rows (before template padding)
    pub code: Vec<[u64; 8]>,
    pub func: Vec<[u64; 8]>,
}

impl PrepIn {
    pub fn honest(code: &[u8], prep: &Prep) -> PrepIn {
        PrepIn { msg: code.to_vec(), pubs: prep_pubs(code), code: tracegen::code_rows(&prep.records), func: tracegen::func_rows(prep) }
    }
}

fn rows_mat(rows: &[[u64; 8]]) -> RowMajorMatrix<F> {
    RowMajorMatrix::new(rows.iter().flat_map(|r| r.iter().map(|&x| F::from_u64(x))).collect(), 8)
}

/// A cached record table (`CODE` / `FUNC`): the padded record matrix plus a zero `mult` column.
fn with_mult(m: &RowMajorMatrix<F>) -> RowMajorMatrix<F> {
    let mut v = vec![];
    for r in m.values.chunks(8) {
        v.extend_from_slice(r);
        v.push(F::ZERO);
    }
    RowMajorMatrix::new(v, 9)
}

/// The four matrices of `prepAir`, at the template heights.
pub fn prep_mats(spec: &AirSpec, inp: &PrepIn) -> Vec<RowMajorMatrix<F>> {
    let mut out = vec![];
    for t in &spec.tables {
        let m = match t.name.as_str() {
            "PHDR" => {
                let h = seg::tmpl_h("PHDR", 4);
                let mut v = vec![F::ZERO; h];
                v[0] = F::ONE;
                RowMajorMatrix::new(v, 1)
            }
            "SHA256" => {
                let len = inp.pubs[32].as_canonical_u32() as u64;
                let r = sha::rows(&[sha::Msg { id: MID, bytes: inp.msg.clone(), dmult: true }], 0, 0, HID, 0, len);
                let h = seg::tmpl_h("SHA256", r.rows.len());
                let mut v: Vec<F> = r.rows.iter().flat_map(|row| row.iter().map(|&x| F::from_u64(x))).collect();
                v.resize(h * sha::NCOLS, F::ZERO);
                RowMajorMatrix::new(v, sha::NCOLS)
            }
            "CODE" => with_mult(&seg::pad_rep("CODE", &rows_mat(&inp.code))),
            "FUNC" => with_mult(&seg::pad_rep("FUNC", &rows_mat(&inp.func))),
            n => panic!("prepAir: unexpected table {n}"),
        };
        assert_eq!(m.width, t.cols.len(), "{} width", t.name);
        out.push(m);
    }
    out
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

fn split_cols(m: &RowMajorMatrix<F>, c: usize) -> (RowMajorMatrix<F>, RowMajorMatrix<F>) {
    let w = m.width;
    let (mut a, mut b) = (vec![], vec![]);
    for row in m.values.chunks(w) {
        a.extend_from_slice(&row[..c]);
        b.extend_from_slice(&row[c..]);
    }
    (RowMajorMatrix::new(a, c), RowMajorMatrix::new(b, w - c))
}

fn ctx(eng: &Sha384RefEngine, spec: &AirSpec, mats: &[RowMajorMatrix<F>], pubs: &[F]) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
    let mut out = vec![];
    for (i, m) in mats.iter().enumerate() {
        let t = &spec.tables[i];
        let pv = if JsonAir::reads_pub(t) { pubs.to_vec() } else { vec![] };
        if t.cached == 0 {
            out.push((i, AirProvingContext::simple(ColMajorMatrix::from_row_major(m), pv)));
        } else {
            let (cm, rest) = split_cols(m, t.cached);
            let cm = ColMajorMatrix::from_row_major(&cm);
            let (commitment, data) = eng.device().commit(&[&cm]).expect("commit cached");
            let cached = CommittedTraceData { commitment, trace: cm, data: Arc::new(data) };
            out.push((i, AirProvingContext { cached_mains: vec![cached], common_main: ColMajorMatrix::from_row_major(&rest), public_values: pv }));
        }
    }
    ProvingContext::new(out)
}

/// The pinned `(log_height, tight_height)` per table of the PREP template (every common main at
/// its full template height, as `segleaf`).
fn prep_heights(spec: &AirSpec, th: &std::collections::HashMap<String, usize>, l_skip: usize) -> Vec<(usize, Option<usize>)> {
    spec.tables
        .iter()
        .map(|t| {
            let h = *th.get(&t.name).unwrap_or_else(|| panic!("template: no height for {}", t.name));
            assert!(h.is_power_of_two(), "template height {h}");
            (h.trailing_zeros() as usize, (h >= 1 << l_skip).then_some(h))
        })
        .collect()
}

type Proof = openvm_stark_backend::proof::Proof<Sha384Config>;

fn cached_words(spec: &AirSpec, p: &Proof, name: &str) -> Vec<u64> {
    p.trace_vdata[spec.index(name)].as_ref().expect("cached").cached_commitments[0].to_vec()
}

fn root_words(eng: &Sha384RefEngine, m: &RowMajorMatrix<F>) -> Vec<u64> {
    let (c, _) = eng.device().commit(&[&ColMajorMatrix::from_row_major(m)]).expect("root");
    c.to_vec()
}

fn read_code(path: &str) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|e| panic!("code {path}: {e}"))
}

pub fn cmd_prepleaf(a: &[String]) {
    crate::set_levers();
    let spec = load(&a[0]);
    let code = read_code(&a[1]);
    let prep = Prep::parse(&std::fs::read_to_string(&a[2]).unwrap());
    let tp = read_template(&a[3]);
    let out = std::path::Path::new(&a[4]);
    std::fs::create_dir_all(out).unwrap();
    seg::TEMPLATE.set(tp.heights.clone()).expect("template set once");
    let inp = PrepIn::honest(&code, &prep);
    let mats = prep_mats(&spec, &inp);
    seg::precheck(&spec, &mats, &inp.pubs, &[]).unwrap_or_else(|e| panic!("PREP precheck: {e}"));
    println!("PRECHECK ok: code {} B, sha256 {}, SHA256 rows {} (live {}), CODE {} records, FUNC {} rows",
        code.len(), sha256_hex(&code), mats[spec.index("SHA256")].values.len() / sha::NCOLS,
        sha::rows(&[sha::Msg { id: MID, bytes: code.clone(), dmult: true }], 0, 0, HID, 0, code.len() as u64).live,
        prep.records.len(), prep.funcs.len());
    let prm = template_params(&tp);
    let pinned = prep_heights(&spec, &tp.heights, prm.l_skip);
    println!("PARAMS n_stack {} w_stack {} log_blowup {} pow {} degree {} (the segment template's)",
        prm.n_stack, prm.w_stack, prm.log_blowup, tp.pow, prm.max_constraint_degree);
    let eng = Sha384RefEngine::new(prm);
    let t = Instant::now();
    let (pk, vk) = eng.keygen(&airs(&spec));
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!("KEYGEN {:.2}s; SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}",
        t.elapsed().as_secs_f64(), b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits);
    let vkb = save_vk(&out.join("PREP.vk.json"), &vk);
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let t = Instant::now();
    let pc = ctx(&eng, &spec, &mats, &inp.pubs);
    openvm_stark_backend::prover::stacked_pcs::set_tight_floor(Some(full_tight_floor(&pc)));
    let proof = eng.prove(&d_pk, pc).expect("prove");
    openvm_stark_backend::prover::stacked_pcs::set_tight_floor(None);
    let tp_s = t.elapsed().as_secs_f64();
    assert_eq!(proof_heights(&proof), pinned, "PREP proof heights are not the template's pinned heights");
    let t = Instant::now();
    eng.verify(&vk, &proof).expect("verify");
    let tv = t.elapsed().as_secs_f64();
    let mut pb = vec![];
    proof.encode(&mut pb).unwrap();
    std::fs::write(out.join("prep.proof"), &pb).unwrap();
    let code_root = cached_words(&spec, &proof, "CODE");
    let func_root = cached_words(&spec, &proof, "FUNC");
    // the canonical roots: the commitments of the padded record matrices (what `segleaf` writes)
    let want_code = root_words(&eng, &seg::pad_rep("CODE", &tracegen::code_matrix(&prep.records)));
    let want_func = root_words(&eng, &seg::pad_rep("FUNC", &tracegen::func_matrix(&prep)));
    assert_eq!(code_root, want_code, "PREP cached CODE commitment = canonical code_root");
    assert_eq!(func_root, want_func, "PREP cached FUNC commitment = canonical func_root");
    let pubs: Vec<u32> = inp.pubs.iter().map(|x| x.as_canonical_u32()).collect();
    let pj = serde_json::to_vec(&serde_json::json!({
        "pubs": pubs, "code_hash": sha256_hex(&code), "code_len": code.len(),
        "wasm_fields": { "in_code_root": format!("{}{}", sha256_hex(&code), "00".repeat(10)),
                         "out_code_root_words": code_root, "out_func_root_words": func_root }
    })).unwrap();
    std::fs::write(out.join("prep.pubs.json"), &pj).unwrap();
    let m = serde_json::json!({
        "template": tp.raw, "vk_sha256": sha256_hex(&vkb), "soundness_bits": b.total_bits,
        "pinned_heights": pinned, "proof_bytes": pb.len(), "proof_sha256": sha256_hex(&pb), "pubs_sha256": sha256_hex(&pj),
        "prove_s": tp_s, "verify_ms": tv * 1000.0, "code_root": code_root, "func_root": func_root,
    });
    std::fs::write(out.join("manifest.json"), serde_json::to_vec_pretty(&m).unwrap()).unwrap();
    println!("PREPLEAF OK: {} B, prove {tp_s:.1}s, verify {:.0} ms, vk sha256 {}, peak_rss_kib {}",
        pb.len(), tv * 1000.0, sha256_hex(&vkb), crate::peak_rss_kib());
    println!("  code_root {:?}\n  func_root {:?}", code_root, func_root);
}

/// The verifier side: reload, verify, pinned heights, public values = saved and canonical
/// (16-bit halves), published roots = the proof's cached commitments, and (with a segment leaf
/// directory) PREP's out roots = every segment leaf's cached CODE / FUNC roots (the tree's R1
/// equality).  Returns `Err(stage)` instead of panicking, for the tamper battery.
fn verify_dir(spec: &AirSpec, out: &std::path::Path, seg: Option<(&std::path::Path, usize)>) -> Result<String, String> {
    let man: serde_json::Value = serde_json::from_slice(&std::fs::read(out.join("manifest.json")).map_err(|e| format!("manifest {e}"))?)
        .map_err(|e| format!("manifest {e}"))?;
    let vkb = std::fs::read(out.join("PREP.vk.json")).map_err(|e| format!("vk {e}"))?;
    if sha256_hex(&vkb) != man["vk_sha256"].as_str().unwrap_or("") {
        return Err("vk hash".into());
    }
    let vk = read_vk(&out.join("PREP.vk.json"));
    let eng = Sha384RefEngine::new(vk.inner.params.clone());
    let th: std::collections::HashMap<String, usize> = man["template"]["heights"].as_object().ok_or("template heights")?
        .iter().map(|(k, h)| (k.clone(), h.as_u64().unwrap() as usize)).collect();
    let pinned = prep_heights(spec, &th, vk.inner.params.l_skip);
    let pb = std::fs::read(out.join("prep.proof")).map_err(|e| format!("proof {e}"))?;
    let mut c = std::io::Cursor::new(&pb[..]);
    let proof = Proof::decode(&mut c).map_err(|e| format!("proof codec {e:?}"))?;
    if c.position() as usize != pb.len() {
        return Err("trailing proof bytes".into());
    }
    let pj: serde_json::Value = serde_json::from_slice(&std::fs::read(out.join("prep.pubs.json")).map_err(|e| format!("pubs {e}"))?)
        .map_err(|e| format!("pubs {e}"))?;
    let pubs_u: Vec<u64> = pj["pubs"].as_array().ok_or("pubs")?.iter().map(|x| x.as_u64().unwrap()).collect();
    if pubs_u.len() != 33 || pubs_u[..32].iter().any(|&x| x >= 1 << 8) {
        return Err("public values not 32 bytes + length".into());
    }
    let pubs: Vec<F> = pubs_u.iter().map(|&x| F::from_u64(x)).collect();
    let t = Instant::now();
    eng.verify(&vk, &proof).map_err(|e| format!("verifier {e:?}"))?;
    let tv = t.elapsed().as_secs_f64();
    if proof_heights(&proof) != pinned {
        return Err("heights are not the template's pinned heights".into());
    }
    let pv_ok = spec.tables.iter().enumerate().all(|(ti, t)| {
        let want: Vec<F> = if JsonAir::reads_pub(t) { pubs.clone() } else { vec![] };
        proof.public_values[ti] == want
    });
    if !pv_ok {
        return Err("public values".into());
    }
    // the code hash the public values encode = the saved `in_code_root` (B_in.wasm.codeRoot, S2)
    let hex: String = hash_hex(&pubs_u) + &"00".repeat(10);
    if pj["wasm_fields"]["in_code_root"].as_str() != Some(hex.as_str()) {
        return Err("in_code_root != public hash".into());
    }
    for (name, key) in [("CODE", "out_code_root_words"), ("FUNC", "out_func_root_words")] {
        let want = cached_words(spec, &proof, name);
        let got: Vec<u64> = pj["wasm_fields"][key].as_array().ok_or(key)?.iter().map(|x| x.as_u64().unwrap()).collect();
        if got != want {
            return Err(format!("published {name} root != proof's cached commitment"));
        }
    }
    if let Some((sd, n)) = seg {
        for i in 0..n {
            let sj: serde_json::Value = serde_json::from_slice(&std::fs::read(sd.join(format!("seg-{i}.pubs.json"))).map_err(|e| format!("seg {e}"))?)
                .map_err(|e| format!("seg {e}"))?;
            for (name, key) in [("CODE", "code_root_words"), ("FUNC", "func_root_words")] {
                let seg_w: Vec<u64> = sj["wasm_fields"][key].as_array().ok_or(key)?.iter().map(|x| x.as_u64().unwrap()).collect();
                if seg_w != cached_words(spec, &proof, name) {
                    return Err(format!("R1: PREP {name} root != segment {i}'s cached {name} root"));
                }
            }
        }
    }
    Ok(format!("{} B verified in {:.0} ms", pb.len(), tv * 1000.0))
}

pub fn cmd_prepleafverify(a: &[String]) {
    crate::set_levers();
    let spec = load(&a[0]);
    let out = std::path::Path::new(&a[1]);
    let seg = a.get(2).map(|d| (std::path::Path::new(d.as_str()), a[3].parse::<usize>().unwrap()));
    match verify_dir(&spec, out, seg) {
        Ok(m) => println!("PREPLEAFVERIFY OK: {m}; heights = template's pinned; public values = saved, 32 bytes + length; \
            roots = cached commitments{}", if seg.is_some() { "; R1: = every segment leaf's CODE/FUNC roots" } else { "" }),
        Err(e) => {
            println!("PREPLEAFVERIFY FAIL: {e}");
            std::process::exit(1);
        }
    }
}

fn copy_dir(from: &std::path::Path, to: &std::path::Path) {
    std::fs::create_dir_all(to).unwrap();
    for e in std::fs::read_dir(from).unwrap() {
        let e = e.unwrap();
        std::fs::copy(e.path(), to.join(e.file_name())).unwrap();
    }
}

/// The tamper battery.  Trace mutants are re-proved (the pre-check result is reported, then the
/// prover runs anyway) and the saved directory is verified; saved-file mutants edit a copy of the
/// honest directory.  Every mutant must be rejected by some stage.
pub fn cmd_preptamper(a: &[String]) {
    crate::set_levers();
    let spec = load(&a[0]);
    let code = read_code(&a[1]);
    let prep = Prep::parse(&std::fs::read_to_string(&a[2]).unwrap());
    let tp = read_template(&a[3]);
    let honest_dir = std::path::Path::new(&a[4]);
    let seg_dir = std::path::Path::new(&a[5]);
    let nseg: usize = a[6].parse().unwrap();
    seg::TEMPLATE.set(tp.heights.clone()).expect("template set once");
    let vk = read_vk(&honest_dir.join("PREP.vk.json"));
    let eng = Sha384RefEngine::new(vk.inner.params.clone());
    let prm = template_params(&tp);
    assert_eq!(prm.l_skip, vk.inner.params.l_skip);
    let (pk, vk2) = eng.keygen(&airs(&spec));
    assert_eq!(serde_json::to_vec(&vk2).unwrap(), serde_json::to_vec(&vk).unwrap(), "keygen reproduces the saved vk");
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let honest = PrepIn::honest(&code, &prep);
    let work = honest_dir.parent().unwrap().join("tamper");
    let mut results = vec![];
    // trace mutants
    let mut cases: Vec<(&str, PrepIn, bool)> = vec![];
    let mut m = honest.clone();
    m.msg[100] ^= 1;
    cases.push(("wrong code byte (byte 100 flipped; public hash kept)", m, false));
    let mut m = honest.clone();
    m.pubs[0] = F::from_u64((m.pubs[0].as_canonical_u32() as u64 + 1) & 0xff);
    cases.push(("wrong hash (public byte 0 + 1)", m, false));
    let mut m = honest.clone();
    m.pubs[32] = m.pubs[32] + F::ONE;
    cases.push(("wrong length (public length + 1)", m, false));
    let mut m = honest.clone();
    m.func[0][2] += 1;
    cases.push(("wrong func record (FUNC row 0 charge + 1)", m, false));
    let mut m = honest.clone();
    m.code[3][1] += 1;
    cases.push(("wrong code record (CODE row 3 op + 1)", m, false));
    let mut m = honest.clone();
    m.code.swap(0, 1);
    cases.push(("code records out of pc order (rows 0, 1 swapped)", m, false));
    // the CODE table committed with the FUNC records and vice versa (each at its own template
    // height: FUNC's rows repeated into CODE, CODE's first rows into FUNC)
    let mut m = honest.clone();
    let (c0, f0) = (m.code.clone(), m.func.clone());
    let nf = f0.len().max(1).min(c0.len());
    m.code = f0;
    m.func = c0[..nf].to_vec();
    cases.push(("swapped code root (CODE committed with the FUNC records, FUNC with CODE's)", m, false));
    cases.push(("natural tight heights (no pinned floor)", honest.clone(), true));
    for (k, (name, inp, natural)) in cases.into_iter().enumerate() {
        let mats = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prep_mats(&spec, &inp))) {
            Ok(m) => m,
            Err(_) => {
                println!("  MUTANT {k} {name}: REJECTED: refused by the template (SEGFIT)");
                results.push(true);
                continue;
            }
        };
        let pre = seg::precheck(&spec, &mats, &inp.pubs, &[]);
        let dir = work.join(format!("t{k}"));
        let _ = std::fs::remove_dir_all(&dir);
        copy_dir(honest_dir, &dir);
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let pc = ctx(&eng, &spec, &mats, &inp.pubs);
            if !natural {
                openvm_stark_backend::prover::stacked_pcs::set_tight_floor(Some(full_tight_floor(&pc)));
            }
            let p = eng.prove(&d_pk, pc);
            openvm_stark_backend::prover::stacked_pcs::set_tight_floor(None);
            p
        }));
        openvm_stark_backend::prover::stacked_pcs::set_tight_floor(None);
        let verdict = match res {
            Err(_) => Err("prover panicked".to_string()),
            Ok(Err(e)) => Err(format!("prover error {e:?}")),
            Ok(Ok(proof)) => {
                let mut pb = vec![];
                proof.encode(&mut pb).unwrap();
                std::fs::write(dir.join("prep.proof"), &pb).unwrap();
                // the prover publishes what the trace says
                let mut pj: serde_json::Value = serde_json::from_slice(&std::fs::read(dir.join("prep.pubs.json")).unwrap()).unwrap();
                let pubs: Vec<u32> = inp.pubs.iter().map(|x| x.as_canonical_u32()).collect();
                pj["pubs"] = serde_json::json!(pubs);
                let pu: Vec<u64> = pubs.iter().map(|&x| x as u64).collect();
                let hex: String = hash_hex(&pu) + &"00".repeat(10);
                pj["wasm_fields"]["in_code_root"] = serde_json::json!(hex);
                pj["wasm_fields"]["out_code_root_words"] = serde_json::json!(cached_words(&spec, &proof, "CODE"));
                pj["wasm_fields"]["out_func_root_words"] = serde_json::json!(cached_words(&spec, &proof, "FUNC"));
                std::fs::write(dir.join("prep.pubs.json"), serde_json::to_vec(&pj).unwrap()).unwrap();
                verify_dir(&spec, &dir, Some((seg_dir, nseg)))
            }
        };
        println!("  MUTANT {k} {name}: precheck {}; {}", match &pre { Ok(()) => "ok".to_string(), Err(e) => format!("FAIL ({})", &e[..e.len().min(90)]) },
            match &verdict { Ok(m) => format!("ACCEPTED ({m})"), Err(e) => format!("REJECTED: {e}") });
        results.push(verdict.is_err());
        let _ = std::fs::remove_dir_all(&dir);
    }
    // saved-file mutants
    let file_cases: Vec<(&str, Box<dyn Fn(&std::path::Path)>)> = vec![
        ("saved proof: one byte flipped", Box::new(|d: &std::path::Path| {
            let mut b = std::fs::read(d.join("prep.proof")).unwrap();
            let i = b.len() / 2;
            b[i] ^= 1;
            std::fs::write(d.join("prep.proof"), b).unwrap();
        })),
        ("saved pubs: published code / func roots swapped", Box::new(|d: &std::path::Path| {
            let mut pj: serde_json::Value = serde_json::from_slice(&std::fs::read(d.join("prep.pubs.json")).unwrap()).unwrap();
            let c = pj["wasm_fields"]["out_code_root_words"].clone();
            pj["wasm_fields"]["out_code_root_words"] = pj["wasm_fields"]["out_func_root_words"].clone();
            pj["wasm_fields"]["out_func_root_words"] = c;
            std::fs::write(d.join("prep.pubs.json"), serde_json::to_vec(&pj).unwrap()).unwrap();
        })),
        ("saved pubs: in_code_root of another contract", Box::new(|d: &std::path::Path| {
            let mut pj: serde_json::Value = serde_json::from_slice(&std::fs::read(d.join("prep.pubs.json")).unwrap()).unwrap();
            pj["wasm_fields"]["in_code_root"] = serde_json::json!(format!("{}{}", sha256_hex(b"another contract"), "00".repeat(10)));
            std::fs::write(d.join("prep.pubs.json"), serde_json::to_vec(&pj).unwrap()).unwrap();
        })),
        ("saved pubs: public hash byte 5 + 1", Box::new(|d: &std::path::Path| {
            let mut pj: serde_json::Value = serde_json::from_slice(&std::fs::read(d.join("prep.pubs.json")).unwrap()).unwrap();
            let x = pj["pubs"][5].as_u64().unwrap();
            pj["pubs"][5] = serde_json::json!((x + 1) & 0xff);
            std::fs::write(d.join("prep.pubs.json"), serde_json::to_vec(&pj).unwrap()).unwrap();
        })),
        ("saved vk: query count changed", Box::new(|d: &std::path::Path| {
            let mut v: serde_json::Value = serde_json::from_slice(&std::fs::read(d.join("PREP.vk.json")).unwrap()).unwrap();
            let s = serde_json::to_string(&v["vk"]["inner"]["params"]).unwrap();
            let _ = s;
            if let Some(q) = v.pointer_mut("/vk/inner/params/whir/rounds/0/num_queries") {
                *q = serde_json::json!(q.as_u64().unwrap() - 1);
            } else {
                v["domain_odd_factor"] = serde_json::json!(v["domain_odd_factor"].as_u64().unwrap() + 2);
            }
            std::fs::write(d.join("PREP.vk.json"), serde_json::to_vec(&v).unwrap()).unwrap();
        })),
        ("segment leaves of another code (segment CODE root word 0 + 1)", Box::new(|_d: &std::path::Path| {})),
    ];
    let nfile = file_cases.len();
    for (k, (name, f)) in file_cases.into_iter().enumerate() {
        let dir = work.join(format!("f{k}"));
        let _ = std::fs::remove_dir_all(&dir);
        copy_dir(honest_dir, &dir);
        f(&dir);
        let segd = work.join(format!("s{k}"));
        let _ = std::fs::remove_dir_all(&segd);
        copy_dir(seg_dir, &segd);
        if k + 1 == nfile {
            let mut sj: serde_json::Value = serde_json::from_slice(&std::fs::read(segd.join("seg-0.pubs.json")).unwrap()).unwrap();
            let x = sj["wasm_fields"]["code_root_words"][0].as_u64().unwrap();
            sj["wasm_fields"]["code_root_words"][0] = serde_json::json!(x ^ 1);
            std::fs::write(segd.join("seg-0.pubs.json"), serde_json::to_vec(&sj).unwrap()).unwrap();
        }
        let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_dir(&spec, &dir, Some((&segd, nseg)))))
            .unwrap_or_else(|_| Err("verifier panicked (vk / proof decoding)".into()));
        println!("  MUTANT f{k} {name}: {}", match &verdict { Ok(m) => format!("ACCEPTED ({m})"), Err(e) => format!("REJECTED: {e}") });
        results.push(verdict.is_err());
        let _ = std::fs::remove_dir_all(&dir);
        let _ = std::fs::remove_dir_all(&segd);
    }
    let _ = std::fs::remove_dir_all(&work);
    let rej = results.iter().filter(|&&r| r).count();
    println!("PREPTAMPER {rej}/{} rejected", results.len());
    assert_eq!(rej, results.len(), "a mutant was accepted");
}
