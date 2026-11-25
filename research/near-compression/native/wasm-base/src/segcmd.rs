//! E2E M4 commands: a call cut into segments, checked, proved and chained by hand.
//!
//!   nearproof-wasm-base segcheck  <airSeg.json> <airM2.json> <prep.json> <steps_per_segment>
//!   nearproof-wasm-base segprove  <airSeg.json> <airM2.json> <prep.json> <steps_per_segment>
//!   nearproof-wasm-base segtamper <airSeg.json> <airM2.json> <prep.json> <steps_per_segment> <segment>
//!   nearproof-wasm-base segdump   <airSeg.json> <airM2.json> <prep.json> <steps_per_segment> <out_prefix>
//!     (M4c: write every segment's trace, publics and chip inputs to `<out_prefix>-<i>.bin`, `dump.rs`)
//!
//! `<airSeg.json>` is `wasmbase-tool airSegMP` (M4b, the multiproof MPATH: the default segment AIR
//! since M4c, sound by `seg_sound_mp`; its tamper battery adds the MPATH-MP cases, `tampers_mp`),
//! `airSeg` (M4, still accepted), or `airSegG` (M4c, segments containing `memory.grow`: then
//! `<airM2.json>` is `airM3` and the prep `prepM3`; tampers add `tampers_g`, and `SEG_TAMPER_G=1`
//! runs only those).  The prover picks the variant from the json.
use crate::air::{AirSpec, JsonAir};
use crate::config::{F, Sha384Config, Sha384RefEngine};
use crate::s384;
use crate::seg::{self, SegInst, Tree};
use crate::tracegen::{self, Gen, Prep};
use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams,
    codec::Encode,
    prover::{AirProvingContext, ColMajorMatrix, CommittedTraceData, CpuColMajorBackend, DeviceDataTransporter, ProvingContext, TraceCommitter},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;
use std::time::Instant;

/// `SEG_CONTINUE=1` (E2E M6, GROW corpus runs): report a segment that fails to build or to
/// pre-check and go on with the others, instead of stopping the whole call.
fn cont() -> bool {
    std::env::var("SEG_CONTINUE").is_ok_and(|v| !v.is_empty())
}

pub(crate) fn load(p: &str) -> AirSpec {
    AirSpec::parse(&std::fs::read_to_string(p).unwrap())
}

/// Trace the whole call once with cuts every `k` steps; build every segment.
pub fn segments(seg_air: &AirSpec, m2_air: &AirSpec, prep_path: &str, k: u64) -> (Prep, Gen, Vec<SegInst>) {
    let prep = Prep::parse(&std::fs::read_to_string(prep_path).unwrap());
    let cut_at: Vec<u64> = (1..).map(|i| i * k).take_while(|&t| t < prep.steps).collect();
    let t0 = Instant::now();
    // A-T1: the segment HOSTB's write pair needs the old byte `ob` of every memory-write row; the
    // full run is traced on the M2 AIR, whose HOSTB has no such column, so it gets one (a witness
    // column only: no constraint of the M2 AIR reads it; the segment AIR checks it).
    let mut m2x = m2_air.clone();
    if seg_air.tables[seg_air.index("HOSTB")].cols.iter().any(|c| c == "ob") {
        let hb = m2x.index("HOSTB");
        if !m2x.tables[hb].cols.iter().any(|c| c == "ob") {
            m2x.tables[hb].cols.push("ob".into());
        }
    }
    let m2_air = &m2x;
    let g = tracegen::generate_cuts(m2_air, &prep, &cut_at);
    assert_eq!(g.steps, prep.steps, "step count vs spec");
    println!("TRACE steps {} cuts {} tracegen {:.2}s", g.steps, cut_at.len(), t0.elapsed().as_secs_f64());
    let mut tree = Tree::initial(&prep);
    let mut out = vec![];
    for i in 0..g.cuts.len() - 1 {
        let t1 = Instant::now();
        let s = if cont() {
            // E2E M6 (GROW): report a segment the generator cannot build and stop there
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| seg::build(seg_air, m2_air, &g, &prep, i, &mut tree))) {
                Ok(s) => s,
                Err(e) => {
                    let msg = e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|x| x.to_string())).unwrap_or_default();
                    println!("SEGBUILD FAIL {i}: {msg}");
                    break;
                }
            }
        } else {
            seg::build(seg_air, m2_air, &g, &prep, i, &mut tree)
        };
        println!("SEGBUILD {i} {:.2}s", t1.elapsed().as_secs_f64());
        out.push(s);
    }
    (prep, g, out)
}

fn cells(s: &SegInst) -> (usize, usize) {
    let main: usize = s.mats.iter().map(|m| m.values.len()).sum();
    let h = seg::tmpl_h("SHA512", s384::trace::main_height(s.comps.len()));
    (main, h * s384::air::WIDTH + 128 * s384::air::T_WIDTH)
}

fn report(spec: &AirSpec, i: usize, s: &SegInst) {
    let st = &s.stats;
    println!(
        "SEG {i} t ({}, {}] steps {} halted {} | boundary: stream in {} out {} msgs, blocks {} (read-only {}), drops {} tombs {}, compressions {} (stream {}, MEMB {}, MPATH {})",
        s.b_in.t, s.b_out.t, s.b_out.t - s.b_in.t, s.halted, st.stream_in, st.stream_out, st.blocks, st.blocks_ro,
        st.drops, st.tombs, st.comps, st.comps_stream, st.comps_memb, st.comps_mpath
    );
    if st.pages.0 != st.pages.1 || st.grown + st.high > 0 {
        println!("  GROW pages {} -> {} | grown blocks (MEMBG) {} | old blocks above 64 MiB (MEMBH) {} | depth lift {}",
            st.pages.0, st.pages.1, st.grown, st.high, st.lift);
    }
    // E2E M6 (GROW): the segment's `memory.grow` / `memory.size` rows (MEMG `f_grow` = col 5,
    // `f_size` = col 6, `ok` = col 14), so a failing grow (pages unchanged) is reported too
    if let Some(ti) = spec.tables.iter().position(|t| t.name == "MEMG") {
        let m = &s.mats[ti];
        let (mut g, mut z, mut ok) = (0usize, 0usize, 0usize);
        for row in m.values.chunks(m.width) {
            g += (row[5] == F::ONE) as usize;
            z += (row[6] == F::ONE) as usize;
            ok += (row[5] == F::ONE && row[14] == F::ONE) as usize;
        }
        if g + z > 0 {
            println!("  MEMG rows: memory.grow {g} (succeeded {ok}, failed {}) memory.size {z}", g - ok);
        }
    }
    let mut bnd_cells = 0usize;
    let mut instr_cells = 0usize;
    for (t, m) in spec.tables.iter().zip(&s.mats) {
        let w = t.cols.len();
        let h = m.values.len() / w;
        if ["SEGB", "CUTI", "CUTO", "MEMB", "MPATH", "DROP", "SEGG", "MEMBG", "MEMBH"].contains(&t.name.as_str()) {
            bnd_cells += h * w;
        } else {
            instr_cells += h * w;
        }
        if std::env::var("SEG_TABLES").is_ok() {
            println!("  TABLE {:<8} width {:>4} height {:>8} cells {:>10}", t.name, w, h, h * w);
        }
    }
    let (_, chip) = cells(s);
    println!(
        "  CELLS instruction+lookup tables {} | boundary tables {} | SHA-512 chip {} (height {}) | total {}",
        instr_cells, bnd_cells, chip, s384::trace::main_height(s.comps.len()), instr_cells + bnd_cells + chip
    );
}

fn chain_ok(segs: &[SegInst]) -> bool {
    let mut ok = true;
    for w in segs.windows(2) {
        if w[0].b_out != w[1].b_in {
            println!("CHAIN BREAK between t = {}: {:?} vs {:?}", w[0].b_out.t, w[0].b_out, w[1].b_in);
            ok = false;
        }
    }
    ok
}

pub fn cmd_segcheck(a: &[String]) {
    let (seg_air, m2_air) = (load(&a[0]), load(&a[1]));
    let k: u64 = a[3].parse().unwrap();
    let (_prep, _g, segs) = segments(&seg_air, &m2_air, &a[2], k);
    let mut bad = 0usize;
    for (i, s) in segs.iter().enumerate() {
        report(&seg_air, i, s);
        let t = Instant::now();
        match seg::precheck(&seg_air, &s.mats, &s.pubs, &s.comps) {
            Ok(()) => println!("  PRECHECK OK ({:.2}s): every constraint on every row, every bus balanced incl. the chip's interface", t.elapsed().as_secs_f64()),
            Err(e) if cont() => {
                println!("  PRECHECK FAIL: {e}");
                bad += 1;
            }
            Err(e) => panic!("segment {i}: {e}"),
        }
    }
    if cont() && (bad > 0 || segs.len() + 1 < _g.cuts.len()) {
        println!("SEGCHECK PARTIAL {} of {} segments built, {} pre-check failures, chain {}", segs.len(), _g.cuts.len() - 1, bad, chain_ok(&segs));
        return;
    }
    assert!(chain_ok(&segs), "boundary chain");
    println!("SEGCHECK OK {} segments chained: B_out(k) = B_in(k+1) for every k", segs.len());
}

/// M4c: dump every segment (after the Rust pre-check) for the Lean `HoldsX`/`ChipIf` checker.
pub fn cmd_segdump(a: &[String]) {
    let (seg_air, m2_air) = (load(&a[0]), load(&a[1]));
    let k: u64 = a[3].parse().unwrap();
    let (_prep, _g, segs) = segments(&seg_air, &m2_air, &a[2], k);
    for (i, s) in segs.iter().enumerate() {
        report(&seg_air, i, s);
        seg::precheck(&seg_air, &s.mats, &s.pubs, &s.comps).unwrap_or_else(|e| panic!("segment {i}: {e}"));
        crate::dump::write(&format!("{}-{i}.bin", a[4]), &s.mats, &s.pubs, &s.comps);
    }
    assert!(chain_ok(&segs), "boundary chain");
    println!("SEGDUMP OK {} segments", segs.len());
}

fn airs(spec: &AirSpec) -> Vec<AirRef<Sha384Config>> {
    let mut v: Vec<AirRef<Sha384Config>> = spec
        .tables
        .iter()
        .map(|t| {
            let np = if JsonAir::reads_pub(t) { spec.num_pub } else { 0 };
            Arc::new(JsonAir { spec: t.clone(), num_pub: np }) as AirRef<Sha384Config>
        })
        .collect();
    v.push(Arc::new(s384::air::Sha512Air4));
    v.push(Arc::new(s384::air::TableAir4));
    v
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

fn chip_mats(comps: &[s384::reference::Comp]) -> (RowMajorMatrix<F>, RowMajorMatrix<F>) {
    let h = seg::tmpl_h("SHA512", s384::trace::main_height(comps.len()));
    let main = s384::trace::gen_main(comps, h);
    let table = s384::trace::gen_table(&main, h);
    (
        RowMajorMatrix::new(main.iter().map(|&x| F::from_u32(x)).collect(), s384::air::WIDTH),
        RowMajorMatrix::new(table.iter().map(|&x| F::from_u32(x)).collect(), s384::air::T_WIDTH),
    )
}

fn ctx(eng: &Sha384RefEngine, spec: &AirSpec, mats: &[RowMajorMatrix<F>], pubs: &[F], comps: &[s384::reference::Comp])
    -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
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
    let (cm, ct) = chip_mats(comps);
    let base = mats.len();
    out.push((base, AirProvingContext::simple(ColMajorMatrix::from_row_major(&cm), vec![])));
    out.push((base + 1, AirProvingContext::simple(ColMajorMatrix::from_row_major(&ct), vec![])));
    ProvingContext::new(out)
}

fn params_for(segs: &[SegInst]) -> SystemParams {
    let mut total = 0usize;
    let mut maxh = 0usize;
    for s in segs {
        let (main, chip) = cells(s);
        total = total.max(main + chip);
        let mh = s.mats.iter().map(|m| m.values.len() / m.width).max().unwrap();
        maxh = maxh.max(mh).max(s384::trace::main_height(s.comps.len()));
    }
    let n_stack = [14usize, 18, 22]
        .into_iter()
        .find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24)
        .unwrap_or(22);
    let w_stack = (total.div_ceil(1 << (n_stack + 2)) + 4).max(8);
    crate::seg_v1_params(n_stack, w_stack, s384::air::DEGREE)
}

pub(crate) fn proof_size(p: &openvm_stark_backend::proof::Proof<Sha384Config>) -> usize {
    let mut b = Vec::new();
    p.encode(&mut b).unwrap();
    b.len()
}

/// The verifier's statement check for one segment: the public values of every table that reads
/// them are the segment's boundary (`pubs`), and CODE/FUNC are the contract's (`code_root`,
/// `func_root`, recomputed from the code).
fn statement_ok(eng: &Sha384RefEngine, spec: &AirSpec, proof: &openvm_stark_backend::proof::Proof<Sha384Config>, pubs: &[F], prep: &Prep) -> bool {
    let pv_ok = spec.tables.iter().enumerate().all(|(i, t)| {
        let want: Vec<F> = if JsonAir::reads_pub(t) { pubs.to_vec() } else { vec![] };
        proof.public_values[i] == want
    });
    let root = |m: RowMajorMatrix<F>| eng.device().commit(&[&ColMajorMatrix::from_row_major(&m)]).expect("root").0;
    let code = root(seg::pad_rep("CODE", &tracegen::code_matrix(&prep.records)));
    let func = root(seg::pad_rep("FUNC", &tracegen::func_matrix(prep)));
    let ok = |name: &str, want| match &proof.trace_vdata[spec.index(name)] {
        Some(v) => v.cached_commitments.len() == 1 && v.cached_commitments[0] == want,
        None => false,
    };
    pv_ok && ok("CODE", code) && ok("FUNC", func)
}

pub fn cmd_segprove(a: &[String]) {
    crate::set_levers();
    let (seg_air, m2_air) = (load(&a[0]), load(&a[1]));
    let k: u64 = a[3].parse().unwrap();
    let (prep, _g, segs) = segments(&seg_air, &m2_air, &a[2], k);
    let prm = params_for(&segs);
    println!("PARAMS n_stack {} w_stack {} degree {}", prm.n_stack, prm.w_stack, prm.max_constraint_degree);
    let eng = Sha384RefEngine::new(prm);
    let airs = airs(&seg_air);
    let t = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    println!("KEYGEN {:.2}s (one verifying key for every segment)", t.elapsed().as_secs_f64());
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!("SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}", b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits);
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let only: Option<Vec<usize>> = std::env::var("SEG_ONLY").ok().map(|s| s.split(',').map(|x| x.parse().unwrap()).collect());
    let mut total_prove = 0.0;
    for (i, s) in segs.iter().enumerate() {
        report(&seg_air, i, s);
        if let Err(e) = seg::precheck(&seg_air, &s.mats, &s.pubs, &s.comps) {
            if cont() {
                println!("  PRECHECK FAIL: {e}");
                continue;
            }
            panic!("segment {i}: {e}");
        }
        if let Some(o) = &only {
            if !o.contains(&i) {
                continue;
            }
        }
        let t = Instant::now();
        let proof = eng.prove(&d_pk, ctx(&eng, &seg_air, &s.mats, &s.pubs, &s.comps)).expect("prove");
        let tp = t.elapsed().as_secs_f64();
        total_prove += tp;
        let t = Instant::now();
        eng.verify(&vk, &proof).expect("verify");
        let tv = t.elapsed().as_secs_f64();
        assert!(statement_ok(&eng, &seg_air, &proof, &s.pubs, &prep), "segment {i}: statement");
        println!(
            "  PROOF {i}: {} B, prove {tp:.1}s, verify {:.0} ms, statement ok (boundary public values, code_root, func_root), peak_rss_kib {}",
            proof_size(&proof),
            tv * 1000.0,
            crate::peak_rss_kib()
        );
    }
    if cont() && (!chain_ok(&segs) || segs.len() + 1 < _g.cuts.len()) {
        println!("SEGPROVE PARTIAL ({} of {} segments built)", segs.len(), _g.cuts.len() - 1);
        return;
    }
    assert!(chain_ok(&segs), "boundary chain");
    println!("SEGPROVE OK {} segments, chained by hand (B_out(k) = B_in(k+1)); total prove {total_prove:.1}s", segs.len());
}

/// Tampers on one segment: each is re-proved and must fail (prover error, verifier, statement or
/// chain check).  The honest segment is proved first.
pub fn cmd_segtamper(a: &[String]) {
    crate::set_levers();
    let (seg_air, m2_air) = (load(&a[0]), load(&a[1]));
    let k: u64 = a[3].parse().unwrap();
    let which: usize = a[4].parse().unwrap();
    let (prep, _g, segs) = segments(&seg_air, &m2_air, &a[2], k);
    let prm = params_for(&segs);
    let eng = Sha384RefEngine::new(prm);
    let airs = airs(&seg_air);
    let (pk, vk) = eng.keygen(&airs);
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let s = &segs[which];
    let run = |mats: &[RowMajorMatrix<F>], pubs: &[F], comps: &[s384::reference::Comp], want_pubs: &[F]| -> Result<(), String> {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| eng.prove(&d_pk, ctx(&eng, &seg_air, mats, pubs, comps)).ok()));
        let proof = match r {
            Ok(Some(p)) => p,
            _ => return Err("prover error".into()),
        };
        eng.verify(&vk, &proof).map_err(|e| format!("verifier: {e:?}"))?;
        if !statement_ok(&eng, &seg_air, &proof, want_pubs, &prep) {
            return Err("statement / chain check".into());
        }
        Ok(())
    };
    run(&s.mats, &s.pubs, &s.comps, &s.pubs).expect("honest segment must verify");
    println!("HONEST segment {which} verifies");
    // `SEG_TAMPER_G=1`: only the `wasmBaseSegAirG` cases (`tampers_g`)
    let cases = if std::env::var("SEG_TAMPER_G").is_ok_and(|v| !v.is_empty()) { tampers_g(&seg_air, s) } else { tampers(&seg_air, s, &segs, which) };
    let (mut rej, mut acc) = (0, 0);
    for (name, mats, pubs, comps, want) in cases {
        let pre = seg::precheck(&seg_air, &mats, &pubs, &comps).err().unwrap_or_else(|| "precheck passes".into());
        match run(&mats, &pubs, &comps, &want) {
            Err(e) => {
                rej += 1;
                println!("REJECTED {name}: {e} [precheck: {}]", &pre[..pre.len().min(140)]);
            }
            Ok(()) => {
                acc += 1;
                println!("ACCEPTED {name} [precheck: {pre}]");
            }
        }
    }
    println!("SEGTAMPER {rej} rejected, {acc} accepted");
}

type Case = (String, Vec<RowMajorMatrix<F>>, Vec<F>, Vec<s384::reference::Comp>, Vec<F>);

/// The tamper battery.  Each case says what the verifier is given (`want`: the public values the
/// chain requires) and what the prover is given (`pubs`, `mats`).
fn tampers(spec: &AirSpec, s: &SegInst, segs: &[SegInst], which: usize) -> Vec<Case> {
    let mut out: Vec<Case> = vec![];
    let ti = |n: &str| spec.index(n);
    let col = |n: &str, c: &str| spec.tables[ti(n)].col(c);
    let set = |mats: &mut Vec<RowMajorMatrix<F>>, t: &str, r: usize, c: &str, f: &dyn Fn(F) -> F| {
        let (i, cc) = (ti(t), col(t, c));
        let w = mats[i].width;
        let v = mats[i].values[r * w + cc];
        mats[i].values[r * w + cc] = f(v);
    };
    let one = F::ONE;
    // (a) forged public boundary: the prover proves with a different boundary than the chain's
    for (name, idx) in [("pub ctx_out limb", seg::PUB_CTX_OUT + 3), ("pub ctx_in limb", seg::PUB_CTX_IN),
        ("pub mem_out limb", seg::PUB_MEM_OUT + 5), ("pub mem_in limb", seg::PUB_MEM_IN + 1), ("pub pc_out", seg::PUB_PC_OUT),
        ("pub S_out", seg::PUB_S_OUT), ("pub t_out", seg::PUB_T_OUT), ("pub segb_out limb", seg::PUB_GB_OUT),
        ("pub cid_in", seg::PUB_CID_IN), ("pub sb_in", seg::PUB_SB_IN), ("pub halted", seg::PUB_STATUS),
        // A-T5: the gas gadget's and the stack budget's publics are bound in-circuit
        ("pub g_out limb 0", seg::PUB_GOUT), ("pub g_out limb 3", seg::PUB_GOUT + 3), ("pub R byte 0", seg::PUB_ROP),
        ("pub S_seg_out", seg::PUB_SSEG_OUT), ("pub rem_lo", seg::PUB_REM_LO), ("pub rem_hi", seg::PUB_REM_HI)] {
        let mut p = s.pubs.clone();
        p[idx] += one;
        // (a1) honest prover rows, forged statement: the proof must not verify against it
        out.push((format!("{name}+1 (rows honest)"), s.mats.clone(), p.clone(), s.comps.clone(), p.clone()));
    }
    // (b) a forged in-boundary that is self-consistent: change one boundary message in CUTI and
    // recompute the digest (the prover re-hashes); the chain check (previous segment's ctx_out) rejects
    {
        // locate a CUTI data row
        let i = ti("CUTI");
        let w = s.mats[i].width;
        let a = col("CUTI", "act");
        if let Some(r) = (0..s.mats[i].values.len() / w).find(|&r| s.mats[i].values[r * w + a] == one) {
            let mut m = s.mats.clone();
            set(&mut m, "CUTI", r, "lo3", &|v| v + one);
            out.push(("CUTI message value+1 (digest unchanged)".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        // A-T5: SEGB's gas gadget witness (bit 0 of d; carry bit 0) flipped on every row
        for c in ["gd0", "gc0"] {
            let mut m = s.mats.clone();
            for r in 0..4 {
                set(&mut m, "SEGB", r, c, &|v| one - v);
            }
            out.push((format!("SEGB gas gadget {c} flipped"), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        // A-T5: a forged g_out with the gadget re-solved for it would need d' = d - 1, i.e. a forged
        // S_seg_out: rows and publics consistent, but the published S_seg no longer links (statement)
        {
            let mut p = s.pubs.clone();
            p[seg::PUB_SSEG_OUT] += one;
            let ok = p[seg::PUB_SSEG_OUT].as_canonical_u32() as u64 <= p[seg::PUB_S_OUT].as_canonical_u32() as u64;
            if ok {
                let r = (0..3).map(|i| (s.pubs[seg::PUB_ROP + i].as_canonical_u32() as u64) << (8 * i)).sum::<u64>();
                let sseg = p[seg::PUB_SSEG_OUT].as_canonical_u32() as u64;
                let segb: u64 = (0..4).map(|i| (s.pubs[seg::PUB_GB_OUT + i].as_canonical_u32() as u64) << (16 * i)).sum();
                let gg = seg::gas_gadget(r, s.pubs[seg::PUB_S_OUT].as_canonical_u32() as u64, sseg, segb);
                for (k, l) in tracegen::limbs(gg.g_out).into_iter().enumerate() {
                    p[seg::PUB_GOUT + k] = F::from_u64(l);
                }
                let mut m = s.mats.clone();
                for r in 0..4 {
                    for (j, &b) in gg.d_bits.iter().enumerate() {
                        set(&mut m, "SEGB", r, &format!("gd{j}"), &|_| F::from_u64(b));
                    }
                    for (j, &b) in gg.c_bits.iter().enumerate() {
                        set(&mut m, "SEGB", r, &format!("gc{j}"), &|_| F::from_u64(b));
                    }
                }
                out.push(("S_seg_out+1 with g_out and the gadget re-solved (gas register forged)".into(), m, p.clone(),
                    s.comps.clone(), p));
            }
        }
        let _ = which;
        let _ = segs;
    }
    // (c) CUTO: drop a kept message's consumption value, wrong dep, wrong order, wrong relabel
    {
        let i = ti("CUTO");
        let w = s.mats[i].width;
        let h = s.mats[i].values.len() / w;
        let act = col("CUTO", "act");
        let find = |c: &str| (0..h).find(|&r| s.mats[i].values[r * w + col("CUTO", c)] == one && s.mats[i].values[r * w + act] == one);
        if let Some(r) = find("act") {
            let mut m = s.mats.clone();
            set(&mut m, "CUTO", r, "lo4", &|v| v + one);
            out.push(("CUTO hashed value+1".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
            let mut m = s.mats.clone();
            set(&mut m, "CUTO", r, "act", &|_| F::ZERO);
            out.push(("CUTO message not consumed (act=0)".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        if let Some(r) = find("kL") {
            let mut m = s.mats.clone();
            set(&mut m, "CUTO", r, "lo0", &|v| v + one);
            out.push(("CUTO local relabelled to another depth".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        if let Some(r) = find("k4") {
            let mut m = s.mats.clone();
            set(&mut m, "CUTO", r, "dep", &|v| v + one);
            out.push(("CUTO record depth+1".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        if let Some(r) = find("k0") {
            let mut m = s.mats.clone();
            set(&mut m, "CUTO", r, "same", &|v| one - v);
            out.push(("CUTO order flag flipped".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
    }
    // (d) DROP: drop without a tombstone; tomb multiplicity
    {
        let i = ti("DROP");
        let w = s.mats[i].width;
        let h = s.mats[i].values.len() / w;
        let (act, ist) = (col("DROP", "act"), col("DROP", "isT"));
        if let Some(r) = (0..h).find(|&r| s.mats[i].values[r * w + act] == one && s.mats[i].values[r * w + ist] == F::ZERO) {
            let mut m = s.mats.clone();
            set(&mut m, "DROP", r, "c", &|v| v + one);
            out.push(("DROP a local of a live/other activation (c+1)".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        if let Some(r) = (0..h).find(|&r| s.mats[i].values[r * w + ist] == one) {
            let mut m = s.mats.clone();
            set(&mut m, "DROP", r, "m", &|v| v + one);
            out.push(("DROP tomb multiplicity+1".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
    }
    // (e) MEMB: an in-byte changed (leaf no longer the tree's), an out-byte changed, read-only flag
    {
        let i = ti("MEMB");
        let w = s.mats[i].width;
        let h = s.mats[i].values.len() / w;
        let p0 = col("MEMB", "p0");
        if let Some(r) = (0..h).find(|&r| s.mats[i].values[r * w + p0] == one) {
            for c in ["bi7", "bo7", "tq7", "blk"] {
                let mut m = s.mats.clone();
                set(&mut m, "MEMB", r, c, &|v| v + one);
                out.push((format!("MEMB {c}+1"), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
            }
            let mut m = s.mats.clone();
            set(&mut m, "MEMB", r, "ro", &|v| one - v);
            out.push(("MEMB read-only flag flipped".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
    }
    // (f') MPATH as a multiproof (`wasmBaseSegAirMP`)
    if spec.tables[ti("MPATH")].cols.iter().any(|c| c == "idx") {
        out.extend(tampers_mp(spec, s));
        // (f'') `wasmBaseSegAirG`: the size message, grown blocks, the lift root
        if spec.tables.iter().any(|t| t.name == "SEGG") {
            out.extend(tampers_g(spec, s));
        }
    } else
    // (f) MPATH: sibling, direction bit, root chain
    {
        let i = ti("MPATH");
        let w = s.mats[i].width;
        let h = s.mats[i].values.len() / w;
        let a = col("MPATH", "act");
        if let Some(r) = (0..h).find(|&r| s.mats[i].values[r * w + a] == one) {
            for c in ["sb0", "bit", "ri0", "rt0"] {
                let mut m = s.mats.clone();
                set(&mut m, "MPATH", r, c, &|v| if c == "bit" { one - v } else { v + one });
                out.push((format!("MPATH {c} changed"), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
            }
        }
    }
    // (g) SEGB: final cid label, gas register tp; HOST gas register value
    {
        let mut m = s.mats.clone();
        set(&mut m, "SEGB", 0, "cidf", &|v| v + one);
        out.push(("SEGB final cid+1".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        let i = ti("HOST");
        let w = s.mats[i].width;
        let h = s.mats[i].values.len() / w;
        let a = col("HOST", "act");
        if let Some(r) = (0..h).find(|&r| s.mats[i].values[r * w + a] == one) {
            let mut m = s.mats.clone();
            set(&mut m, "HOST", r, "gb0", &|v| v + one);
            out.push(("HOST gas register segb limb+1".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
    }
    // (h) the call-key bus (E2E M4c, LINK): HOSTB / REG-C rows whose `(ts, hid)` is no HOST row's
    if spec.tables[ti("HOST")].cols.iter().any(|c| c == "nk") {
        out.extend(tampers_key(spec, s));
    }
    out
}

/// Tampers of the call-key bus (`Seg.busHKey`).  Each forges a HOSTB / REG-C call key that no active
/// HOST row offers, in a way the other buses and constraints do not see (the M4c CORE counterexamples
/// to `HostBLinked.linked` / `RegCLinked`), or forges HOST's multiplicity `nk`.
fn tampers_key(spec: &AirSpec, s: &SegInst) -> Vec<Case> {
    let mut out: Vec<Case> = vec![];
    let ti = |n: &str| spec.index(n);
    let col = |n: &str, c: &str| spec.tables[ti(n)].col(c);
    let one = F::ONE;
    let rows = |m: &Vec<RowMajorMatrix<F>>, t: &str| m[ti(t)].values.len() / m[ti(t)].width;
    let get = |m: &Vec<RowMajorMatrix<F>>, t: &str, r: usize, c: &str| m[ti(t)].values[r * m[ti(t)].width + col(t, c)];
    let put = |m: &mut Vec<RowMajorMatrix<F>>, t: &str, r: usize, c: &str, v: F| {
        let (i, cc) = (ti(t), col(t, c));
        let w = m[i].width;
        m[i].values[r * w + cc] = v;
    };
    // a HOST call whose key is looked up
    let hk = (0..rows(&s.mats, "HOST")).find(|&r| get(&s.mats, "HOST", r, "act") == one && get(&s.mats, "HOST", r, "nk") != F::ZERO);
    if let Some(r) = hk {
        let (ts, hid) = (get(&s.mats, "HOST", r, "ts"), get(&s.mats, "HOST", r, "hid"));
        // (h1) relabel the call's hid (+1000) on HOSTB and/or REG-C rows: bus 210 between them and
        // every group constraint stay consistent; only the key lookup has no HOST row to land on
        for (name, tabs) in [("HOSTB+REG-C call key relabelled (hid+1000)", vec!["HOSTB", "REG"]),
            ("HOSTB call key relabelled (hid+1000)", vec!["HOSTB"]), ("REG-C call key relabelled (hid+1000)", vec!["REG"])] {
            let mut m = s.mats.clone();
            let mut n = 0;
            for t in tabs.iter() {
                for q in 0..rows(&m, t) {
                    if get(&m, t, q, "act") == one && get(&m, t, q, "ts") == ts && get(&m, t, q, "hid") == hid {
                        put(&mut m, t, q, "hid", hid + F::from_u32(1000));
                        n += 1;
                    }
                }
            }
            if n > 0 {
                out.push((format!("{name}, {n} rows"), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
            }
        }
        // (h2) HOST offers its key once more / once less than it is looked up
        for (name, d) in [("HOST nk+1", one), ("HOST nk-1", -one)] {
            let mut m = s.mats.clone();
            put(&mut m, "HOST", r, "nk", get(&s.mats, "HOST", r, "nk") + d);
            out.push((name.into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
    }
    // (h4) E2E M6 FIX214: the group index bits `hg0, hg1` (wire id `hid + 256·(hg0 + 2·hg1)`)
    if spec.tables[ti("HOSTB")].cols.iter().any(|c| c == "hg0") {
        let nb = rows(&s.mats, "HOSTB");
        let act = |q: usize| get(&s.mats, "HOSTB", q, "act") == one;
        // a non-bit group index
        if let Some(q) = (0..nb).find(|&q| act(q)) {
            let mut m = s.mats.clone();
            put(&mut m, "HOSTB", q, "hg0", F::from_u32(2));
            out.push((format!("HOSTB[row {q}].hg0 = 2 (group index not a bit)"), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        // a group index that changes inside a group (row q continues row q-1's group)
        if let Some(q) = (1..nb).find(|&q| act(q) && get(&s.mats, "HOSTB", q, "f") == F::ZERO) {
            let mut m = s.mats.clone();
            put(&mut m, "HOSTB", q, "hg1", one - get(&s.mats, "HOSTB", q, "hg1"));
            out.push((format!("HOSTB[row {q}].hg1 flipped mid-group"), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
        // the pre-fix encoding of a multi-group call: `hid` = the wire id, `g = 0` (the key
        // `[ts, hid + 256·g]` is no HOST row's)
        if let Some(q) = (0..nb).find(|&q| act(q) && (get(&s.mats, "HOSTB", q, "hg0") != F::ZERO || get(&s.mats, "HOSTB", q, "hg1") != F::ZERO)) {
            let mut m = s.mats.clone();
            let ts = get(&s.mats, "HOSTB", q, "ts");
            let (h0, h1) = (get(&s.mats, "HOSTB", q, "hg0"), get(&s.mats, "HOSTB", q, "hg1"));
            let mut n = 0;
            for p in 0..nb {
                if act(p) && get(&m, "HOSTB", p, "ts") == ts && get(&m, "HOSTB", p, "hg0") == h0 && get(&m, "HOSTB", p, "hg1") == h1 {
                    let hid = get(&m, "HOSTB", p, "hid");
                    put(&mut m, "HOSTB", p, "hid", hid + F::from_u32(256) * (h0 + h1 + h1));
                    put(&mut m, "HOSTB", p, "hg0", F::ZERO);
                    put(&mut m, "HOSTB", p, "hg1", F::ZERO);
                    n += 1;
                }
            }
            out.push((format!("HOSTB group at ts {} in the pre-fix wire-id encoding (hid += 256*g, g = 0), {n} rows", ts.as_canonical_u32()),
                m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
        }
    }
    // (h5) A-T1: HOSTB's memory-write pair (`Seg.HostBK.writeInters`, count `act·dir·(1−reg)`): a
    // response byte of a `setU128H` host consumes the live byte `ob` at `mtp` and produces `byte` at
    // `ts`.  Every tamper is recounted (BYTE/RANGE16 multiplicities), so only the write pair can
    // reject it.
    if spec.tables[ti("HOSTB")].cols.iter().any(|c| c == "ob") {
        let nb = rows(&s.mats, "HOSTB");
        let wr = |m: &Vec<RowMajorMatrix<F>>, q: usize| get(m, "HOSTB", q, "act") == one && get(m, "HOSTB", q, "dir") == one
            && get(m, "HOSTB", q, "reg") == F::ZERO;
        if let Some(q) = (0..nb).find(|&q| wr(&s.mats, q)) {
            let ts = get(&s.mats, "HOSTB", q, "ts");
            let mut cases: Vec<(String, Vec<RowMajorMatrix<F>>)> = vec![];
            for (c, d) in [("byte", 1u32), ("ob", 1), ("mtp", 1), ("ptrLo", 1), ("pos", 0)] {
                let mut m = s.mats.clone();
                if c == "pos" {
                    // the write lands one address later (pos and gap shifted together, `pos < len` kept)
                    let (p, g) = (get(&m, "HOSTB", q, "pos"), get(&m, "HOSTB", q, "gap"));
                    if g == F::ZERO {
                        continue;
                    }
                    put(&mut m, "HOSTB", q, "pos", p + one);
                    put(&mut m, "HOSTB", q, "gap", g - one);
                } else {
                    let x = get(&m, "HOSTB", q, c);
                    put(&mut m, "HOSTB", q, c, x + F::from_u32(d));
                }
                cases.push((format!("HOSTB[row {q}] write byte (ts {}): {c} changed", ts.as_canonical_u32()), m));
            }
            // a write row turned into a request (read) row: consumes the NEW byte at `mtp`
            let mut m = s.mats.clone();
            put(&mut m, "HOSTB", q, "dir", F::ZERO);
            cases.push((format!("HOSTB[row {q}] write row relabelled as a read (dir 1 -> 0)"), m));
            // the pre-fix shape: the call's write group deactivated (and HOST's key multiplicity `nk`
            // lowered to match, so bus 214 stays balanced): its writes never reach memory
            let mut m = s.mats.clone();
            let mut n = 0u32;
            for p in 0..nb {
                if wr(&s.mats, p) && get(&s.mats, "HOSTB", p, "ts") == ts {
                    put(&mut m, "HOSTB", p, "act", F::ZERO);
                    n += 1;
                }
            }
            if let Some(h) = (0..rows(&m, "HOST")).find(|&h| get(&m, "HOST", h, "act") == one && get(&m, "HOST", h, "ts") == ts) {
                let nk = get(&m, "HOST", h, "nk");
                put(&mut m, "HOST", h, "nk", nk - F::from_u32(n));
            }
            cases.push((format!("HOSTB write group at ts {} dropped ({n} rows, act = 0): the old gap", ts.as_canonical_u32()), m));
            for (name, mut m) in cases {
                seg::recount(spec, &mut m, &s.pubs);
                out.push((name, m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
            }
        }
    }
    // (h3) a foreign HOSTB response group in a padding row: `dir = 1`, `reg = 0`, one byte, its own
    // group; its bus-210 pair cancels, no CH traffic, the BYTE/R16 multiplicities are recounted
    let hb = ti("HOSTB");
    if let Some(r) = (0..rows(&s.mats, "HOSTB")).rev().find(|&r| get(&s.mats, "HOSTB", r, "act") == F::ZERO) {
        let mut m = s.mats.clone();
        let w = m[hb].width;
        for x in m[hb].values[r * w..(r + 1) * w].iter_mut() {
            *x = F::ZERO;
        }
        for (c, v) in [("act", 1u32), ("dir", 1), ("f", 1), ("len", 1), ("ts", 7), ("hid", 999)] {
            put(&mut m, "HOSTB", r, c, F::from_u32(v));
        }
        seg::recount(spec, &mut m, &s.pubs);
        out.push(("HOSTB foreign response group (ts 7, hid 999) in a padding row".into(), m, s.pubs.clone(), s.comps.clone(), s.pubs.clone()));
    }
    out
}

/// Tampers of `wasmBaseSegAirG`'s new parts (E2E M4c): the memory size across the cut (public
/// `nblk`/`D` and SEGG's size message), grown blocks (MEMBG), old blocks above 64 MiB (MEMBH), the
/// lift root after a depth change (SEGG), MEMG's grow rows.
fn tampers_g(spec: &AirSpec, s: &SegInst) -> Vec<Case> {
    let mut out: Vec<Case> = vec![];
    let one = F::ONE;
    let zero = F::ZERO;
    let tab = |n: &str| spec.index(n);
    let get = |t: &str, r: usize, c: &str| {
        let i = tab(t);
        s.mats[i].values[r * s.mats[i].width + spec.tables[i].col(c)]
    };
    let height = |t: &str| {
        let i = tab(t);
        s.mats[i].values.len() / s.mats[i].width
    };
    let edit = |edits: &[(&str, usize, &str, F)]| {
        let mut m = s.mats.clone();
        for &(t, r, c, v) in edits {
            let i = tab(t);
            let w = m[i].width;
            m[i].values[r * w + spec.tables[i].col(c)] = v;
        }
        m
    };
    let mut push = |name: String, m: Vec<RowMajorMatrix<F>>, pubs: Vec<F>| {
        out.push((name, m, pubs.clone(), s.comps.clone(), pubs));
    };
    let f64_ = |x: u64| F::from_u64(x);
    // (1) the public geometry, rows honest: the proof must not verify against the forged statement
    for (name, idx, d) in [("pub nblk_out+64 (forged out-size)", seg::PUB_NBLK_OUT, 64u64), ("pub nblk_in+64 (forged in-size)", seg::PUB_NBLK_IN, 64),
        ("pub D_out+1", seg::PUB_DEPTH, 1), ("pub D_in+1", seg::PUB_DEPTH_IN, 1), ("pub MEMB bound (104)-1", seg::PUB_NBLK, F::NEG_ONE.as_canonical_u32() as u64)] {
        let mut p = s.pubs.clone();
        p[idx] += f64_(d);
        push(format!("{name} (rows honest)"), s.mats.clone(), p);
    }
    // (2) forged size with consistent public values: SEGG's size message no longer matches MEMG's
    {
        let mut p = s.pubs.clone();
        p[seg::PUB_NBLK_OUT] += f64_(64);
        push("SEGG pout+1 with pub nblk_out+64 (forged final size)".into(), edit(&[("SEGG", 0, "pout", get("SEGG", 0, "pout") + one)]), p);
        let mut p = s.pubs.clone();
        p[seg::PUB_NBLK_IN] += f64_(64);
        push("SEGG pin+1 with pub nblk_in+64 (forged initial size)".into(), edit(&[("SEGG", 0, "pin", get("SEGG", 0, "pin") + one)]), p);
        push("SEGG tz+1 (final size message time)".into(), edit(&[("SEGG", 0, "tz", get("SEGG", 0, "tz") + one)]), s.pubs.clone());
    }
    // (3) the lift root after a depth change
    if get("SEGG", 0, "lift") == one {
        push("SEGG lift root pn0+1 (forged root after the depth change)".into(), edit(&[("SEGG", 0, "pn0", get("SEGG", 0, "pn0") + one)]), s.pubs.clone());
        push("SEGG lift=0 (depth change without the lift root)".into(), edit(&[("SEGG", 0, "lift", zero)]), s.pubs.clone());
        push("SEGG old left child oL0+1 (old root not the in-root)".into(), edit(&[("SEGG", 0, "oL0", get("SEGG", 0, "oL0") + one)]), s.pubs.clone());
        for side in ["L", "R"] {
            let nd = format!("nd{side}");
            let n0 = format!("n{side}0");
            if get("SEGG", 0, &nd) == one {
                push(format!("SEGG touched child {side} marked untouched"), edit(&[("SEGG", 0, &nd, zero)]), s.pubs.clone());
            } else {
                push(format!("SEGG untouched child {side} stub n{side}0+1"), edit(&[("SEGG", 0, &n0, get("SEGG", 0, &n0) + one)]), s.pubs.clone());
            }
        }
        // the lift claimed with the old right subtree forged (a nonzero grown half): the right
        // child's MPATH node row with its old output changed consistently is rejected by SEGG's
        // constant `Z_16` on bus 17
        let mi = tab("MPATH");
        let d_in = s.pubs[seg::PUB_DEPTH_IN];
        if let Some(r) = (0..height("MPATH")).find(|&r| get("MPATH", r, "act") == one && get("MPATH", r, "lvl") == d_in && get("MPATH", r, "idx") == one) {
            let _ = mi;
            push("MPATH node (D_in, 1) old digest po0+1 (old right subtree not zero)".into(), edit(&[("MPATH", r, "po0", get("MPATH", r, "po0") + one)]), s.pubs.clone());
        }
    }
    // (4) grown blocks
    if let Some(r) = (0..height("MEMBG")).find(|&r| get("MEMBG", r, "p0") == one) {
        let tg = get("MEMBG", r, "tg");
        push("MEMBG out byte bo3+1 (grown content forged)".into(), edit(&[("MEMBG", r, "bo3", get("MEMBG", r, "bo3") + one)]), s.pubs.clone());
        let mut e: Vec<(&str, usize, &str, F)> = vec![];
        for k in 0..9 {
            e.push(("MEMBG", r + k, "tg", tg - one));
        }
        push("MEMBG tg-1 on the whole block (zero bytes before the grow)".into(), edit(&e), s.pubs.clone());
        let t_in = s.pubs[seg::PUB_T_IN];
        let mut e: Vec<(&str, usize, &str, F)> = vec![];
        for k in 0..9 {
            e.push(("MEMBG", r + k, "tg", t_in));
        }
        push("MEMBG tg=t_in (grown block present at the segment start)".into(), edit(&e), s.pubs.clone());
        push("MEMBG gold+1 on the padding row".into(), edit(&[("MEMBG", r + 8, "gold", get("MEMBG", r + 8, "gold") + one)]), s.pubs.clone());
        let mut e: Vec<(&str, usize, &str, F)> = vec![];
        for k in 0..9 {
            e.push(("MEMBG", r + k, "blk", get("MEMBG", r + k, "blk") + one));
        }
        push("MEMBG blk+1 on the whole block".into(), edit(&e), s.pubs.clone());
        push("MEMBG out-leaf limb hoO0+1 (padding row)".into(), edit(&[("MEMBG", r + 8, "hoO0", get("MEMBG", r + 8, "hoO0") + one)]), s.pubs.clone());
        let mut e: Vec<(&str, usize, &str, F)> = vec![];
        for k in 0..9 {
            e.push(("MEMBG", r + k, "act", zero));
            e.push(("MEMBG", r + k, &["p0", "p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"][k], zero));
        }
        push("MEMBG block dropped (rows inactive)".into(), edit(&e), s.pubs.clone());
        // the multiproof receives the grown leaf with a nonzero old digest
        let blk = get("MEMBG", r + 8, "blk");
        for (sbit, side) in [(zero, "L"), (one, "R")] {
            let lf = format!("lf{side}");
            if let Some(mr) = (0..height("MPATH")).find(|&x| get("MPATH", x, &lf) == one && get("MPATH", x, "idx") * F::from_u32(2) + sbit == blk) {
                let o0 = format!("o{side}0");
                push(format!("MPATH grown leaf {side} with old digest o{side}0+1 (old leaf not zleaf)"), edit(&[("MPATH", mr, &o0, get("MPATH", mr, &o0) + one)]), s.pubs.clone());
            }
        }
    }
    // (5) old blocks above 64 MiB
    if let Some(r) = (0..height("MEMBH")).find(|&r| get("MEMBH", r, "p0") == one) {
        let mut e: Vec<(&str, usize, &str, F)> = vec![];
        for k in 0..9 {
            e.push(("MEMBH", r + k, "blk", get("MEMBH", r + k, "blk") + one));
        }
        push("MEMBH blk+1 on the whole block".into(), edit(&e), s.pubs.clone());
        push("MEMBH in-byte bi7+1".into(), edit(&[("MEMBH", r, "bi7", get("MEMBH", r, "bi7") + one)]), s.pubs.clone());
    }
    // (6) MEMG
    if let Some(r) = (0..height("MEMG")).find(|&r| get("MEMG", r, "f_grow") == one && get("MEMG", r, "ok") == one) {
        push("MEMG grow gm+1".into(), edit(&[("MEMG", r, "gm", get("MEMG", r, "gm") + one)]), s.pubs.clone());
        push("MEMG grow old+1".into(), edit(&[("MEMG", r, "old", get("MEMG", r, "old") + one)]), s.pubs.clone());
        push("MEMG grow n0+1, d-1 (grow by one more page)".into(),
            edit(&[("MEMG", r, "n0", get("MEMG", r, "n0") + one), ("MEMG", r, "d", get("MEMG", r, "d") - one)]), s.pubs.clone());
        push("MEMG grow tz+1 (size message time)".into(), edit(&[("MEMG", r, "tz", get("MEMG", r, "tz") + one)]), s.pubs.clone());
    }
    if let Some(r) = (0..height("MEMG")).find(|&r| get("MEMG", r, "f_size") == one) {
        push("MEMG memory.size old+1".into(), edit(&[("MEMG", r, "old", get("MEMG", r, "old") + one)]), s.pubs.clone());
    }
    out
}

/// Tampers of the multiproof MPATH (`wasmBaseSegAirMP`).  Where a case would also break the chip
/// interface by itself (a duplicated row), the compressions are duplicated too, so only the
/// node/leaf/root buses or the row constraints can reject it.
fn tampers_mp(spec: &AirSpec, s: &SegInst) -> Vec<Case> {
    let mut out: Vec<Case> = vec![];
    let ti = spec.index("MPATH");
    let t = &spec.tables[ti];
    let w = s.mats[ti].width;
    let h = s.mats[ti].values.len() / w;
    let col = |c: &str| t.col(c);
    let get = |r: usize, c: &str| s.mats[ti].values[r * w + col(c)];
    let one = F::ONE;
    let zero = F::ZERO;
    let find = |p: &dyn Fn(usize) -> bool| (0..h).find(|&r| get(r, "act") == one && p(r));
    let edit = |edits: &[(usize, &str, F)]| {
        let mut m = s.mats.clone();
        for &(r, c, v) in edits {
            m[ti].values[r * w + col(c)] = v;
        }
        m
    };
    let mut push = |name: String, m: Vec<RowMajorMatrix<F>>, comps: Vec<s384::reference::Comp>| {
        out.push((name, m, s.pubs.clone(), comps, s.pubs.clone()));
    };
    let non_root = find(&|r| get(r, "top") == zero);
    let root = find(&|r| get(r, "top") == one);
    // node digest limbs (old output, new output), position, level of a non-root node
    if let Some(r) = non_root {
        for c in ["po0", "pn5"] {
            push(format!("MPATH-MP node digest {c}+1 (non-root)"), edit(&[(r, c, get(r, c) + one)]), s.comps.clone());
        }
        push("MPATH-MP idx+1".into(), edit(&[(r, "idx", get(r, "idx") + one)]), s.comps.clone());
        push("MPATH-MP lvl+1".into(), edit(&[(r, "lvl", get(r, "lvl") + one)]), s.comps.clone());
        // lvl+1 with consistent level bits: only the node bus can reject it
        {
            let u = get(r, "lvl").as_canonical_u32() as usize + 1;
            let d = s.pubs[seg::PUB_DEPTH].as_canonical_u32() as usize;
            let names: Vec<(String, F)> = (0..5)
                .flat_map(|i| [(format!("a{i}"), F::from_u32(((u - 1) >> i) as u32 & 1)), (format!("b{i}"), F::from_u32((d.saturating_sub(u) >> i) as u32 & 1))])
                .collect();
            let mut e: Vec<(usize, &str, F)> = names.iter().map(|(n, v)| (r, n.as_str(), *v)).collect();
            e.push((r, "lvl", F::from_u32(u as u32)));
            push("MPATH-MP lvl+1 (level bits consistent)".into(), edit(&e), s.comps.clone());
        }
        push("MPATH-MP level bit a0 flipped".into(), edit(&[(r, "a0", one - get(r, "a0"))]), s.comps.clone());
        // a duplicated node: a copy of the row in a padding row, with its own (duplicated) compressions
        {
            let mut m = s.mats.clone();
            let mut comps = s.comps.clone();
            // no padding row: double the table with zero rows (still a power of two)
            let pad = match (0..h).find(|&p| get(p, "act") == zero) {
                Some(p) => p,
                None => {
                    m[ti].values.extend(std::iter::repeat_n(F::ZERO, h * w));
                    h
                }
            };
            for c in 0..w {
                m[ti].values[pad * w + c] = m[ti].values[r * w + c];
            }
            for cc in ["cidO", "cidN"] {
                if cc == "cidN" && get(r, "ro") == one {
                    continue;
                }
                let k = get(r, cc).as_canonical_u32() as usize / 128;
                m[ti].values[pad * w + col(cc)] = F::from_u32((comps.len() * 128) as u32);
                comps.push(s384::reference::Comp { h: s.comps[k].h, block: s.comps[k].block });
            }
            push("MPATH-MP duplicated node (own compressions)".into(), m, comps);
        }
    }
    if let Some(r) = root {
        push("MPATH-MP root old limb po0+1".into(), edit(&[(r, "po0", get(r, "po0") + one)]), s.comps.clone());
        push("MPATH-MP root new limb pn3+1".into(), edit(&[(r, "pn3", get(r, "pn3") + one)]), s.comps.clone());
        push("MPATH-MP root flag cleared (top=0)".into(), edit(&[(r, "top", zero)]), s.comps.clone());
    }
    // child flags: touched -> untouched (new := old so the row constraint holds), leaf <-> node
    for side in ["L", "R"] {
        let (lf, nd, o0, n0) = (format!("lf{side}"), format!("nd{side}"), format!("o{side}0"), format!("n{side}0"));
        if let Some(r) = find(&|r| get(r, &lf) == one) {
            push(format!("MPATH-MP touched leaf {side} marked untouched"), edit(&[(r, &lf, zero), (r, &n0, get(r, &o0))]), s.comps.clone());
            push(format!("MPATH-MP touched leaf {side} received as a node"), edit(&[(r, &lf, zero), (r, &nd, one)]), s.comps.clone());
        }
        if let Some(r) = find(&|r| get(r, &nd) == one) {
            push(format!("MPATH-MP touched node {side} marked untouched"), edit(&[(r, &nd, zero), (r, &n0, get(r, &o0))]), s.comps.clone());
        }
        if let Some(r) = find(&|r| get(r, &lf) == zero && get(r, &nd) == zero) {
            push(format!("MPATH-MP untouched {side} marked touched (node)"), edit(&[(r, &nd, one)]), s.comps.clone());
            let tag = if get(r, "lvl") == one { "" } else { " at lvl>1" };
            push(format!("MPATH-MP untouched {side} marked touched (leaf){tag}"), edit(&[(r, &lf, one)]), s.comps.clone());
            // the sibling (witness) digest changed in both trees
            push(format!("MPATH-MP sibling {side} limb+1 (old and new)"), edit(&[(r, &o0, get(r, &o0) + one), (r, &n0, get(r, &n0) + one)]), s.comps.clone());
        }
    }
    // a read-only node with a child new ≠ old
    if let Some(r) = find(&|r| get(r, "ro") == one) {
        push("MPATH-MP read-only node with nL0 != oL0".into(), edit(&[(r, "nL0", get(r, "nL0") + one)]), s.comps.clone());
    }
    // a changed node claimed read-only (new compression skipped, pn := po)
    if let Some(r) = find(&|r| get(r, "ro") == zero) {
        let mut e: Vec<(usize, String, F)> = vec![(r, "ro".into(), one), (r, "cidN".into(), zero)];
        for l in 0..18 {
            e.push((r, format!("pn{l}"), get(r, &format!("po{l}"))));
        }
        let er: Vec<(usize, &str, F)> = e.iter().map(|(a, b, c)| (*a, b.as_str(), *c)).collect();
        push("MPATH-MP changed node claimed read-only (pn := po)".into(), edit(&er), s.comps.clone());
    }
    // a read-only MEMB block with a new leaf != old, consistently on MEMB's message and the node row
    {
        let mi = spec.index("MEMB");
        let mt = &spec.tables[mi];
        let mw = s.mats[mi].width;
        let mh = s.mats[mi].values.len() / mw;
        let mg = |r: usize, c: &str| s.mats[mi].values[r * mw + mt.col(c)];
        if let Some(mr) = (0..mh).find(|&r| mg(r, "p8") == one && mg(r, "ro") == one) {
            let blk = mg(mr, "blk");
            for (sbit, side) in [(zero, "L"), (one, "R")] {
                let lf = format!("lf{side}");
                if let Some(r) = find(&|r| get(r, &lf) == one && get(r, "idx") * F::from_u32(2) + sbit == blk) {
                    let n0 = format!("n{side}0");
                    let mut m = edit(&[(r, &n0, get(r, &n0) + one), (r, "ro", zero)]);
                    m[mi].values[mr * mw + mt.col("hoO0")] += one;
                    push("MEMB read-only block with new leaf != old (MEMB message + node row)".into(), m, s.comps.clone());
                }
            }
        }
    }
    out
}

// ------------------------------------------------------------------------------------------
// A-T1: pinned-shape segment templates (aggregation-tree leaves, plan §5.0.1.4 blocker 4)
// ------------------------------------------------------------------------------------------

/// The table heights of one built segment, by table name (`SHA512` = the chip's main trace).
fn seg_heights(spec: &AirSpec, s: &SegInst) -> std::collections::BTreeMap<String, usize> {
    let mut h: std::collections::BTreeMap<String, usize> =
        spec.tables.iter().zip(&s.mats).map(|(t, m)| (t.name.clone(), m.values.len() / m.width)).collect();
    h.insert("SHA512".into(), seg::tmpl_h("SHA512", s384::trace::main_height(s.comps.len())));
    h
}

/// `segtemplate <seg_air> <m2_air> (<prep> <K>)+`: the per-table maximum height over every segment
/// of every listed call (each cut every `K` steps), as a template `heights` object, plus the stacked
/// geometry the template needs (`n_stack`, `w_stack` by the same rule as `params_for`).
pub fn cmd_segtemplate(a: &[String]) {
    crate::set_levers();
    let (seg_air, m2_air) = (load(&a[0]), load(&a[1]));
    let mut maxh: std::collections::BTreeMap<String, usize> = Default::default();
    let mut nseg = 0;
    for pk in a[2..].chunks(2) {
        let k: u64 = pk[1].parse().unwrap();
        let (_prep, _g, segs) = segments(&seg_air, &m2_air, &pk[0], k);
        for s in segs.iter() {
            for (n, h) in seg_heights(&seg_air, s) {
                let e = maxh.entry(n).or_default();
                *e = (*e).max(h);
            }
            nseg += 1;
        }
    }
    let total: usize = seg_air.tables.iter().map(|t| maxh[&t.name] * t.cols.len()).sum::<usize>()
        + maxh["SHA512"] * s384::air::WIDTH + 128 * s384::air::T_WIDTH;
    let tallest = *maxh.values().max().unwrap();
    let n_stack = [14usize, 18, 22]
        .into_iter()
        .find(|&n| (1usize << (n + 2)) >= tallest && total.div_ceil(1 << (n + 2)) + 4 <= 24)
        .unwrap_or(22);
    let w_stack = (total.div_ceil(1 << (n_stack + 2)) + 4).max(8);
    println!("TEMPLATE_SEGMENTS {nseg} cells {total} tallest {tallest} n_stack {n_stack} w_stack {w_stack}");
    println!("{}", serde_json::json!({ "n_stack": n_stack, "w_stack": w_stack, "heights": maxh }));
}

/// A template file: the pinned geometry and per-table heights of one segment template.
pub(crate) struct Template {
    pub(crate) n_stack: usize,
    pub(crate) w_stack: usize,
    pub(crate) log_blowup: usize,
    pub(crate) pow: usize,
    pub(crate) certs: String,
    pub(crate) exclusions: String,
    pub(crate) heights: std::collections::HashMap<String, usize>,
    pub(crate) raw: serde_json::Value,
}
pub(crate) fn read_template(path: &str) -> Template {
    let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let u = |k: &str| v[k].as_u64().unwrap_or_else(|| panic!("template: {k}")) as usize;
    let s = |k: &str| v[k].as_str().unwrap_or_else(|| panic!("template: {k}")).to_string();
    let heights = v["heights"].as_object().unwrap().iter().map(|(k, h)| (k.clone(), h.as_u64().unwrap() as usize)).collect();
    Template { n_stack: u("n_stack"), w_stack: u("w_stack"), log_blowup: u("log_blowup"), pow: u("pow"),
        certs: s("certs"), exclusions: s("exclusions"), heights, raw: v.clone() }
}
pub(crate) fn template_params(t: &Template) -> SystemParams {
    crate::seg_base_params(t.n_stack, t.w_stack, t.log_blowup, t.pow, s384::air::DEGREE, &t.certs, &t.exclusions)
}

pub(crate) fn sha256_hex(b: &[u8]) -> String {
    use sha2::Digest;
    sha2::Sha256::digest(b).iter().map(|x| format!("{x:02x}")).collect()
}

pub(crate) type SegVk = openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sha384Config>;

/// Save a verifying key in the stack's envelope (`pq-chunk-e2e` `save_vk`: the extended-domain odd
/// factor, which upstream VK serde skips, kept explicitly).
pub(crate) fn save_vk(path: &std::path::Path, vk: &SegVk) -> Vec<u8> {
    let env = serde_json::json!({ "domain_odd_factor": vk.inner.params.whir.domain_odd_factor, "vk": vk });
    let b = serde_json::to_vec(&env).unwrap();
    std::fs::write(path, &b).unwrap();
    b
}
pub(crate) fn read_vk(path: &std::path::Path) -> SegVk {
    let mut v: serde_json::Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let odd = v["domain_odd_factor"].as_u64().unwrap() as usize;
    let mut vk: SegVk = serde_json::from_value(v["vk"].take()).unwrap();
    vk.inner.params.whir.domain_odd_factor = odd;
    vk
}

/// A-T2: the prover-side tight-height floor that commits every common main at its full height:
/// `(common-main width, log height, height)` per trace of the proving context.
pub(crate) fn full_tight_floor(pc: &ProvingContext<CpuColMajorBackend<Sha384Config>>) -> Vec<(usize, usize, usize)> {
    use openvm_stark_backend::prover::MatrixDimensions;
    pc.common_main_traces()
        .map(|(_, m)| (m.width(), m.height().trailing_zeros() as usize, m.height()))
        .collect()
}

/// A-T2: the pinned `(log_height, tight_height)` of every AIR of a template, in vk order: each JSON
/// table at its template height, the SHA-512 chip's main trace at the template's `SHA512` height
/// and its table at 128 rows; the tight height is the full height (every table has common-main
/// columns; a trace below `2^l_skip` rows declares none).  This is a function of the template file
/// alone, so a template leaf's heights — program constants of lane D's leaf — are data independent.
fn template_heights(spec: &AirSpec, th: &std::collections::HashMap<String, usize>, l_skip: usize) -> Vec<(usize, Option<usize>)> {
    let mut hs: Vec<usize> = spec.tables.iter().map(|t| *th.get(&t.name).unwrap_or_else(|| panic!("template: no height for {}", t.name))).collect();
    hs.push(th["SHA512"]);
    hs.push(s384::air::ROWS);
    hs.iter()
        .map(|&h| {
            assert!(h.is_power_of_two(), "template height {h}");
            (h.trailing_zeros() as usize, (h >= 1 << l_skip).then_some(h))
        })
        .collect()
}

/// The `(log_height, tight_height)` per AIR a proof declares.
pub(crate) fn proof_heights(p: &openvm_stark_backend::proof::Proof<Sha384Config>) -> Vec<(usize, Option<usize>)> {
    p.trace_vdata.iter().map(|v| v.as_ref().map_or((usize::MAX, None), |v| (v.log_height, v.tight_height))).collect()
}

/// `segleaf <seg_air> <m2_air> <prep> <K> <template.json> <out_dir>`: prove every segment of the call
/// at the pinned template (every table padded to the template height; a segment that does not fit is
/// refused with `SEGFIT`), under the stack's base configuration (`seg_base_params`), with ONE
/// verifying key; save `SEG.vk.json`, `seg-<i>.proof` (the stack's proof codec), `seg-<i>.pubs.json`
/// and `manifest.json` (template, parameters, soundness, file hashes, per-segment boundaries).
pub fn cmd_segleaf(a: &[String]) {
    crate::set_levers();
    let (seg_air, m2_air) = (load(&a[0]), load(&a[1]));
    let k: u64 = a[3].parse().unwrap();
    let tp = read_template(&a[4]);
    let out = std::path::Path::new(&a[5]);
    std::fs::create_dir_all(out).unwrap();
    seg::TEMPLATE.set(tp.heights.clone()).expect("template set once");
    let (prep, g, segs) = segments(&seg_air, &m2_air, &a[2], k);
    let prm = template_params(&tp);
    let pinned = template_heights(&seg_air, &tp.heights, prm.l_skip);
    // the stack budget `stackRem` at a cut: the live space-5 message `[rem & 0xffff, rem >> 16]`
    let stack_rem = |c: &tracegen::CutSnap| -> Option<u64> {
        c.live.iter().find(|l| l.space == 5 && l.slot == 0).map(|l| l.v[0] | (l.v[1] << 16))
    };
    println!("PARAMS n_stack {} w_stack {} log_blowup {} pow {} degree {} (stack base configuration)",
        prm.n_stack, prm.w_stack, prm.log_blowup, tp.pow, prm.max_constraint_degree);
    let eng = Sha384RefEngine::new(prm);
    let airs = airs(&seg_air);
    let t = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!("KEYGEN {:.2}s; SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}",
        t.elapsed().as_secs_f64(), b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits);
    let vkb = save_vk(&out.join("SEG.vk.json"), &vk);
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let mut man = vec![];
    for (i, s) in segs.iter().enumerate() {
        report(&seg_air, i, s);
        let hs = seg_heights(&seg_air, s);
        for (n, h) in hs.iter() {
            if let Some(&th) = tp.heights.get(n) {
                assert_eq!(*h, th, "segment {i}: table {n} height {h} != template {th}");
            }
        }
        seg::precheck(&seg_air, &s.mats, &s.pubs, &s.comps).unwrap_or_else(|e| panic!("segment {i}: {e}"));
        let t = Instant::now();
        let pc = ctx(&eng, &seg_air, &s.mats, &s.pubs, &s.comps);
        // A-T2: pin the tight heights.  Every committed common main commits its full template
        // height (`stacked_pcs::set_tight_floor`, as lanes B and G do), so a segment's tight heights
        // are the template's, not the position of its last non-zero row.  Lane D's leaf program
        // takes the child's (log, tight) heights as constants: one leaf program per template.
        // `SEG_TIGHT_NATURAL=1` keeps the natural tight heights (the pre-A-T2 leaves; tamper input).
        let natural = std::env::var("SEG_TIGHT_NATURAL").is_ok_and(|v| v == "1");
        if !natural {
            openvm_stark_backend::prover::stacked_pcs::set_tight_floor(Some(full_tight_floor(&pc)));
        }
        let proof = eng.prove(&d_pk, pc).expect("prove");
        openvm_stark_backend::prover::stacked_pcs::set_tight_floor(None);
        if !natural {
            let got = proof_heights(&proof);
            assert_eq!(got, pinned, "segment {i}: proof heights are not the template's pinned heights");
        }
        let tp_s = t.elapsed().as_secs_f64();
        let mut pb = vec![];
        proof.encode(&mut pb).unwrap();
        std::fs::write(out.join(format!("seg-{i}.proof")), &pb).unwrap();
        let pubs: Vec<u32> = s.pubs.iter().map(|x| x.as_canonical_u32()).collect();
        // A-T1 (lane I's boundary digest): the WasmBnd fields beyond the 105 public values.
        // `code_root`/`func_root`: the proof's cached CODE/FUNC commitments (bound by the proof; the
        // 42-byte digest as 6 u64 words: five full words + a 16-bit last word). `fuel`: not in the AIR; the leaf rule is
        // `fuel_out = fuel_in - (t_out - t_in)` (one call-machine step per STATE time).
        // `stack_rem`: the honest value at each cut, from the trace's live budget message; **not
        // bound by a public value** (it is inside the ctx digest's cut view, `budMsg`), so a leaf must
        // not rely on it until the AIR exposes it.  `vm_ctx_digest`: not available (the remainder
        // `blank s` moves with `gas.g`; m6 §6, TmplWasm `RestOK`).
        let cc = |name: &str| proof.trace_vdata[seg_air.index(name)].as_ref().map(|v| v.cached_commitments[0].to_vec());
        // A-T5: `stackRem` and `gasLeft` of the out-record are public values (CUTO's budget row,
        // SEGB's gas gadget); a halting segment's out-record is the fin record `fbBnd (q, .fin r)`
        // (every counter 0, every digest `bdigest []` but `vmCtxDigest`), not the AIR's halted state.
        let pu = |i: usize| s.pubs[i].as_canonical_u32() as u64;
        let gas_out: u64 = (0..4).map(|k| pu(seg::PUB_GOUT + k) << (16 * k)).sum();
        let rop: u64 = (0..3).map(|k| pu(seg::PUB_ROP + k) << (8 * k)).sum();
        let rem_out = pu(seg::PUB_REM_LO) + 65536 * pu(seg::PUB_REM_HI);
        assert_eq!(rop as u128, prep.regular, "segment {i}: published R");
        let wf = serde_json::json!({
            "code_root_words": cc("CODE"), "func_root_words": cc("FUNC"),
            "fuel_rule": "fuel_out = fuel_in - (t_out - t_in)", "steps": s.b_out.t - s.b_in.t,
            "stack_rem_in_unbound": stack_rem(&g.cuts[i]), "stack_rem_out_unbound": stack_rem(&g.cuts[i + 1]),
            "stack_rem_out": rem_out, "gas_left_out": gas_out, "regular_op_cost": rop,
            "out_record": if s.halted == 0 { "air" } else { "fin" },
            "vm_ctx_digest": serde_json::Value::Null,
        });
        let pj = serde_json::to_vec(&serde_json::json!({ "segment": i, "halted": s.halted, "pubs": pubs, "wasm_fields": wf })).unwrap();
        std::fs::write(out.join(format!("seg-{i}.pubs.json")), &pj).unwrap();
        let t = Instant::now();
        eng.verify(&vk, &proof).expect("verify");
        let tv = t.elapsed().as_secs_f64();
        assert!(statement_ok(&eng, &seg_air, &proof, &s.pubs, &prep), "segment {i}: statement");
        println!("  LEAF {i}: {} B, prove {tp_s:.1}s, verify {:.0} ms, statement ok, peak_rss_kib {}",
            pb.len(), tv * 1000.0, crate::peak_rss_kib());
        man.push(serde_json::json!({ "segment": i, "t_in": s.b_in.t, "t_out": s.b_out.t, "halted": s.halted,
            "proof_bytes": pb.len(), "proof_sha256": sha256_hex(&pb), "pubs_sha256": sha256_hex(&pj),
            "prove_s": tp_s, "verify_ms": tv * 1000.0 }));
    }
    assert!(chain_ok(&segs), "boundary chain");
    let root = |m: RowMajorMatrix<F>| {
        let c = eng.device().commit(&[&ColMajorMatrix::from_row_major(&m)]).expect("root").0;
        format!("{c:?}")
    };
    let m = serde_json::json!({
        "template": tp.raw, "k": k, "segments": man, "vk_sha256": sha256_hex(&vkb),
        "soundness_bits": b.total_bits,
        "pinned_heights": pinned, "tight_heights": "pinned: full template height per AIR (A-T2)",
        "code_root": root(seg::pad_rep("CODE", &tracegen::code_matrix(&prep.records))),
        "func_root": root(seg::pad_rep("FUNC", &tracegen::func_matrix(&prep))),
    });
    std::fs::write(out.join("manifest.json"), serde_json::to_vec_pretty(&m).unwrap()).unwrap();
    println!("SEGLEAF OK {} segments at one template vk (sha256 {}), boundaries chain; saved to {}",
        segs.len(), sha256_hex(&vkb), out.display());
}

/// `segleafverify <seg_air> <out_dir> <n>`: reload `SEG.vk.json` and `seg-0..n-1.proof` from disk,
/// check the vk against the manifest's hash, verify each proof, check that its public values are the
/// saved ones and that consecutive segments chain (out-boundary of `i` = in-boundary of `i + 1`:
/// pc/t/S/sb/cid/S_seg/segb, ctx digest, memory root).
pub fn cmd_segleafverify(a: &[String]) {
    use openvm_stark_backend::codec::Decode;
    crate::set_levers();
    let spec = load(&a[0]);
    let out = std::path::Path::new(&a[1]);
    let n: usize = a[2].parse().unwrap();
    let man: serde_json::Value = serde_json::from_slice(&std::fs::read(out.join("manifest.json")).unwrap()).unwrap();
    let vkb = std::fs::read(out.join("SEG.vk.json")).unwrap();
    assert_eq!(sha256_hex(&vkb), man["vk_sha256"].as_str().unwrap(), "vk hash");
    let vk = read_vk(&out.join("SEG.vk.json"));
    let eng = Sha384RefEngine::new(vk.inner.params.clone());
    // A-T2: the template's pinned (log, tight) heights, recomputed from the manifest's template
    // heights (not read from a proof); every proof must declare exactly these
    let th: std::collections::HashMap<String, usize> = man["template"]["heights"].as_object().expect("template heights")
        .iter().map(|(k, h)| (k.clone(), h.as_u64().unwrap() as usize)).collect();
    let pinned = template_heights(&spec, &th, vk.inner.params.l_skip);
    let mut prev: Option<Vec<F>> = None;
    for i in 0..n {
        let pb = std::fs::read(out.join(format!("seg-{i}.proof"))).unwrap();
        let mut c = std::io::Cursor::new(&pb[..]);
        let proof = openvm_stark_backend::proof::Proof::<Sha384Config>::decode(&mut c).expect("proof codec");
        assert_eq!(c.position() as usize, pb.len(), "trailing proof bytes");
        let pj: serde_json::Value = serde_json::from_slice(&std::fs::read(out.join(format!("seg-{i}.pubs.json"))).unwrap()).unwrap();
        let pubs: Vec<F> = pj["pubs"].as_array().unwrap().iter().map(|x| F::from_u32(x.as_u64().unwrap() as u32)).collect();
        let t = Instant::now();
        eng.verify(&vk, &proof).unwrap_or_else(|e| panic!("segment {i}: verifier {e:?}"));
        let tv = t.elapsed().as_secs_f64();
        assert_eq!(proof_heights(&proof), pinned, "segment {i}: heights are not the template's pinned heights");
        let pv_ok = spec.tables.iter().enumerate().all(|(ti, t)| {
            let want: Vec<F> = if JsonAir::reads_pub(t) { pubs.clone() } else { vec![] };
            proof.public_values[ti] == want
        });
        assert!(pv_ok, "segment {i}: public values");
        // A-T5: only the last segment halts (status 1 / 2), and its out-record is the fin record
        let st = pubs[seg::PUB_STATUS].as_canonical_u32();
        assert!(if i + 1 == n { st == 1 || st == 2 } else { st == 0 }, "segment {i}: status {st}");
        let kind = pj["wasm_fields"]["out_record"].as_str().unwrap_or("air");
        assert_eq!(kind, if st == 0 { "air" } else { "fin" }, "segment {i}: out-record kind");
        // the published CODE/FUNC roots are the proof's own cached commitments
        for (name, key) in [("CODE", "code_root_words"), ("FUNC", "func_root_words")] {
            let want: Vec<u64> = proof.trace_vdata[spec.index(name)].as_ref().expect("cached").cached_commitments[0].to_vec();
            let got: Vec<u64> = pj["wasm_fields"][key].as_array().expect(key).iter().map(|x| x.as_u64().unwrap()).collect();
            assert_eq!(got, want, "segment {i}: published {name} root");
        }
        if let Some(p) = &prev {
            let ok = p[seg::PUB_PC_OUT..seg::PUB_PC_OUT + 10] == pubs[seg::PUB_PC_IN..seg::PUB_PC_IN + 10]
                && p[seg::PUB_CTX_OUT..seg::PUB_CTX_OUT + 18] == pubs[seg::PUB_CTX_IN..seg::PUB_CTX_IN + 18]
                && p[seg::PUB_MEM_OUT..seg::PUB_MEM_OUT + 18] == pubs[seg::PUB_MEM_IN..seg::PUB_MEM_IN + 18];
            assert!(ok, "segment {i}: boundary chain");
        }
        println!("  DISK {i}: {} B verified in {:.0} ms, heights = template's pinned (log, tight), public values = saved, chains", pb.len(), tv * 1000.0);
        prev = Some(pubs);
    }
    println!("SEGLEAFVERIFY OK {n} segments from disk under one vk");
}
