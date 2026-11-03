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

fn load(p: &str) -> AirSpec {
    AirSpec::parse(&std::fs::read_to_string(p).unwrap())
}

/// Trace the whole call once with cuts every `k` steps; build every segment.
pub fn segments(seg_air: &AirSpec, m2_air: &AirSpec, prep_path: &str, k: u64) -> (Prep, Gen, Vec<SegInst>) {
    let prep = Prep::parse(&std::fs::read_to_string(prep_path).unwrap());
    let cut_at: Vec<u64> = (1..).map(|i| i * k).take_while(|&t| t < prep.steps).collect();
    let t0 = Instant::now();
    let g = tracegen::generate_cuts(m2_air, &prep, &cut_at);
    assert_eq!(g.steps, prep.steps, "step count vs spec");
    println!("TRACE steps {} cuts {} tracegen {:.2}s", g.steps, cut_at.len(), t0.elapsed().as_secs_f64());
    let mut tree = Tree::initial(&prep);
    let mut out = vec![];
    for i in 0..g.cuts.len() - 1 {
        let t1 = Instant::now();
        let s = seg::build(seg_air, m2_air, &g, &prep, i, &mut tree);
        println!("SEGBUILD {i} {:.2}s", t1.elapsed().as_secs_f64());
        out.push(s);
    }
    (prep, g, out)
}

fn cells(s: &SegInst) -> (usize, usize) {
    let main: usize = s.mats.iter().map(|m| m.values.len()).sum();
    let h = s384::trace::main_height(s.comps.len());
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
    for (i, s) in segs.iter().enumerate() {
        report(&seg_air, i, s);
        let t = Instant::now();
        seg::precheck(&seg_air, &s.mats, &s.pubs, &s.comps).unwrap_or_else(|e| panic!("segment {i}: {e}"));
        println!("  PRECHECK OK ({:.2}s): every constraint on every row, every bus balanced incl. the chip's interface", t.elapsed().as_secs_f64());
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
    let h = s384::trace::main_height(comps.len());
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

fn proof_size(p: &openvm_stark_backend::proof::Proof<Sha384Config>) -> usize {
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
    let code = root(tracegen::code_matrix(&prep.records));
    let func = root(tracegen::func_matrix(prep));
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
        seg::precheck(&seg_air, &s.mats, &s.pubs, &s.comps).unwrap_or_else(|e| panic!("segment {i}: {e}"));
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
        ("pub cid_in", seg::PUB_CID_IN), ("pub sb_in", seg::PUB_SB_IN), ("pub halted", seg::PUB_STATUS)] {
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
    // (h3) a foreign HOSTB response group in a padding row: `dir = 1`, `reg = 0`, one byte, its own
    // group; its bus-210 pair cancels, no CH traffic, the BYTE/R16 multiplicities are recounted
    let hb = ti("HOSTB");
    if let Some(r) = (0..rows(&s.mats, "HOSTB")).rev().find(|&r| get(&s.mats, "HOSTB", r, "act") == F::ZERO) {
        let mut m = s.mats.clone();
        let w = m[hb].width;
        for x in m[hb].values[r * w..(r + 1) * w].iter_mut() {
            *x = F::ZERO;
        }
        for (c, v) in [("act", 1u32), ("dir", 1), ("f", 1), ("blen", 1), ("ts", 7), ("hid", 999)] {
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
