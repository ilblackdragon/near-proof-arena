//! Real D0a base proof -> bound NV recursion -> separately verified final packet.
//! Research protocol: cryptographic security and zero-knowledge masking are not established here.
mod perf_check;
mod profile;
mod zk_selftest;
#[path = "../../pq-state-port/src/main.rs"]
#[allow(dead_code)]
mod state;
use openvm_recursion_circuit::{
    nv::{
        circuit::{NvCircuit, check_statement_claim, natural_tight_heights, prove_level},
        vd::{self, VdSetup},
    },
    sha384::config::{Sha384Config as SC, Sha384CpuEngine},
};
use openvm_stark_backend::{
    StarkEngine, SystemParams,
    codec::{Decode, Encode},
    keygen::types::MultiStarkVerifyingKey,
    proof::Proof,
};
use p3_matrix::Matrix;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use std::{io::Cursor, path::Path};

#[derive(Serialize, Deserialize)]
struct Setup {
    version: u32,
    domain_odd_factor: usize,
    air_sha256: String,
    base_params: SystemParams,
    final_vk: MultiStarkVerifyingKey<SC>,
    program: Vec<[u32; 4]>,
    level: u32,
}
// Upstream skips the extended-domain factor in VK serde. Keep it explicitly.
#[derive(Serialize, Deserialize)]
struct SavedVk {
    domain_odd_factor: usize,
    vk: MultiStarkVerifyingKey<SC>,
}
fn save_vk(path: &Path, vk: &MultiStarkVerifyingKey<SC>) {
    let envelope = SavedVk {
        domain_odd_factor: vk.inner.params.whir.domain_odd_factor,
        vk: vk.clone(),
    };
    std::fs::write(path, serde_json::to_vec(&envelope).unwrap()).unwrap();
}
fn read_vk(path: &Path) -> MultiStarkVerifyingKey<SC> {
    let mut envelope: SavedVk = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    assert_eq!(envelope.domain_odd_factor, 15, "unsupported profile domain");
    envelope.vk.inner.params.whir.domain_odd_factor = envelope.domain_odd_factor;
    envelope.vk
}
type Ef = openvm_recursion_circuit::sha384::config::EF;
fn tape_eval() -> bool {
    openvm_recursion_circuit::nv::circuit::tape_eval_lever()
}
fn ef_words(x: Ef) -> [u32; 12] {
    use p3_field::PrimeField32;
    openvm_recursion_circuit::nv::builder::coeffs(x).map(|c| c.as_canonical_u32())
}
fn ef_of_words(w: [u32; 12]) -> Ef {
    assert!(w.iter().all(|&x| x < 0x7800_0001), "noncanonical extension coefficient");
    openvm_recursion_circuit::nv::builder::ef_from(w.map(p3_field::PrimeCharacteristicRing::from_u32))
}
/// The base proof's stacking point, recorded by its native verification on this thread.
fn base_point(vk: &MultiStarkVerifyingKey<SC>, p: &Proof<SC>) -> Vec<Ef> {
    let _ = openvm_stark_backend::verifier::take_last_stacking_point::<Ef>();
    Sha384CpuEngine::new(vk.inner.params.clone())
        .verify(vk, p)
        .expect("base reverify");
    openvm_stark_backend::verifier::take_last_stacking_point::<Ef>().expect("stacking point")
}
fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn save_proof(path: &Path, p: &Proof<SC>) -> usize {
    let mut b = vec![];
    p.encode(&mut b).unwrap();
    std::fs::write(path, &b).unwrap();
    b.len()
}
fn read_proof(path: &Path) -> Proof<SC> {
    let b = std::fs::read(path).unwrap();
    decode_proof(&b)
}
fn decode_proof(b: &[u8]) -> Proof<SC> {
    let mut c = Cursor::new(b);
    let p = Proof::decode(&mut c).expect("proof codec");
    assert_eq!(c.position() as usize, b.len(), "trailing proof bytes");
    p
}
/// Encoded size of each top-level section of a proof, plus the per-AIR split of the
/// `trace_vdata`/`public_values` vectors. Read-only: decodes an existing proof file, proves
/// nothing. Exists so proof-size deltas between two runs can be attributed to a section
/// instead of inferred from "same shape, different bytes".
fn proof_sections(p: &Proof<SC>) -> String {
    use openvm_stark_backend::codec::Encode;
    fn size<T: Encode>(x: &T) -> usize {
        let mut b = Vec::new();
        x.encode(&mut b).unwrap();
        b.len()
    }
    let lv = &p.whir_proof.levers;
    let (gkr, rel) = if lv.is_default() {
        (size(&p.gkr_proof), size(&p.batch_constraint_proof))
    } else {
        let (mut g, mut r) = (Vec::new(), Vec::new());
        p.gkr_proof.encode_levers(lv, &mut g).unwrap();
        p.batch_constraint_proof.encode_levers(&mut r).unwrap();
        (g.len(), r.len())
    };
    // trace_vdata carries per-AIR optional trace metadata; when heights differ between two
    // runs this is where the bytes move. Split "present" vs "absent" entries so an empty
    // AIR cannot masquerade as a size change.
    let vd_present = p.trace_vdata.iter().filter(|x| x.is_some()).count();
    let vd_bytes: Vec<usize> = p
        .trace_vdata
        .iter()
        .map(|x| match x {
            Some(v) => size(v),
            None => 0,
        })
        .collect();
    let pv_entries: Vec<usize> = p.public_values.iter().map(Vec::len).collect();
    // WHIR sub-split. Under `multiproof`, each round's Merkle openings are one canonical
    // batched multiproof whose digest count depends on which siblings the verifier can
    // recompute from other opened leaves — so this count is data-dependent even when the
    // query schedule and row counts are identical. That is the only place a byte delta can
    // hide once geometry is fixed, so it is printed explicitly.
    let w = &p.whir_proof;
    let init_digests: usize = w
        .initial_round_merkle_proofs
        .iter()
        .map(|g| g.iter().map(|mp| mp.len()).sum::<usize>())
        .sum();
    let later_digests: Vec<usize> = w
        .codeword_merkle_proofs
        .iter()
        .map(|r| r.iter().map(|mp| mp.len()).sum())
        .collect();
    let init_rows: usize = w
        .initial_round_opened_rows
        .iter()
        .map(|c| c.iter().map(|q| q.len()).sum::<usize>())
        .sum();
    // Per-round digest accounting. Under the `multiproof` lever each round holds exactly ONE
    // canonical batched multiproof, so a proof's digest arrays are lengths, not Merkle paths:
    // their values must NOT be multiplied by the query count. The count of digests actually
    // sent is what matters for bytes, and it is printed directly.
    let init_commits = w.initial_round_opened_rows.len();
    let init_q: Vec<usize> = w.initial_round_opened_rows.iter().map(|c| c.len()).collect();
    let later_q: Vec<usize> = w.codeword_opened_values.iter().map(|r| r.len()).collect();
    let init_shape: Vec<usize> = w.initial_round_merkle_proofs.iter().map(Vec::len).collect();
    let init_lens: Vec<Vec<usize>> = w
        .initial_round_merkle_proofs
        .iter()
        .map(|g| g.iter().map(|mp| mp.len()).collect())
        .collect();
    let later_lens: Vec<Vec<usize>> = w
        .codeword_merkle_proofs
        .iter()
        .map(|r| r.iter().map(|mp| mp.len()).collect())
        .collect();
    let init_all_digests: usize = init_lens.iter().flatten().sum();
    // The WHIR Merkle depth is NOT recoverable from these arrays under `multiproof` (they hold
    // one batched proof per round, not one path per query). It is printed by the prover as
    // `NV_QCOST ... nbits=` and used there as `depth = nbits + ceil_log2(domain_odd_factor)`.
    // Without it no structural upper bound on the digest count can be derived here, so none is
    // claimed: the earlier `worst_digests` field multiplied query counts by batched-proof
    // LENGTHS and over-estimated by ~32x. Removed rather than left to mislead.
    let codeword_vals: Vec<usize> = w.codeword_opened_values.iter().map(|r| r.len()).collect();
    format!(
        "total={} common_main_commit={} trace_vdata={} gkr={} relations={} stacking={} whir={} \
         vd_present={} vd_per_air={:?} pv_entries={:?} \
         whir_commits={} whir_init_rows={} whir_init_digests={} whir_later_queries={:?} \
         whir_later_digests={:?} whir_final_poly={} \
         whir_init_commits={} whir_init_queries={:?} whir_later_queries_n={:?} \
         whir_digest_count={} whir_bytes_overhead={} whir_init_all_digests={} \
         whir_init_shape={:?} whir_init_lens={:?} whir_later_lens={:?}",
        size(p),
        std::mem::size_of_val(&p.common_main_commit),
        size(&p.trace_vdata),
        gkr,
        rel,
        size(&p.stacking_proof),
        size(&p.whir_proof),
        vd_present,
        vd_bytes,
        pv_entries,
        w.initial_round_opened_rows.len(),
        init_rows,
        init_digests,
        codeword_vals,
        later_digests,
        w.final_poly.len(),
        init_commits,
        init_q,
        later_q,
        init_digests + later_digests.iter().sum::<usize>(),
        // Width-aware: 42 was hardcoded here and silently overstated the overhead at d != 42.
        size(&p.whir_proof)
            - openvm_recursion_circuit::sha384::config::sha_levers().digest_bytes
                * (init_digests + later_digests.iter().sum::<usize>()),
        init_all_digests,
        init_shape,
        init_lens,
        later_lens
    )
}
fn init() {
    // Must happen before any engine/codec is constructed, in this single-threaded main.
    // Every default here is a *fallback*: an explicit value already in the environment wins, so
    // the digest-width margin lever (`NEARPROOF_DIGEST_BYTES=41`) and the streaming switch stay
    // reachable from a shell. Before this, the hardcoded "42" silently overrode the caller.
    unsafe {
        for (k, v) in [
            ("PQD1_POW", "24"),
            ("NEARPROOF_DIGEST_BYTES", "42"),
            ("NEARPROOF_COSET_LEAF", "1"),
            ("NEARPROOF_TSTAR", "1"),
            ("NEARPROOF_CPU_FAST", "1"),
            ("NEARPROOF_STREAM_COMMIT", "1"),
            // e2e: bind the base's cached TAPE by its openings at the stacking point (L1 circuit),
            // so the verifier evaluates the public TAPE instead of recomputing its commitment.
            ("NEARPROOF_TAPE_EVAL", "1"),
            // e2e (E2E-D): PCS-level hiding of the base and FINAL commitments (profile::zk_lever)
            ("NEARPROOF_ZK", "1"),
        ] {
            if std::env::var_os(k).is_none() {
                std::env::set_var(k, v);
            }
        }
    }
}
fn base(air: &str, dump: &str, out: &Path, certs: &str, exclusions: &str) {
    std::fs::create_dir_all(out).unwrap();
    let (vk, p) = state::chunk_bridge::prove_base(air, dump, certs, exclusions);
    let claim = state::chunk_bridge::expected_claim(air, dump, vk.inner.params.clone());
    assert_eq!(p.public_values, claim.public_values);
    assert_eq!(
        p.trace_vdata
            .iter()
            .flatten()
            .flat_map(|v| v.cached_commitments.clone())
            .collect::<Vec<_>>(),
        claim.cached_roots
    );
    save_vk(&out.join("BASE.vk.json"), &vk);
    println!(
        "BASE_VERIFIED bytes={}",
        save_proof(&out.join("BASE.proof"), &p)
    );
    std::fs::copy(Path::new(dump).join("hint.bin"), out.join("hint.bin")).unwrap();
}
fn load_base(out: &Path) -> (MultiStarkVerifyingKey<SC>, Proof<SC>) {
    let vk = read_vk(&out.join("BASE.vk.json"));
    let p = read_proof(&out.join("BASE.proof"));
    Sha384CpuEngine::new(vk.inner.params.clone())
        .verify(&vk, &p)
        .expect("base reverify");
    (vk, p)
}
fn probe(out: &Path) {
    let (vk, p) = load_base(out);
    let mut circ = NvCircuit::new(vk.inner.params.k_whir(), 22, 1);
    circ.prog_log = 21;
    circ.program_part = true;
    let w = circ.program_words(&vk, &p);
    println!(
        "L1_PROBE program_rows={} min_log_rows={}",
        w.len(),
        w.len().next_power_of_two().trailing_zeros()
    );
}
fn chain(
    air: &str,
    public: &str,
    out: &Path,
    certs: &str,
    exclusions: &str,
    resume: u32,
    final_only: bool,
) {
    let (mut vk, mut p) = load_base(out);
    state::chunk_bridge::check_base_key(air, public, &vk);
    let base_params = vk.inner.params.clone();
    let root_claim = state::chunk_bridge::expected_claim(air, public, base_params.clone());
    assert_eq!(p.public_values, root_claim.public_values, "base public values");
    assert_eq!(
        p.trace_vdata
            .iter()
            .flatten()
            .flat_map(|v| v.cached_commitments.clone())
            .collect::<Vec<_>>(),
        root_claim.cached_roots,
        "base TAPE root"
    );
    // The statement the chain carries: with tape-eval, the TAPE enters through its openings at
    // the base stacking point (checked here against the base proof's own openings).
    let base_u = base_point(&vk, &p);
    let claim = if tape_eval() {
        let c = state::chunk_bridge::expected_claim_at(air, public, base_params.clone(), &base_u);
        let ys = &c.tape_point.as_ref().unwrap().1;
        assert!(
            p.stacking_proof.stacking_openings.iter().any(|o| o == ys),
            "public TAPE evaluation differs from the base proof's TAPE opening"
        );
        std::fs::write(
            out.join("BASE.u.json"),
            serde_json::to_vec(&base_u.iter().map(|&x| ef_words(x)).collect::<Vec<_>>()).unwrap(),
        )
        .unwrap();
        println!("TAPE_EVAL_OK u_len={} openings={}", base_u.len(), ys.len());
        c
    } else {
        root_claim
    };
    let parent = Sha384CpuEngine::new(profile::params(false, certs, exclusions));
    let final_engine = Sha384CpuEngine::new_final(profile::params(true, certs, exclusions));
    let mut circ = NvCircuit::new(vk.inner.params.k_whir(), 18, 1);
    circ.prog_log = 17;
    circ.program_part = true;
    let mut words = vec![];
    let mut root = None;
    let mut floor: Option<Vec<usize>> = None;
    assert!(
        !final_only || resume >= 2,
        "final replay requires an NV checkpoint"
    );
    let mut converged = final_only;
    let mut levels = if final_only { resume } else { 0 };
    // Checkpoints are local trusted prover state, never verifier inputs.
    if resume > 0 {
        assert!(resume < 10);
        vk = read_vk(&out.join(format!("L{resume}.vk.json")));
        p = read_proof(&out.join(format!("L{resume}.proof")));
        parent.verify(&vk, &p).expect("checkpoint proof");
        assert!(check_statement_claim(&p.public_values[0], &claim));
        let checkpoint: (Vec<[u32; 4]>, Option<(u32, [u64; 6])>, Option<Vec<usize>>) =
            serde_json::from_slice(
                &std::fs::read(out.join(format!("L{resume}.state.json"))).unwrap(),
            )
            .unwrap();
        words = checkpoint.0;
        circ.anchor = checkpoint.1;
        floor = checkpoint.2;
        root = Some(p.trace_vdata[0].as_ref().unwrap().cached_commitments[0]);
    }
    if final_only {
        // Trusted local replay of the converged checkpoint. The final program
        // equality and independent verifier checks below remain mandatory.
        circ.log_rows = 20;
        circ.prog_log = 18;
        circ.child_nv = true;
        circ.bind = true;
    }
    for level in (resume + 1..=10).filter(|_| !final_only) {
        // Program binding requires the same ALU domain at every recursive layer.
        // Tight heights still compress unused common-main rows.
        circ.log_rows = 20;
        circ.prog_log = if level == 1 { 20 } else { 18 };
        circ.child_nv = level >= 2;
        circ.bind = level >= 2;
        let mut by_bind = false;
        if level >= 2 {
            let a = circ.select_anchor(&vk, &p, level - 1, &words, root.unwrap());
            by_bind = a.0 != level - 1;
            circ.anchor = Some(a);
            let (mats, _) = circ.generate(&vk, &p);
            let nat = natural_tight_heights(&mats, 2);
            if !floor
                .as_ref()
                .is_some_and(|f| nat.iter().zip(f).all(|(n, f)| n <= f))
            {
                floor = Some(
                    nat.iter()
                        .zip(&mats)
                        .map(|(&n, m)| (n + n / 64).next_multiple_of(4).min(m.height()))
                        .collect(),
                );
            }
            circ.tight_floor = floor.clone();
            println!("L{level}_ANCHOR M={} bind={by_bind} floor={floor:?}", a.0);
        }
        let t = std::time::Instant::now();
        let (v, q, b, sh) = prove_level(&circ, &parent, &vk, &p);
        assert!(
            check_statement_claim(&q.public_values[0], &claim),
            "L{level} changed statement"
        );
        words = b.instrs.iter().map(|i| i.words()).collect();
        root = Some(q.trace_vdata[0].as_ref().unwrap().cached_commitments[0]);
        println!(
            "L{level}_VERIFIED rows={} shapes={sh:?} bytes={} seconds={:.2}",
            words.len(),
            save_proof(&out.join(format!("L{level}.proof")), &q),
            t.elapsed().as_secs_f64()
        );
        save_vk(&out.join(format!("L{level}.vk.json")), &v);
        std::fs::write(
            out.join(format!("L{level}.state.json")),
            serde_json::to_vec(&(&words, &circ.anchor, &floor)).unwrap(),
        )
        .unwrap();
        vk = v;
        p = q;
        levels = level;
        if level >= 2 && by_bind {
            converged = true;
            break;
        }
    }
    assert!(converged, "bound program did not converge; no final claim");
    let mut fc = circ.clone_shape();
    fc.program_part = false;
    fc.tight_floor = None;
    // [E2E-D] witness-guessing distinguisher: NEARPROOF_ZK_GUESS=DIR (FINAL.proof + SETUP.json of
    // a packet) tests this checkpoint's FINAL trace (the witness) against that proof and exits.
    if let Ok(dir) = std::env::var("NEARPROOF_ZK_GUESS") {
        zk_guess(&fc, &vk, &p, Path::new(&dir));
        return;
    }
    let final_started = std::time::Instant::now();
    println!("FINAL_PHASE start");
    let (fv, fp, b, _) = prove_level(&fc, &final_engine, &vk, &p);
    println!(
        "FINAL_PHASE proved_and_verified seconds={:.6}",
        final_started.elapsed().as_secs_f64()
    );
    let fw: Vec<_> = b.instrs.iter().map(|i| i.words()).collect();
    assert_eq!(fw, words, "FINAL program differs from child");
    let setup = Setup {
        version: if tape_eval() { 2 } else { 1 },
        domain_odd_factor: 15,
        air_sha256: hash(&std::fs::read(air).unwrap()),
        base_params,
        final_vk: fv,
        program: fw,
        level: levels + 1,
    };
    let vd = VdSetup {
        vk_final: setup.final_vk.clone(),
        program: setup.program.clone(),
        level: setup.level,
    };
    vd::verify_final_claim(&vd, &final_engine, &claim, &fp, false)
        .expect("final statement + pinned program");
    // Verify that the actual final artifact cannot be relabelled with a different statement.
    let mut wrong = claim.clone();
    match wrong.tape_point.as_mut() {
        Some((u, _)) => u[0] += <Ef as p3_field::PrimeCharacteristicRing>::ONE,
        None => wrong.cached_roots[0][0] ^= 1,
    }
    assert!(vd::verify_final_claim(&vd, &final_engine, &wrong, &fp, false).is_err());
    let mut bad_setup = vd.clone();
    bad_setup.program[0][0] ^= 1;
    assert!(vd::verify_final_claim(&bad_setup, &final_engine, &claim, &fp, false).is_err());
    println!("NEGATIVE_CONTROLS_OK changed_tape_root changed_program");
    let setup_bytes = serde_json::to_vec(&setup).unwrap();
    let setup_size = setup_bytes.len();
    let pin = hash(&setup_bytes);
    std::fs::write(out.join("SETUP.json"), setup_bytes).unwrap();
    std::fs::write(out.join("SETUP.sha256"), &pin).unwrap();
    let proof_bytes = save_proof(&out.join("FINAL.proof"), &fp);
    let hint = std::fs::read(out.join("hint.bin")).unwrap();
    let mut packet = if tape_eval() { b"NPQCH02\0".to_vec() } else { b"NPQCH01\0".to_vec() };
    packet.extend_from_slice(&(hint.len() as u64).to_le_bytes());
    packet.extend_from_slice(&hint);
    if tape_eval() {
        // v2: the base stacking point (public Fiat-Shamir randomness; bound by the statement)
        packet.extend_from_slice(&(base_u.len() as u32).to_le_bytes());
        for &x in &base_u {
            for w in ef_words(x) {
                packet.extend_from_slice(&w.to_le_bytes());
            }
        }
    }
    fp.encode(&mut packet).unwrap();
    std::fs::write(out.join("FINAL.bundle"), &packet).unwrap();
    let result = serde_json::json!({"scope":"D0a","trusted_setup_bytes":setup_size,"security_established":false,"zero_knowledge_established":false,"proof_bytes":proof_bytes,"hint_bytes":hint.len(),"bundle_bytes":packet.len(),"under_300000":packet.len()<300000,"setup_sha256":pin,"levels":levels+1,"tape_eval":tape_eval()});
    std::fs::write(
        out.join("RESULT.json"),
        serde_json::to_vec_pretty(&result).unwrap(),
    )
    .unwrap();
    println!("FINAL_VERIFIED {result}");
}
/// Bundle framing: (hint length, base stacking point for v2, offset of the encoded proof).
/// v1 = magic | u64 hint length | hint | proof; v2 adds u32 m | m x 12 u32 (the base point) before
/// the proof.
fn bundle_parts(packet: &[u8], v2: bool, base_n_stack: usize) -> (usize, Option<Vec<Ef>>, usize) {
    assert!(
        packet.len() >= 16 && &packet[..8] == if v2 { b"NPQCH02\0" } else { b"NPQCH01\0" },
        "bundle framing"
    );
    let n = usize::try_from(u64::from_le_bytes(packet[8..16].try_into().unwrap())).unwrap();
    assert!(n <= packet.len() - 16, "truncated hint");
    let mut body = 16 + n;
    let base_u: Option<Vec<Ef>> = v2.then(|| {
        assert!(packet.len() >= body + 4, "truncated stacking point");
        let m = u32::from_le_bytes(packet[body..body + 4].try_into().unwrap()) as usize;
        assert_eq!(m, base_n_stack + 1, "stacking point length");
        body += 4;
        assert!(packet.len() >= body + 48 * m, "truncated stacking point");
        let u = (0..m)
            .map(|i| {
                let o = body + 48 * i;
                ef_of_words(core::array::from_fn(|k| {
                    u32::from_le_bytes(packet[o + 4 * k..o + 4 * k + 4].try_into().unwrap())
                }))
            })
            .collect();
        body += 48 * m;
        u
    });
    (n, base_u, body)
}
fn verify(air: &str, claim_path: &str, helper: &str, setup_path: &str, pin: &str, bundle: &str) {
    let t_all = std::time::Instant::now();
    let mut lap = t_all;
    let mut phases: Vec<(&str, f64)> = vec![];
    let mut mark = |name: &'static str, phases: &mut Vec<(&str, f64)>| {
        phases.push((name, lap.elapsed().as_secs_f64() * 1e3));
        lap = std::time::Instant::now();
    };
    let setup_bytes = std::fs::read(setup_path).unwrap();
    assert_eq!(
        hash(&setup_bytes),
        pin,
        "untrusted setup: hash differs from operator's pin"
    );
    mark("setup_read_pin", &mut phases);
    let mut setup: Setup = serde_json::from_slice(&setup_bytes).unwrap();
    mark("setup_parse", &mut phases);
    assert_eq!(setup.domain_odd_factor, 15);
    setup.base_params.whir.domain_odd_factor = setup.domain_odd_factor;
    setup.final_vk.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
    assert!(setup.version == 1 || setup.version == 2, "setup version");
    let air_bytes = std::fs::read(air).unwrap();
    assert_eq!(hash(&air_bytes), setup.air_sha256, "AIR differs from pinned setup");
    let packet = std::fs::read(bundle).unwrap();
    let (n, base_u, body) = bundle_parts(&packet, setup.version == 2, setup.base_params.n_stack);
    mark("air_pin_bundle_read", &mut phases);
    // Only the AIR's public-input view is needed (numPub, pubSegs, maxPub, table count, each
    // table's pub bound): one streaming pass over the pinned AIR bytes.
    let air_pub = npudr::airpub::AirPublic::from_json_slice(&air_bytes).expect("air json");
    mark("air_parse", &mut phases);
    // `statepublic`, in process (the helper path argument is accepted for CLI compatibility and
    // ignored): recompute the public inputs/messages from the claim and the transmitted hint.
    let _ = helper;
    let public = public_data(&air_pub, &std::fs::read(claim_path).unwrap(), &packet[16..16 + n]);
    mark("statepublic", &mut phases);
    let expected = state::chunk_bridge::expected_claim_parsed(
        &air_pub.table_num_pub,
        &public,
        setup.base_params,
        base_u.as_deref(),
    );
    mark("expected_claim_tape", &mut phases);
    let fp = decode_proof(&packet[body..]);
    mark("proof_decode", &mut phases);
    let engine = Sha384CpuEngine::new_final(setup.final_vk.inner.params.clone());
    vd::verify_final_claim(
        &VdSetup {
            vk_final: setup.final_vk,
            program: setup.program,
            level: setup.level,
        },
        &engine,
        &expected,
        &fp,
        false,
    )
    .expect("final verifier");
    mark("final_verify", &mut phases);
    let total = t_all.elapsed().as_secs_f64() * 1e3;
    println!(
        "VERIFY_PROFILE_MS total={total:.2} {}",
        phases.iter().map(|(k, v)| format!("{k}={v:.2}")).collect::<Vec<_>>().join(" ")
    );
    println!(
        "INDEPENDENT_VERIFY_OK bundle_bytes={} under_300000={}",
        packet.len(),
        packet.len() < 300000
    );
}
/// The verifier-generated public data of a claim + transmitted hint (`statepublic`, in process).
/// A claim/hint the preparation rejects panics ("claim/hint rejected"), i.e. the packet is rejected.
fn public_data(
    air: &npudr::airpub::AirPublic,
    claim: &[u8],
    hint: &[u8],
) -> state::chunk_bridge::PublicData {
    let st = npudr::v3::statement::public_statement(air, claim, hint).expect("claim/hint rejected");
    state::chunk_bridge::PublicData::new(
        &st.pubs,
        st.msgs.iter().map(|(b, s, m)| (*b as u64, *s, m.as_slice())),
    )
}
/// Parity of the in-process claim preparation with the original file/subprocess path: the
/// `statepublic` executable writes pubs.bin/pubmsgs.json, the file-based `expected_claim(_at)`
/// (full classical AIR parse) reads them. The two `StatementClaim`s must be identical.
fn claim_parity(air: &str, claim_path: &str, helper: &str, setup_path: &str, bundle: &str) {
    let mut setup: Setup = serde_json::from_slice(&std::fs::read(setup_path).unwrap()).unwrap();
    setup.base_params.whir.domain_odd_factor = setup.domain_odd_factor;
    let packet = std::fs::read(bundle).unwrap();
    let (n, base_u, _) = bundle_parts(&packet, setup.version == 2, setup.base_params.n_stack);
    // reference: subprocess + files (the pre-in-process verifier path)
    let dir = tempfile::tempdir().unwrap();
    let hint = dir.path().join("hint.bin");
    std::fs::write(&hint, &packet[16..16 + n]).unwrap();
    let public = dir.path().join("public");
    assert!(
        std::process::Command::new(helper)
            .args([air, claim_path])
            .arg(&hint)
            .arg(&public)
            .status()
            .expect("statepublic")
            .success(),
        "claim/hint rejected"
    );
    let p = public.to_str().unwrap();
    let reference = match &base_u {
        Some(u) => state::chunk_bridge::expected_claim_at(air, p, setup.base_params.clone(), u),
        None => state::chunk_bridge::expected_claim(air, p, setup.base_params.clone()),
    };
    // in process
    let air_bytes = std::fs::read(air).unwrap();
    let fast = npudr::airpub::AirPublic::from_json_slice(&air_bytes).unwrap();
    let full = npudr::airpub::AirPublic::of(
        &npudr::air::Air::from_json(std::str::from_utf8(&air_bytes).unwrap()).unwrap(),
    );
    assert_eq!(fast.table_num_pub, full.table_num_pub, "pub bounds (streaming vs full parse)");
    assert_eq!(fast.table_num_pub, state::chunk_bridge::table_num_pub(air), "pub bounds (classical)");
    assert_eq!(
        (fast.num_tables, fast.air.num_pub, fast.air.max_pub, fast.air.v2, &fast.air.pub_segs),
        (full.num_tables, full.air.num_pub, full.air.max_pub, full.air.v2, &full.air.pub_segs),
        "AIR public view (streaming vs full parse)"
    );
    let public = public_data(&fast, &std::fs::read(claim_path).unwrap(), &packet[16..16 + n]);
    let claim = state::chunk_bridge::expected_claim_parsed(
        &fast.table_num_pub,
        &public,
        setup.base_params,
        base_u.as_deref(),
    );
    let (a, b) = (format!("{reference:?}"), format!("{claim:?}"));
    assert_eq!(a, b, "in-process claim differs from the statepublic/file path");
    println!(
        "CLAIM_PARITY_OK tape_eval={} public_values={} claim_debug_sha256={}",
        base_u.is_some(),
        claim.public_values.iter().map(Vec::len).sum::<usize>(),
        hash(a.as_bytes())
    );
}
/// Split timing of the verifier's stages on already-prepared public inputs (median of `reps`).
/// Measurement only; `verify` is the acceptance path.
fn verify_bench(air: &str, public: &str, setup_path: &str, bundle: &str, reps: usize) {
    let mut setup: Setup = serde_json::from_slice(&std::fs::read(setup_path).unwrap()).unwrap();
    setup.base_params.whir.domain_odd_factor = setup.domain_odd_factor;
    setup.final_vk.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
    let packet = std::fs::read(bundle).unwrap();
    let (_, base_u, body) = bundle_parts(&packet, setup.version == 2, setup.base_params.n_stack);
    let med = |mut v: Vec<f64>| {
        v.sort_by(|a, b| a.partial_cmp(b).unwrap());
        v[v.len() / 2]
    };
    let time = |f: &mut dyn FnMut()| {
        let t = std::time::Instant::now();
        f();
        t.elapsed().as_secs_f64() * 1e3
    };
    let (mut tc, mut td, mut tv, mut tp) = (vec![], vec![], vec![], vec![]);
    let mut claim = None;
    for _ in 0..reps {
        tc.push(time(&mut || {
            claim = Some(match &base_u {
                Some(u) => state::chunk_bridge::expected_claim_at(air, public, setup.base_params.clone(), u),
                None => state::chunk_bridge::expected_claim(air, public, setup.base_params.clone()),
            })
        }));
    }
    let claim = claim.unwrap();
    let mut fp = None;
    for _ in 0..reps {
        td.push(time(&mut || fp = Some(decode_proof(&packet[body..]))));
    }
    let fp = fp.unwrap();
    let engine = Sha384CpuEngine::new_final(setup.final_vk.inner.params.clone());
    let vd = VdSetup {
        vk_final: setup.final_vk.clone(),
        program: setup.program.clone(),
        level: setup.level,
    };
    for _ in 0..reps {
        tv.push(time(&mut || {
            engine.verify(&setup.final_vk, &fp).expect("final proof")
        }));
    }
    for _ in 0..reps {
        tp.push(time(&mut || {
            vd::check_final_program(&vd, &fp).expect("program")
        }));
    }
    let mut tf = vec![];
    for _ in 0..reps {
        tf.push(time(&mut || {
            vd::verify_final_claim(&vd, &engine, &claim, &fp, false).expect("final claim")
        }));
    }
    println!(
        "VERIFY_BENCH_MS threads={} reps={reps} expected_claim={:.2} decode={:.3} engine_verify={:.2} program_check_replay={:.2} verify_final_claim={:.2}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_default(),
        med(tc),
        med(td),
        med(tv),
        med(tp),
        med(tf)
    );
}
/// [E2E-D] Witness-guessing distinguisher. Given a FINAL proof and a candidate witness (the FINAL
/// trace generated from an L4 checkpoint), recompute every column opening the proof reveals —
/// the prismatic MLE of the candidate trace column (and its next-row rotation) at the batch point
/// `r` the verifier derives from the proof — and count how many equal the proof's values. Without
/// PIOP masking the true witness matches every opening (the proof identifies its witness); with
/// masking only the public columns (`zk_public_cols`, the pinned program) can match.
fn zk_guess(fc: &NvCircuit, vk: &MultiStarkVerifyingKey<SC>, p: &Proof<SC>, dir: &Path) {
    use openvm_stark_backend::poly_common::{eval_eq_uni, evals_eq_hypercube_serial};
    use p3_field::{PrimeCharacteristicRing, TwoAdicField};
    let mut setup: Setup = serde_json::from_slice(&std::fs::read(dir.join("SETUP.json")).unwrap()).unwrap();
    setup.final_vk.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
    let fp = read_proof(&dir.join("FINAL.proof"));
    let engine = Sha384CpuEngine::new_final(setup.final_vk.inner.params.clone());
    let r = {
        use openvm_stark_backend::StarkEngine;
        let mut t = engine.initial_transcript();
        openvm_stark_backend::verifier::verify_with_point(engine.config(), &setup.final_vk, &fp, &mut t).expect("final proof")
    };
    let (mats, _) = fc.generate(vk, p);
    let mvk = &setup.final_vk.inner;
    let l_skip = mvk.params.l_skip;
    let omega = openvm_recursion_circuit::sha384::config::F::two_adic_generator(l_skip);
    let mut order: Vec<usize> = (0..mvk.per_air.len()).filter(|&a| fp.trace_vdata[a].is_some()).collect();
    order.sort_by_key(|&a| (std::cmp::Reverse(fp.trace_vdata[a].as_ref().unwrap().log_height), a));
    let (mut tot, mut hit, mut tot_pub, mut hit_pub) = (0usize, 0usize, 0usize, 0usize);
    for (t, &air) in order.iter().enumerate() {
        let m = &mats[air];
        let h = m.height();
        let n = (h.trailing_zeros() as usize).saturating_sub(l_skip);
        assert_eq!(fp.trace_vdata[air].as_ref().unwrap().log_height, n + l_skip, "candidate trace shape");
        let lz: Vec<Ef> = (0..1usize << l_skip)
            .map(|z| eval_eq_uni(l_skip, r[0], Ef::from(omega.exp_u64(z as u64))))
            .collect();
        let eqy = evals_eq_hypercube_serial(&r[1..=n]);
        let w: Vec<Ef> = (0..h).map(|row| lz[row & ((1 << l_skip) - 1)] * eqy[row >> l_skip]).collect();
        let mask = mvk.per_air[air].params.opening_masks()[0].clone();
        let public = &mvk.per_air[air].params.zk_public_cols;
        let openings = openvm_stark_backend::proof::column_openings_by_mask(
            &fp.batch_constraint_proof.column_openings[t][0],
            &mask,
        );
        let width = m.width();
        let cols: Vec<(Ef, Ef)> = (0..width)
            .map(|c| {
                let mut plain = Ef::ZERO;
                let mut rot = Ef::ZERO;
                for row in 0..h {
                    plain += w[row] * m.values[row * width + c];
                    rot += w[row] * m.values[((row + 1) % h) * width + c];
                }
                (plain, rot)
            })
            .collect();
        for (c, ((pl, rt), &has_rot)) in cols.iter().zip(&mask).enumerate() {
            let (o, orot) = openings[c];
            // the pinned program columns of the NvAir are public in every mode
            let up = openvm_recursion_circuit::nv::uair::U_P;
            let is_pub = public.contains(&c) || (air == 0 && (up..up + 4).contains(&c));
            if is_pub {
                tot_pub += 1;
                hit_pub += (o == *pl) as usize;
            } else {
                tot += 1;
                hit += (o == *pl) as usize;
            }
            if has_rot {
                tot += 1;
                hit += (orot == *rt) as usize;
            }
        }
    }
    println!(
        "ZK_GUESS proof={} zk={} witness_openings_matched={hit}/{tot} public_column_openings_matched={hit_pub}/{tot_pub}",
        dir.display(),
        setup.final_vk.inner.params.whir.levers.zk
    );
}

/// [E2E-D] Hiding sanity check: field-by-field comparison of two proofs of the same statement.
/// Every proof field is flattened to its scalar leaves (field-element coefficients, digest bytes,
/// lengths); leaves are grouped by path with indices removed, and each group reports how many
/// leaves agree at the same position. A field that is a deterministic function of the witness
/// agrees everywhere when the two proofs share the witness and differ only in prover randomness;
/// a hidden field agrees only by chance (~1/p per base-field leaf). Shape (lengths) must agree.
/// Necessary, not sufficient, for zero knowledge.
fn zk_diff(a: &Path, b: &Path) {
    use std::collections::BTreeMap;
    fn walk(v: &serde_json::Value, path: &str, out: &mut Vec<(String, serde_json::Value)>) {
        match v {
            serde_json::Value::Object(m) => {
                for (k, x) in m {
                    walk(x, &format!("{path}.{k}"), out)
                }
            }
            serde_json::Value::Array(xs) => {
                out.push((format!("{path}#len"), serde_json::json!(xs.len())));
                for x in xs {
                    walk(x, &format!("{path}[]"), out)
                }
            }
            x => out.push((path.to_string(), x.clone())),
        }
    }
    let (pa, pb) = (read_proof(a), read_proof(b));
    let (mut la, mut lb) = (vec![], vec![]);
    walk(&serde_json::to_value(&pa).unwrap(), "", &mut la);
    walk(&serde_json::to_value(&pb).unwrap(), "", &mut lb);
    let mut stats: BTreeMap<String, (usize, usize, bool)> = BTreeMap::new();
    let mut ib = lb.iter().peekable();
    for (k, x) in &la {
        // walk order is identical while shapes agree; a shape difference shows up as a #len miss
        let same = match ib.next() {
            Some((kb, y)) if kb == k => x == y,
            _ => false,
        };
        let key = k.trim_end_matches("#len").to_string();
        let e = stats.entry(key).or_insert((0, 0, false));
        if k.ends_with("#len") {
            e.2 |= !same;
        } else {
            e.0 += 1;
            e.1 += same as usize;
        }
    }
    let mut leaking = 0;
    for (k, (n, eq, shape_diff)) in &stats {
        if *n == 0 {
            continue;
        }
        let verdict = if *shape_diff {
            "SHAPE_DIFFERS"
        } else if *eq == *n {
            leaking += 1;
            "IDENTICAL"
        } else if *eq * 1000 > *n {
            leaking += 1;
            "PARTLY_IDENTICAL"
        } else {
            "differs"
        };
        println!("ZK_DIFF {k} leaves={n} equal={eq} {verdict}");
    }
    println!("ZK_DIFF_SUMMARY groups={} identical_or_partly={leaking}", stats.len());
}
fn main() {
    init();
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(String::as_str) {
        Some("check-stream-parity") if a.len() == 2 => perf_check::run(),
        Some("base") if a.len() == 7 => base(&a[2], &a[3], Path::new(&a[4]), &a[5], &a[6]),
        Some("probe") if a.len() == 3 => probe(Path::new(&a[2])),
        Some("validate-base") if a.len() == 5 => {
            let (vk, _) = load_base(Path::new(&a[4]));
            state::chunk_bridge::check_base_key(&a[2], &a[3], &vk);
            println!("BASE_AIR_KEY_MATCH_OK");
        }
        Some("chain") if a.len() == 7 || a.len() == 8 => chain(
            &a[2],
            &a[3],
            Path::new(&a[4]),
            &a[5],
            &a[6],
            a.get(7).map(|s| s.parse().unwrap()).unwrap_or(0),
            false,
        ),
        Some("replay-final") if a.len() == 8 => chain(
            &a[2],
            &a[3],
            Path::new(&a[4]),
            &a[5],
            &a[6],
            a[7].parse().unwrap(),
            true,
        ),
        Some("verify") if a.len() == 8 => verify(&a[2], &a[3], &a[4], &a[5], &a[6], &a[7]),
        Some("claim-parity") if a.len() == 7 => claim_parity(&a[2], &a[3], &a[4], &a[5], &a[6]),
        Some("soundness") if a.len() >= 3 => {
            // Per-component soundness bits of each named vk (BASE/L*.vk.json or SETUP.json).
            for path in &a[2..] {
                let vk = if path.ends_with("SETUP.json") {
                    let mut s: Setup = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
                    s.final_vk.inner.params.whir.domain_odd_factor = s.domain_odd_factor;
                    s.final_vk
                } else {
                    read_vk(Path::new(path))
                };
                let c = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
                let w = &c.whir_details;
                println!(
                    "SOUNDNESS_BITS file={path} n_stack={} log_blowup={} queries={:?} logup={:.1} gkr_sumcheck={:.1} gkr_batching={:.1} zerocheck={:.1} constraint_batching={:.1} stacked_reduction={:.1} whir={:.1} total={:.1} whir_query={:.1} whir_proximity={:.1} whir_sumcheck={:.1} whir_fold={:.1} whir_ood={:.1} whir_gamma={:.1} whir_shift={:.1} whir_mu={:.1}",
                    vk.inner.params.n_stack,
                    vk.inner.params.log_blowup,
                    vk.inner.params.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
                    c.logup_bits, c.gkr_sumcheck_bits, c.gkr_batching_bits, c.zerocheck_sumcheck_bits,
                    c.constraint_batching_bits, c.stacked_reduction_bits, c.whir_bits, c.total_bits,
                    w.query_bits, w.proximity_gaps_bits, w.sumcheck_bits, w.fold_rbr_bits, w.ood_rbr_bits,
                    w.gamma_batching_bits, w.shift_rbr_bits, w.mu_batching_bits
                );
            }
        }
        Some("verify-bench") if a.len() == 7 => {
            verify_bench(&a[2], &a[3], &a[4], &a[5], a[6].parse().unwrap())
        }
        Some("proof-sections") if a.len() == 3 => {
            let p = read_proof(Path::new(&a[2]));
            println!("PROOF_SECTIONS {}", proof_sections(&p));
        }
        Some("zk-diff") if a.len() == 4 => zk_diff(Path::new(&a[2]), Path::new(&a[3])),
        Some("zk-selftest") => zk_selftest::run(&a[2..]),
        Some("zk-layout") if a.len() == 4 => {
            // [E2E-D] stacked layout of a FINAL proof's shape under every zk packing mode
            let setup: Setup = serde_json::from_slice(&std::fs::read(&a[2]).unwrap()).unwrap();
            let p = read_proof(Path::new(&a[3]));
            let mvk = &setup.final_vk.inner;
            let mut per: Vec<_> = mvk
                .per_air
                .iter()
                .zip(&p.trace_vdata)
                .filter_map(|(vk, td)| td.as_ref().map(|td| (vk.params.width.common_main, td.log_height, td.tight_height)))
                .collect();
            per.sort_by_key(|x| std::cmp::Reverse(x.1));
            for zk in [0u8, 2, 3, 4, 5] {
                let t = std::time::Instant::now();
                let l = openvm_stark_backend::prover::stacked_pcs::StackedLayout::new_tight_zk(
                    mvk.params.l_skip,
                    mvk.params.l_skip + mvk.params.n_stack,
                    per.clone(),
                    zk,
                )
                .unwrap();
                println!("ZK_LAYOUT zk={zk} width={} slices={} ms={:.1}", l.width(), l.sorted_cols.len(), t.elapsed().as_secs_f64() * 1e3);
            }
        }
        _ => panic!(
            "usage: base AIR DUMP OUT CERTS EXCLUSIONS | probe OUT | validate-base AIR PUBLIC OUT | chain AIR PUBLIC OUT CERTS EXCLUSIONS [RESUME_LEVEL] | replay-final AIR PUBLIC OUT CERTS EXCLUSIONS LEVEL | verify AIR CLAIM STATEPUBLIC(ignored: in-process) SETUP TRUSTED_SHA256 BUNDLE | claim-parity AIR CLAIM STATEPUBLIC SETUP BUNDLE | proof-sections PROOF | zk-diff PROOF_A PROOF_B"
        ),
    }
}
