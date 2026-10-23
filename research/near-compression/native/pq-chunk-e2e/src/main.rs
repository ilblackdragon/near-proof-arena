//! Real D0a base proof -> bound NV recursion -> separately verified final packet.
//! Research protocol: cryptographic security and zero-knowledge masking are not established here.
mod perf_check;
mod profile;
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
        size(&p.whir_proof) - 42 * (init_digests + later_digests.iter().sum::<usize>()),
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
    let claim = state::chunk_bridge::expected_claim(air, public, base_params.clone());
    assert_eq!(p.public_values, claim.public_values, "base public values");
    assert_eq!(
        p.trace_vdata
            .iter()
            .flatten()
            .flat_map(|v| v.cached_commitments.clone())
            .collect::<Vec<_>>(),
        claim.cached_roots,
        "base TAPE root"
    );
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
        version: 1,
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
    wrong.cached_roots[0][0] ^= 1;
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
    let mut packet = b"NPQCH01\0".to_vec();
    packet.extend_from_slice(&(hint.len() as u64).to_le_bytes());
    packet.extend_from_slice(&hint);
    fp.encode(&mut packet).unwrap();
    std::fs::write(out.join("FINAL.bundle"), &packet).unwrap();
    let result = serde_json::json!({"scope":"D0a","trusted_setup_bytes":setup_size,"security_established":false,"zero_knowledge_established":false,"proof_bytes":proof_bytes,"hint_bytes":hint.len(),"bundle_bytes":packet.len(),"under_300000":packet.len()<300000,"setup_sha256":pin,"levels":levels+1});
    std::fs::write(
        out.join("RESULT.json"),
        serde_json::to_vec_pretty(&result).unwrap(),
    )
    .unwrap();
    println!("FINAL_VERIFIED {result}");
}
fn verify(air: &str, claim_path: &str, helper: &str, setup_path: &str, pin: &str, bundle: &str) {
    let setup_bytes = std::fs::read(setup_path).unwrap();
    assert_eq!(
        hash(&setup_bytes),
        pin,
        "untrusted setup: hash differs from operator's pin"
    );
    let mut setup: Setup = serde_json::from_slice(&setup_bytes).unwrap();
    assert_eq!(setup.domain_odd_factor, 15);
    setup.base_params.whir.domain_odd_factor = setup.domain_odd_factor;
    setup.final_vk.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
    assert_eq!(setup.version, 1);
    assert_eq!(
        hash(&std::fs::read(air).unwrap()),
        setup.air_sha256,
        "AIR differs from pinned setup"
    );
    let packet = std::fs::read(bundle).unwrap();
    assert!(
        packet.len() >= 16 && &packet[..8] == b"NPQCH01\0",
        "bundle framing"
    );
    let n = usize::try_from(u64::from_le_bytes(packet[8..16].try_into().unwrap())).unwrap();
    assert!(n <= packet.len() - 16, "truncated hint");
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
    let expected =
        state::chunk_bridge::expected_claim(air, public.to_str().unwrap(), setup.base_params);
    let fp = decode_proof(&packet[16 + n..]);
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
    println!(
        "INDEPENDENT_VERIFY_OK bundle_bytes={} under_300000={}",
        packet.len(),
        packet.len() < 300000
    );
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
        Some("proof-sections") if a.len() == 3 => {
            let p = read_proof(Path::new(&a[2]));
            println!("PROOF_SECTIONS {}", proof_sections(&p));
        }
        _ => panic!(
            "usage: base AIR DUMP OUT CERTS EXCLUSIONS | probe OUT | validate-base AIR PUBLIC OUT | chain AIR PUBLIC OUT CERTS EXCLUSIONS [RESUME_LEVEL] | replay-final AIR PUBLIC OUT CERTS EXCLUSIONS LEVEL | verify AIR CLAIM STATEPUBLIC SETUP TRUSTED_SHA256 BUNDLE | proof-sections PROOF"
        ),
    }
}
