//! Entry points for the chunk recursion harness, sharing its exact protocol config.
use super::*;
use openvm_recursion_circuit::{
    nv::circuit::{StatementClaim, commit_program_part},
    sha384::config::Sha384CpuEngine,
};
use openvm_stark_backend::{keygen::types::MultiStarkVerifyingKey, proof::Proof};

pub fn prove_base(
    air: &str,
    dump: &str,
    certs: &str,
    exclusions: &str,
) -> (MultiStarkVerifyingKey<Sha384Config>, Proof<Sha384Config>) {
    // The driver initializes these once, before spawning worker threads.
    let levers = config::sha_levers();
    // 41 B is the documented margin lever (CMS19 constants + Thm 4, K = 0); the wire path is
    // width-generic. Keep the coset/tstar invariants strict and allow only the 42 -> 41 width.
    assert!(
        matches!(levers.digest_bytes, 42 | 41) && levers.coset_leaf && levers.tstar,
        "chunk proof requires coset_leaf, tstar and a 42/41-byte digest"
    );
    let inst = load(air, dump, Variant::D0a);
    report(&inst);
    // NEGATIVE TESTS ONLY: prove a witness the AIR rejects, so the verifier (not the prover's own
    // check) is what refuses it. Never set for a real run.
    if std::env::var("NEARPROOF_NEGATIVE_SKIP_PRECHECK").as_deref() == Ok("1") {
        eprintln!("NEGATIVE TEST: precheck skipped");
    } else {
        precheck(&inst);
    }
    let shape = params_for(&inst, "small");
    let params = crate::profile::shaped_params(
        false,
        shape.n_stack,
        shape.w_stack,
        shape.max_constraint_degree,
        certs,
        exclusions,
    );
    let engine = Sha384CpuEngine::new(params);
    let tables = airs(&inst);
    let (pk, vk) = engine.keygen(&tables);
    let proof = engine
        .prove(
            &engine.device().transport_pk_to_device(&pk),
            ProvingContext::new(
                inst.mats
                    .iter()
                    .enumerate()
                    .map(|(i, m)| {
                        let pv = pv_of(&inst.spec[i], &inst.pubs);
                        let context = if inst.spec[i].cached {
                            // Cached commitments must retain full heights; tight heights apply only
                            // to the common main traces, exactly as for recursive program parts.
                            let (commitment, data) = commit_program_part(
                                engine.config(),
                                ColMajorMatrix::from_row_major(m),
                            );
                            AirProvingContext {
                                cached_mains: vec![CommittedTraceData {
                                    commitment,
                                    trace: m.clone(),
                                    data: Arc::new(data),
                                }],
                                common_main: RowMajorMatrix::new(
                                    vec![F::ZERO; m.values.len() / m.width],
                                    1,
                                ),
                                public_values: pv,
                            }
                        } else {
                            AirProvingContext::simple(m.clone(), pv)
                        };
                        (i, context)
                    })
                    .collect(),
            ),
        )
        .expect("base prove");
    engine.verify(&vk, &proof).expect("base verify");
    let expected = expected_claim(air, dump, vk.inner.params.clone());
    assert_eq!(proof.public_values, expected.public_values);
    assert_eq!(
        proof
            .trace_vdata
            .iter()
            .flatten()
            .flat_map(|v| v.cached_commitments.clone())
            .collect::<Vec<_>>(),
        expected.cached_roots
    );
    println!("BASE_PROOF {}", census(&proof));
    (vk, proof)
}

/// Only verifier-generated public inputs/messages are read, never the proof or private traces.
/// `statepublic` regenerates these files from claim.bin + hint.bin.
pub fn expected_claim(air: &str, public: &str, params: SystemParams) -> StatementClaim {
    public_statement(air, public, params, None, None)
}

/// [e2e tape-eval] The claim with the TAPE bound by evaluation: the stacked public TAPE table's
/// prismalinear evaluation at the base proof's stacking point `u` (computed here from claim +
/// hint, O(stacked height)), instead of its recomputed commitment root.
pub fn expected_claim_at(
    air: &str,
    public: &str,
    params: SystemParams,
    u: &[openvm_recursion_circuit::sha384::config::EF],
) -> StatementClaim {
    public_statement(air, public, params, None, Some(u))
}

/// Prismalinear evaluations at `u` of every column of the stacked (full-height) commitment of
/// `trace`: the values the base proof's `stacking_openings` carry for that commitment.
pub fn stacked_openings_at(
    params: &SystemParams,
    trace: &openvm_stark_backend::prover::ColMajorMatrix<F>,
    u: &[openvm_recursion_circuit::sha384::config::EF],
) -> Vec<openvm_recursion_circuit::sha384::config::EF> {
    use openvm_recursion_circuit::sha384::config::EF;
    use openvm_stark_backend::prover::MatrixDimensions;
    use p3_field::{PrimeCharacteristicRing, TwoAdicField};
    let (q, _) = openvm_stark_backend::prover::stacked_pcs::stacked_matrix_tight(
        params.l_skip,
        params.n_stack,
        &[trace],
        false,
    )
    .expect("stacked TAPE layout");
    let h = q.height();
    assert_eq!(u.len(), params.n_stack + 1, "stacking point length");
    assert_eq!(h, 1usize << (params.l_skip + params.n_stack), "stacked height");
    let omega_pows: Vec<F> = F::two_adic_generator(params.l_skip)
        .powers()
        .take(1 << params.l_skip)
        .collect();
    // Only rows below the last non-zero row contribute: there the high hypercube bits are 0, so
    // eq factors as eq_low(u_0, u_1..u_m) * prod_{i > m} (1 - u_i). Builds 2^(l_skip + m) weights
    // instead of the full stacked height.
    let last = q.values.iter().rposition(|v| *v != F::ZERO).map_or(0, |i| i % h);
    let used = (0..q.width())
        .filter_map(|c| q.values[c * h..(c + 1) * h].iter().rposition(|v| *v != F::ZERO))
        .max()
        .unwrap_or(last);
    let m = (usize::BITS - used.leading_zeros()) as usize; // rows < 2^m
    let m = m.saturating_sub(params.l_skip).min(params.n_stack);
    let tail: EF = u[1 + m..].iter().map(|&x| EF::ONE - x).product();
    let eq = openvm_stark_backend::prover::poly::evals_eq_hyperprism::<F, EF>(&omega_pows, u[0], &u[1..1 + m]);
    q.values
        .chunks_exact(h)
        .map(|col| {
            col[..eq.len()]
                .iter()
                .zip(&eq)
                .filter(|(v, _)| **v != F::ZERO)
                .map(|(&v, &e)| e * v)
                .sum::<EF>()
                * tail
        })
        .collect()
}

/// Rebuild the entire base VK from the declared AIR and verifier-produced public tape.
/// This prevents a local checkpoint for a different relation entering a trusted setup run.
pub fn check_base_key(air: &str, public: &str, vk: &MultiStarkVerifyingKey<Sha384Config>) {
    public_statement(air, public, vk.inner.params.clone(), Some(vk), None);
}

fn public_statement(
    air: &str,
    public: &str,
    params: SystemParams,
    expected_vk: Option<&MultiStarkVerifyingKey<Sha384Config>>,
    tape_point: Option<&[openvm_recursion_circuit::sha384::config::EF]>,
) -> StatementClaim {
    // The driver initializes these once, before spawning worker threads.
    let levers = config::sha_levers();
    // 41 B is the documented margin lever (CMS19 constants + Thm 4, K = 0); the wire path is
    // width-generic. Keep the coset/tstar invariants strict and allow only the 42 -> 41 width.
    assert!(
        matches!(levers.digest_bytes, 42 | 41) && levers.coset_leaf && levers.tstar,
        "chunk proof requires coset_leaf, tstar and a 42/41-byte digest"
    );
    let mut cl = ClassicalAir::parse(&std::fs::read_to_string(air).unwrap(), ORDER);
    assert_eq!(cl.tables.len(), ORDER.len());
    offset_buses(&mut cl);
    let d = std::path::Path::new(public);
    let bytes = std::fs::read(d.join("pubs.bin")).unwrap();
    assert_eq!(bytes.len() % 4, 0);
    let pubs: Vec<F> = bytes
        .chunks_exact(4)
        .map(|c| {
            let x = u32::from_le_bytes(c.try_into().unwrap());
            assert!((x as u64) < P, "noncanonical public field");
            F::new(x)
        })
        .collect();
    let messages: serde_json::Value =
        serde_json::from_slice(&std::fs::read(d.join("pubmsgs.json")).unwrap()).unwrap();
    let mut tape = BTreeMap::new();
    for x in messages.as_array().unwrap() {
        let bus = u16::try_from(x[0].as_u64().unwrap())
            .unwrap()
            .checked_add(BUS_OFFSET)
            .unwrap();
        let msg = x[2]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| {
                let x = v.as_u64().unwrap();
                assert!(x < P, "noncanonical message field");
                x as u32
            })
            .collect();
        add(
            &mut tape,
            (bus, msg),
            if x[1].as_bool().unwrap() { 1 } else { P - 1 },
        );
    }
    let (ts, tm) = harness("TAPE", &tape, true);
    let params_copy = params.clone();
    let engine = Sha384RefEngine::new(params);
    if let Some(expected) = expected_vk {
        let tables: Vec<AirRef<Sha384Config>> = cl
            .tables
            .iter()
            .cloned()
            .chain(std::iter::once(ts))
            .map(|spec| Arc::new(JsonAir { spec }) as AirRef<Sha384Config>)
            .collect();
        let (_, actual) = engine.keygen(&tables);
        assert_eq!(
            serde_json::to_value(&actual).unwrap(),
            serde_json::to_value(expected).unwrap(),
            "base verifying key differs from the declared AIR and public TAPE"
        );
    }
    let mut pvs: Vec<_> = cl.tables.iter().map(|t| pv_of(t, &pubs)).collect();
    pvs.push(vec![]);
    if let Some(u) = tape_point {
        let ys = stacked_openings_at(&params_copy, &ColMajorMatrix::from_row_major(&tm), u);
        return StatementClaim {
            public_values: pvs,
            cached_roots: vec![],
            tape_point: Some((u.to_vec(), ys)),
        };
    }
    let root = commit_program_part(engine.config(), ColMajorMatrix::from_row_major(&tm)).0;
    StatementClaim {
        public_values: pvs,
        cached_roots: vec![root],
        tape_point: None,
    }
}
