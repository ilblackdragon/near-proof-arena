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
    assert!(levers.digest_bytes == 42 && levers.coset_leaf && levers.tstar);
    let inst = load(air, dump, Variant::D0a);
    report(&inst);
    precheck(&inst);
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
    public_statement(air, public, params, None)
}

/// Rebuild the entire base VK from the declared AIR and verifier-produced public tape.
/// This prevents a local checkpoint for a different relation entering a trusted setup run.
pub fn check_base_key(air: &str, public: &str, vk: &MultiStarkVerifyingKey<Sha384Config>) {
    public_statement(air, public, vk.inner.params.clone(), Some(vk));
}

fn public_statement(
    air: &str,
    public: &str,
    params: SystemParams,
    expected_vk: Option<&MultiStarkVerifyingKey<Sha384Config>>,
) -> StatementClaim {
    // The driver initializes these once, before spawning worker threads.
    let levers = config::sha_levers();
    assert!(levers.digest_bytes == 42 && levers.coset_leaf && levers.tstar);
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
    let root = commit_program_part(engine.config(), ColMajorMatrix::from_row_major(&tm)).0;
    let mut pvs: Vec<_> = cl.tables.iter().map(|t| pv_of(t, &pubs)).collect();
    pvs.push(vec![]);
    StatementClaim {
        public_values: pvs,
        cached_roots: vec![root],
    }
}
