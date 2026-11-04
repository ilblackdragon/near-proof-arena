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
    // [E2E-D D-7, review-D6 F1] NEARPROOF_BASE_CLASS=class.json: prove at a pinned shape class
    // (per AIR (log, tight) heights), so every chunk of the class has the same base vk, parameters
    // and committed heights, hence the same tree leaf program. Off by default (natural shape).
    let class = std::env::var("NEARPROOF_BASE_CLASS").ok().map(|p| BaseClass::read(&p));
    let mut inst = inst;
    if let Some(c) = &class {
        // [E2E-D D-8] the class's pinned TAPE shape (log, keys), when it has one
        if let Some(tp) = c.tape_pad() {
            let (ts, tm) = harness_padded("TAPE", &inst.tape, true, Some(&tp));
            *inst.spec.last_mut().unwrap() = ts;
            *inst.mats.last_mut().unwrap() = tm;
            println!("BASE_CLASS_TAPE_PAD log={} keys={}", tp.log, tp.keys.len());
        }
        c.pad(&inst);
    }
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
    if let Some(c) = &class {
        // the floor is matched to the committed common mains by (width, log height), in AIR order
        let f: Vec<(usize, usize, usize)> = inst
            .mats
            .iter()
            .zip(&inst.spec)
            .zip(&c.heights)
            .map(|((m, t), &(log, tight))| {
                let w = if t.cached { 1 } else { m.width };
                (w, log, tight)
            })
            .collect();
        openvm_stark_backend::prover::stacked_pcs::set_tight_floor(Some(f));
    }
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
    if let Some(c) = &class {
        assert!(!openvm_stark_backend::prover::stacked_pcs::tight_floor_pending(), "base class floor not consumed");
        let got: Vec<(usize, usize)> = proof
            .trace_vdata
            .iter()
            .map(|v| {
                let v = v.as_ref().expect("every base AIR has a trace");
                (v.log_height, v.tight_height.unwrap_or(1 << v.log_height))
            })
            .collect();
        assert_eq!(got, c.heights, "base proof heights differ from the class pin");
        println!("BASE_CLASS_HEIGHTS_OK name={} airs={}", c.name, got.len());
    }
    engine.verify(&vk, &proof).expect("base verify");
    let expected = expected_claim_padded(air, dump, vk.inner.params.clone(), class.as_ref().and_then(|c| c.tape_pad()).as_ref());
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
    public_statement(air, public, params, None, None, None)
}

/// [E2E-D D-8] [`expected_claim`] with the class's pinned TAPE shape (`None`: natural TAPE).
pub fn expected_claim_padded(air: &str, public: &str, params: SystemParams, pad: Option<&TapePad>) -> StatementClaim {
    public_statement(air, public, params, None, None, pad)
}

/// [E2E-D D-8] [`expected_claim_at`] with the class's pinned TAPE shape (`None`: natural TAPE).
pub fn expected_claim_at_padded(
    air: &str,
    public: &str,
    params: SystemParams,
    u: &[openvm_recursion_circuit::sha384::config::EF],
    pad: Option<&TapePad>,
) -> StatementClaim {
    public_statement(air, public, params, None, Some(u), pad)
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
    public_statement(air, public, params, None, Some(u), None)
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
    // sum_r v_r * eq(u_0..u_m; r), with eq(r) = eq_uni(u_0, omega^{r mod 2^l_skip}) *
    // prod_i (u_{1+i} if bit i of r >> l_skip else 1 - u_{1+i}) (`evals_eq_hyperprism`'s order),
    // evaluated by folding instead of materializing the 2^(l_skip + m) weights: first the
    // univariate skip block (base-field values times 2^l_skip weights), then one hypercube
    // variable at a time, lo + u_i * (hi - lo). Exact field arithmetic: the same value.
    let d = 1usize << params.l_skip;
    let eq_uni = openvm_stark_backend::prover::poly::evals_eq_hyperprism::<F, EF>(&omega_pows, u[0], &[]);
    assert_eq!(eq_uni.len(), d);
    q.values
        .chunks_exact(h)
        .map(|col| {
            let mut g: Vec<EF> = col[..d << m]
                .chunks_exact(d)
                .map(|blk| {
                    blk.iter()
                        .zip(&eq_uni)
                        .filter(|(v, _)| **v != F::ZERO)
                        .map(|(&v, &e)| e * v)
                        .sum::<EF>()
                })
                .collect();
            for &x in &u[1..1 + m] {
                g = g.chunks_exact(2).map(|p| p[0] + x * (p[1] - p[0])).collect();
            }
            debug_assert_eq!(g.len(), 1);
            g[0] * tail
        })
        .collect()
}

/// Rebuild the entire base VK from the declared AIR and verifier-produced public tape.
/// This prevents a local checkpoint for a different relation entering a trusted setup run.
pub fn check_base_key(air: &str, public: &str, vk: &MultiStarkVerifyingKey<Sha384Config>) {
    public_statement(air, public, vk.inner.params.clone(), Some(vk), None, None);
}

/// Verifier-generated public inputs: the public values and the TAPE's net message counts.
pub struct PublicData {
    pubs: Vec<F>,
    tape: BTreeMap<Key, u64>,
    /// [E2E-D D-8] the pinned TAPE shape the claim is computed under (`None`: natural)
    pad: Option<TapePad>,
}

impl PublicData {
    /// From canonical public inputs and public messages `(bus, send, record)`: the data
    /// `statepublic` writes to pubs.bin / pubmsgs.json, with the same range checks as `read`.
    pub fn new<'a>(pubs: &[u32], msgs: impl IntoIterator<Item = (u64, bool, &'a [u32])>) -> Self {
        let pubs = pubs
            .iter()
            .map(|&x| {
                assert!((x as u64) < P, "noncanonical public field");
                F::new(x)
            })
            .collect();
        let mut tape = BTreeMap::new();
        for (bus, send, m) in msgs {
            let bus = u16::try_from(bus).unwrap().checked_add(BUS_OFFSET).unwrap();
            let msg = m
                .iter()
                .map(|&x| {
                    assert!((x as u64) < P, "noncanonical message field");
                    x
                })
                .collect();
            add(&mut tape, (bus, msg), if send { 1 } else { P - 1 });
        }
        PublicData { pubs, tape, pad: None }
    }

    /// [E2E-D D-8] Compute the claim under a class's pinned TAPE shape (V_d: from the setup).
    pub fn with_tape_pad(mut self, pad: Option<TapePad>) -> Self {
        self.pad = pad;
        self
    }

    /// Read `pubs.bin` + `pubmsgs.json` from a `statepublic` output directory.
    pub fn read(public: &str) -> Self {
        let d = std::path::Path::new(public);
        let bytes = std::fs::read(d.join("pubs.bin")).unwrap();
        assert_eq!(bytes.len() % 4, 0);
        let pubs: Vec<u32> = bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
            .collect();
        let messages: serde_json::Value =
            serde_json::from_slice(&std::fs::read(d.join("pubmsgs.json")).unwrap()).unwrap();
        let msgs: Vec<(u64, bool, Vec<u32>)> = messages
            .as_array()
            .unwrap()
            .iter()
            .map(|x| {
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
                (x[0].as_u64().unwrap(), x[1].as_bool().unwrap(), msg)
            })
            .collect();
        Self::new(&pubs, msgs.iter().map(|(b, s, m)| (*b, *s, m.as_slice())))
    }
}

/// `expected_claim_at` (with `u`) / `expected_claim` (without) on in-memory inputs: each table's
/// public-input bound (`max pub index + 1` over its constraints and interactions, in AIR order;
/// the caller derives it from the AIR bytes it pinned) and the verifier-generated public data.
/// Same claim as the file-based entry points on the equivalent AIR and files.
pub fn expected_claim_parsed(
    table_num_pub: &[usize],
    public: &PublicData,
    params: SystemParams,
    u: Option<&[openvm_recursion_circuit::sha384::config::EF]>,
) -> StatementClaim {
    assert_eq!(table_num_pub.len(), ORDER.len());
    claim_of(table_num_pub, public, params, u)
}

/// Each table's public-input bound as the classical AIR parser computes it (parity checks).
pub fn table_num_pub(air: &str) -> Vec<usize> {
    let cl = ClassicalAir::parse(&std::fs::read_to_string(air).unwrap(), ORDER);
    cl.tables.iter().map(|t| t.num_pub).collect()
}

fn public_statement(
    air: &str,
    public: &str,
    params: SystemParams,
    expected_vk: Option<&MultiStarkVerifyingKey<Sha384Config>>,
    tape_point: Option<&[openvm_recursion_circuit::sha384::config::EF]>,
    pad: Option<&TapePad>,
) -> StatementClaim {
    let mut cl = ClassicalAir::parse(&std::fs::read_to_string(air).unwrap(), ORDER);
    assert_eq!(cl.tables.len(), ORDER.len());
    offset_buses(&mut cl);
    let public = PublicData::read(public).with_tape_pad(pad.cloned());
    if let Some(expected) = expected_vk {
        let (ts, _) = harness_padded("TAPE", &public.tape, true, public.pad.as_ref());
        let engine = Sha384RefEngine::new(params.clone());
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
    let num_pub: Vec<usize> = cl.tables.iter().map(|t| t.num_pub).collect();
    claim_of(&num_pub, &public, params, tape_point)
}

fn claim_of(
    table_num_pub: &[usize],
    public: &PublicData,
    params: SystemParams,
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
    let (_, tm) = harness_padded("TAPE", &public.tape, true, public.pad.as_ref());
    // `pv_of` of each classical table, then the TAPE's (empty) public values.
    let mut pvs: Vec<Vec<F>> = table_num_pub
        .iter()
        .map(|&n| (0..n).map(|i| public.pubs.get(i).copied().unwrap_or(F::ZERO)).collect())
        .collect();
    pvs.push(vec![]);
    if let Some(u) = tape_point {
        let ys = stacked_openings_at(&params, &ColMajorMatrix::from_row_major(&tm), u);
        return StatementClaim {
            public_values: pvs,
            cached_roots: vec![],
            tape_point: Some((u.to_vec(), ys)),
        };
    }
    // The reference engine is only needed for the commitment-root (non-TAPE-eval) claim.
    let engine = Sha384RefEngine::new(params);
    let root = commit_program_part(engine.config(), ColMajorMatrix::from_row_major(&tm)).0;
    StatementClaim {
        public_values: pvs,
        cached_roots: vec![root],
        tape_point: None,
    }
}

/// [E2E-D D-7, review-D6 F1] A pinned base shape class: per AIR (AIR order, TAPE last) the log
/// height and the committed (tight) height. A chunk belongs to the class when every table's natural
/// log height fits the class's and its used rows the class's tight height; its dump is then cut at
/// the class log heights by the generator (`statedump --class`: the table's own padding progression,
/// re-checked there and by `precheck`), and committed at the class tight heights (`stacked_pcs::set_tight_floor`). The base
/// parameters (`params_for`) depend only on the padded heights and widths, so every member gets
/// the same vk and the same committed shape. The cached TAPE table is not padded (V_d recomputes its
/// evaluation from the claim): its log height must equal the class's.
#[derive(Clone, Debug, PartialEq)]
pub struct BaseClass {
    pub name: String,
    /// table names, AIR order (TAPE last)
    pub names: Vec<String>,
    pub heights: Vec<(usize, usize)>,
    /// [E2E-D D-8] the pinned TAPE keys (classical (bus, message length)); with them the TAPE is
    /// built at the class's TAPE log and keys (`TapePad`) instead of the chunk's natural shape
    pub tape_keys: Option<Vec<(u16, usize)>>,
}

impl BaseClass {
    pub fn to_json(&self) -> serde_json::Value {
        let mut v = serde_json::json!({ "name": self.name, "names": self.names, "heights": self.heights });
        if let Some(k) = &self.tape_keys {
            v["tape_keys"] = serde_json::json!(k);
        }
        v
    }
    /// [E2E-D D-8] The class's pinned TAPE shape (`None` without `tape_keys`).
    pub fn tape_pad(&self) -> Option<TapePad> {
        let keys = self.tape_keys.clone()?;
        assert_eq!(self.names.last().map(String::as_str), Some("TAPE"), "TAPE last");
        Some(TapePad { log: self.heights.last().unwrap().0, keys })
    }
    pub fn read(path: &str) -> Self {
        let v: serde_json::Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let heights = v["heights"]
            .as_array()
            .unwrap()
            .iter()
            .map(|h| (h[0].as_u64().unwrap() as usize, h[1].as_u64().unwrap() as usize))
            .collect();
        let names = v["names"].as_array().unwrap().iter().map(|n| n.as_str().unwrap().to_string()).collect();
        let tape_keys = v.get("tape_keys").map(|k| k.as_array().unwrap().iter().map(|x| (x[0].as_u64().unwrap() as u16, x[1].as_u64().unwrap() as usize)).collect());
        BaseClass { name: v["name"].as_str().unwrap().to_string(), names, heights, tape_keys }
    }
    /// Does the chunk's natural shape fit this class (log heights, used rows, TAPE log equal)?
    pub fn admits(&self, shape: &[TableShape]) -> Result<(), String> {
        if shape.len() != self.heights.len() {
            return Err("AIR count".into());
        }
        for (t, &(log, tight)) in shape.iter().zip(&self.heights) {
            // the dump is cut at the class log heights (statedump --class): logs equal exactly
            if t.log != log {
                return Err(format!("{}: log {} != class {log} (dump with statedump --class)", t.name, t.log));
            }
            if t.tight > tight {
                return Err(format!("{}: ({}, {}) exceeds the class ({log}, {tight})", t.name, t.log, t.tight));
            }
        }
        Ok(())
    }
    fn pad(&self, inst: &Inst) {
        let shape = inst_shape(inst);
        if let Err(e) = self.admits(&shape) {
            panic!("chunk not in base class {}: {e}", self.name);
        }
    }
}

/// One base AIR's natural shape: log height, used rows rounded to 2^l_skip (the tight height).
#[derive(Clone, Debug)]
pub struct TableShape {
    pub name: String,
    pub width: usize,
    pub log: usize,
    pub tight: usize,
    pub cached: bool,
}

fn inst_shape(inst: &Inst) -> Vec<TableShape> {
    inst.spec
        .iter()
        .zip(&inst.mats)
        .map(|(t, m)| {
            let w = m.width.max(1);
            let h = m.values.len() / w;
            let used = (0..h).rev().find(|&r| m.values[r * w..(r + 1) * w].iter().any(|v| *v != F::ZERO)).map_or(0, |r| r + 1);
            // a cached table commits its common main (one zero column) tight: 2^l_skip rows
            let tight = if t.cached { 4 } else { used.max(1).next_multiple_of(4) };
            TableShape { name: t.name.clone(), width: m.width, log: h.trailing_zeros() as usize, tight, cached: t.cached }
        })
        .collect()
}

/// The natural base shape of a dump (no proof).
pub fn base_shape(air: &str, dump: &str) -> Vec<TableShape> {
    inst_shape(&load(air, dump, Variant::D0a))
}

/// [E2E-D D-8] Is the dump (cut at the class logs: `statedump --class`) admitted by the class, as
/// `prove_base` would admit it (the class's TAPE pad applied, logs equal, used rows within the
/// tight heights)? With `check`, also the base prover's own precheck (every constraint, every bus
/// balanced with the public messages; panics on a failure).
pub fn class_admits(air: &str, dump: &str, class: &BaseClass, check: bool) -> Result<(), String> {
    let mut inst = load(air, dump, Variant::D0a);
    if let Some(tp) = class.tape_pad() {
        let (ts, tm) = harness_padded("TAPE", &inst.tape, true, Some(&tp));
        *inst.spec.last_mut().unwrap() = ts;
        *inst.mats.last_mut().unwrap() = tm;
    }
    class.admits(&inst_shape(&inst))?;
    if check {
        precheck(&inst);
    }
    Ok(())
}

/// [E2E-D D-7] The smallest class admitting every given shape, with each tight height rounded up
/// to a multiple of `2^(log - bucket_bits)` (headroom, so later chunks of similar size fit).
pub fn class_of(name: &str, shapes: &[Vec<TableShape>], bucket_bits: usize) -> BaseClass {
    let n = shapes[0].len();
    let heights = (0..n)
        .map(|i| {
            let log = shapes.iter().map(|s| s[i].log).max().unwrap();
            if shapes[0][i].cached {
                assert!(shapes.iter().all(|s| s[i].log == log), "{}: cached table logs differ", shapes[0][i].name);
                return (log, 4);
            }
            let t = shapes.iter().map(|s| s[i].tight).max().unwrap();
            let q = (1usize << log.saturating_sub(bucket_bits)).max(4);
            (log, t.next_multiple_of(q).min(1 << log))
        })
        .collect();
    BaseClass { name: name.to_string(), names: shapes[0].iter().map(|t| t.name.clone()).collect(), heights, tape_keys: None }
}
