//! [E2E-D zk-piop] Self-test of the masked protocol (`WhirLevers::zk >= 4`) on small AIRs with the
//! FINAL configuration (SHA-384, Ext12, the FINAL levers): prove, verify, codec round trip, and
//! tamper tests on every zk field (each must be rejected). `zk = 6` (D-3): no stacked openings,
//! `B` in `stacking_proof.zk[2]`, extension-field stacking masks; the tampers also cover opened
//! WHIR rows of every mask column. Every zk mode also declares a full-height tight chunk
//! (review #1/#2: must be rejected, never hang or panic).
//! `zk-selftest [LOG_FIB] [N_STACK] [ZKS] [LOG_SEND] [SEND_LIVE]`.
use std::sync::Arc;

use openvm_recursion_circuit::sha384::config::{Sha384Config as SC, Sha384CpuEngine};
use openvm_stark_backend::{
    codec::{Decode, Encode},
    interaction::LogUpSecurityParameters,
    proof::Proof,
    prover::{AirProvingContext, ColMajorMatrix, CpuColMajorBackend, ProvingContext},
    test_utils::{
        TestFixture,
        dummy_airs::{
            fib_air::{air::FibonacciAir, trace::generate_trace_rows},
            interaction::dummy_interaction_air::DummyInteractionAir,
        },
    },
    AirRef, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

type F = openvm_recursion_circuit::sha384::config::F;

struct Mixed {
    log_fib: usize,
    log_send: usize,
    log_recv: usize,
    /// sender rows that are nonzero (the rest is a zero tail: tight heights, chunked slices)
    send_live: usize,
}

impl TestFixture<SC> for Mixed {
    fn airs(&self) -> Vec<AirRef<SC>> {
        vec![
            Arc::new(FibonacciAir),
            Arc::new(DummyInteractionAir::new(2, true, 3)),
            Arc::new(DummyInteractionAir::new(2, false, 3)),
        ]
    }
    fn generate_proving_ctx(&self) -> ProvingContext<CpuColMajorBackend<SC>> {
        let n = 1usize << self.log_fib;
        let f_n = {
            use p3_field::PrimeField64;
            let (mut a, mut b) = (0u64, 1u64);
            for _ in 0..n - 1 {
                let c = (a + b) % F::ORDER_U64;
                a = b;
                b = c;
            }
            F::from_u64(b)
        };
        let fib = generate_trace_rows::<F>(0, 1, n);
        // sender: rows (1, v, 7v) with v = i mod R; receiver: rows (S/R, v, 7v), R = receiver height
        let (ns, nr) = (1usize << self.log_send, 1usize << self.log_recv);
        let mut snd = vec![];
        let mut cnt = vec![0usize; nr];
        for i in 0..ns {
            if i < self.send_live {
                let v = i % nr;
                cnt[v] += 1;
                snd.extend([F::ONE, F::from_usize(v + 5), F::from_usize(7 * v + 1)]);
            } else {
                snd.extend([F::ZERO; 3]);
            }
        }
        let mut rcv = vec![];
        for v in 0..nr {
            rcv.extend([F::from_usize(cnt[v]), F::from_usize(v + 5), F::from_usize(7 * v + 1)]);
        }
        ProvingContext::new(vec![
            (0, AirProvingContext::simple(ColMajorMatrix::from_row_major(&fib), vec![F::ZERO, F::ONE, f_n])),
            (1, AirProvingContext::simple_no_pis(ColMajorMatrix::from_row_major(&RowMajorMatrix::new(snd, 3)))),
            (2, AirProvingContext::simple_no_pis(ColMajorMatrix::from_row_major(&RowMajorMatrix::new(rcv, 3)))),
        ])
    }
}

fn params(zk: u8, n_stack: usize) -> SystemParams {
    let (l_skip, k, log_blowup) = (2, 4, 6);
    let levers = WhirLevers {
        k_first: 1,
        multiproof: true,
        keep_domain: true,
        gruen_gkr: true,
        gkr_derive_claims: true,
        next_mask: true,
        gruen_zerocheck: true,
        wide_query_pow: true,
        tight_heights: true,
        whir_y: true,
        zk,
    };
    let h = l_skip + n_stack;
    let lf = 3 + (h - 1 - 3) % k;
    let whir = WhirConfig::new_full(
        log_blowup,
        h,
        WhirParams {
            k,
            log_final_poly_len: lf,
            query_phase_pow_bits: 4,
            folding_pow_bits: 0,
            mu_pow_bits: 0,
            proximity: WhirProximityStrategy::ListDecoding { m: 64 },
        },
        100,
        levers,
        15,
    );
    SystemParams {
        l_skip,
        n_stack,
        w_stack: 4096,
        log_blowup,
        whir,
        logup: LogUpSecurityParameters { max_interaction_count: 1 << 30, log_max_message_length: 7, pow_bits: 0 },
        max_constraint_degree: 3,
    }
}

fn roundtrip(p: &Proof<SC>) -> Proof<SC> {
    let mut b = vec![];
    p.encode(&mut b).unwrap();
    Proof::<SC>::decode(&mut std::io::Cursor::new(&b)).unwrap()
}

pub fn run(args: &[String]) {
    let log_fib: usize = args.first().map(|s| s.parse().unwrap()).unwrap_or(9);
    let n_stack: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(12);
    let zks: Vec<u8> = args
        .get(2)
        .map(|s| s.split(',').map(|x| x.parse().unwrap()).collect())
        .unwrap_or_else(|| vec![0, 2, 4]);
    let log_send: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(7);
    let send_live: usize = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(1 << log_send);
    let fx = Mixed { log_fib, log_send, log_recv: 5, send_live };
    for zk in zks {
        let engine = Sha384CpuEngine::new_final(params(zk, n_stack));
        let t = std::time::Instant::now();
        let (vk, proof) = fx.keygen_and_prove(&engine);
        let prove_ms = t.elapsed().as_secs_f64() * 1e3;
        let mut bytes = vec![];
        proof.encode(&mut bytes).unwrap();
        let t = std::time::Instant::now();
        engine.verify(&vk, &proof).unwrap_or_else(|e| panic!("zk={zk}: honest proof rejected: {e:?}"));
        let verify_ms = t.elapsed().as_secs_f64() * 1e3;
        let back = roundtrip(&proof);
        assert_eq!(back, proof, "zk={zk}: codec round trip");
        engine.verify(&vk, &back).unwrap();
        println!(
            "ZK_SELFTEST zk={zk} ok bytes={} prove_ms={prove_ms:.0} verify_ms={verify_ms:.1} gkr_zk={} batch_zk={} stack_zk={}",
            bytes.len(),
            proof.gkr_proof.zk.len(),
            proof.batch_constraint_proof.zk.len(),
            proof.stacking_proof.zk.len()
        );
        // [E2E-D review #1/#2] each AIR declares its largest tight height `2^log_height` (a changed
        // layout): must be a plain rejection, no panic or hang. The full-stacked-height case
        // (zk 1/2/4: no layout; zk 3/5/6: used to loop forever) is `stark-backend/tests/zk_layout.rs`.
        if zk > 0 {
            for t in 0..proof.trace_vdata.len() {
                let Some(Some(vd)) = proof.trace_vdata.get(t) else { continue };
                if vd.tight_height.is_none() || vd.tight_height == Some(1 << vd.log_height) {
                    continue;
                }
                let mut p = proof.clone();
                if let Some(v) = p.trace_vdata[t].as_mut() {
                    // the largest declarable tight height (full-height layouts: unit tests
                    // `stark-backend/tests/zk_layout.rs`)
                    v.tight_height = Some(1 << v.log_height);
                }
                let t0 = std::time::Instant::now();
                let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| engine.verify(&vk, &p)));
                match r {
                    Ok(Err(e)) => println!(
                        "ZK_SELFTEST_MAX_TIGHT zk={zk} air={t} rejected in {:.1} ms: {e:?}",
                        t0.elapsed().as_secs_f64() * 1e3
                    ),
                    Ok(Ok(())) => panic!("zk={zk}: max tight height accepted"),
                    Err(_) => panic!("zk={zk}: max tight height panicked the verifier"),
                }
            }
        }
        if zk < 4 {
            continue;
        }
        // [E2E-D obligation H] the prover pads to setup-pinned heights: commit the sender AIR at a
        // tight height 8 rows above its natural one (explicit zero rows); the proof must declare
        // exactly the pinned heights and verify.
        if let Some(th) = proof.trace_vdata[1].as_ref().and_then(|v| v.tight_height) {
            let log = proof.trace_vdata[1].as_ref().unwrap().log_height;
            if th + 8 <= 1 << log {
                let widths = [2usize, 3, 3];
                let floor: Vec<(usize, usize, usize)> = proof
                    .trace_vdata
                    .iter()
                    .zip(widths)
                    .enumerate()
                    .map(|(i, (v, w))| {
                        let v = v.as_ref().unwrap();
                        let h = v.tight_height.unwrap_or(1 << v.log_height);
                        (w, v.log_height, if i == 1 { h + 8 } else { h })
                    })
                    .collect();
                openvm_stark_backend::prover::stacked_pcs::set_tight_floor(Some(floor));
                let (vk2, p2) = fx.keygen_and_prove(&engine);
                openvm_stark_backend::prover::stacked_pcs::set_tight_floor(None);
                assert_eq!(p2.trace_vdata[1].as_ref().unwrap().tight_height, Some(th + 8), "zk={zk}: padding");
                engine.verify(&vk2, &p2).unwrap_or_else(|e| panic!("zk={zk}: padded proof rejected: {e:?}"));
                println!("ZK_SELFTEST_PAD zk={zk} air=1 tight {th} -> {} verified", th + 8);
            }
        }
        // tamper tests: every zk field and a sample of masked fields must be bound
        let one = <openvm_recursion_circuit::sha384::config::EF as PrimeCharacteristicRing>::ONE;
        let mut cases: Vec<(String, Proof<SC>)> = vec![];
        for i in 0..proof.gkr_proof.zk.len() {
            let mut p = proof.clone();
            p.gkr_proof.zk[i] += one;
            cases.push((format!("gkr.zk[{i}]"), p));
        }
        for i in 0..proof.batch_constraint_proof.zk.len() {
            let mut p = proof.clone();
            p.batch_constraint_proof.zk[i] += one;
            cases.push((format!("batch.zk[{i}]"), p));
        }
        for i in 0..proof.stacking_proof.zk.len() {
            let mut p = proof.clone();
            p.stacking_proof.zk[i] += one;
            cases.push((format!("stack.zk[{i}]"), p));
        }
        for l in 0..proof.gkr_proof.claims_per_layer.len() {
            let mut p = proof.clone();
            p.gkr_proof.claims_per_layer[l].q_xi_0 += one;
            cases.push((format!("gkr.claims[{l}].q0"), p));
            if l > 0 {
                let mut p = proof.clone();
                p.gkr_proof.claims_per_layer[l].p_xi_1 += one;
                cases.push((format!("gkr.claims[{l}].p1"), p));
            }
        }
        for (r, round) in proof.gkr_proof.sumcheck_polys.iter().enumerate() {
            for s in 0..round.len() {
                let mut p = proof.clone();
                p.gkr_proof.sumcheck_polys[r][s][1] += one;
                cases.push((format!("gkr.sumcheck[{r}][{s}]"), p));
            }
        }
        for r in 0..proof.batch_constraint_proof.sumcheck_round_polys.len() {
            let mut p = proof.clone();
            p.batch_constraint_proof.sumcheck_round_polys[r][0] += one;
            cases.push((format!("batch.round[{r}]"), p));
        }
        {
            let mut p = proof.clone();
            p.batch_constraint_proof.univariate_round_coeffs[3] += one;
            cases.push(("batch.uni[3]".into(), p));
        }
        for t in 0..proof.batch_constraint_proof.column_openings.len() {
            let mut p = proof.clone();
            p.batch_constraint_proof.column_openings[t][0][0] += one;
            cases.push((format!("batch.opening[{t}][0]"), p));
        }
        for r in 0..proof.stacking_proof.sumcheck_round_polys.len() {
            let mut p = proof.clone();
            p.stacking_proof.sumcheck_round_polys[r][1] += one;
            cases.push((format!("stack.round[{r}]"), p));
        }
        let w = proof.stacking_proof.stacking_openings[0].len();
        if w > 0 {
            for c in [0, w - 3, w - 2, w - 1] {
                let mut p = proof.clone();
                p.stacking_proof.stacking_openings[0][c] += one;
                cases.push((format!("stack.opening[{c}]"), p));
            }
        } else {
            // zk = 6: a stacked opening appended to the (empty) list must be rejected
            let mut p = proof.clone();
            p.stacking_proof.stacking_openings[0].push(one);
            cases.push(("stack.opening[appended]".into(), p));
        }
        // opened WHIR rows: first trace column, every pad / M_2 / M_1 / M_s column (zk = 6: 37 mask
        // columns; zk = 4, 5: 15) of the first query
        let rows = &proof.whir_proof.initial_round_opened_rows[0][0][0];
        let width = rows.len();
        let nmask = if zk >= 6 { 37 } else { 15 };
        for c in std::iter::once(0).chain(width - nmask..width) {
            let mut p = proof.clone();
            p.whir_proof.initial_round_opened_rows[0][0][0][c] += F::ONE;
            cases.push((format!("whir.row0[{c}]"), p));
        }
        let mut rejected = 0;
        for (name, p) in &cases {
            match engine.verify(&vk, p) {
                Err(_) => rejected += 1,
                Ok(()) => println!("ZK_SELFTEST_TAMPER_ACCEPTED {name}"),
            }
        }
        println!("ZK_SELFTEST_TAMPER zk={zk} rejected={rejected}/{}", cases.len());
        assert_eq!(rejected, cases.len(), "a tampered proof verified");
    }
}
