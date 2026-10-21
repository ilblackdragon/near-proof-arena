//! NV v0 circuit: ALU + transcript engine + Merkle AIR + SHA subsystem.
use std::{collections::HashMap, sync::Arc};

use openvm_stark_backend::{
    interaction::BusIndex, keygen::types::MultiStarkVerifyingKey, proof::Proof, AirRef,
    StarkProtocolConfig,
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;

use super::{
    uair::{nv_trace, NvAir, UBuses, E1_BITS, E1_SIZE},
    builder::Builder,
    fmt::sha_k,
        hash::{byte_table2, generate2, ByteAir, HashBuses, Job2, Work2, U2},
    isa::Op,
    transcript2::{replay2_multi, tr2_traces, TrBuses},
    verifier::build_verifier,
};
use crate::sha384::{
    compress4_air::{Layout, Sha512Air4, TableAir4},
    config::{Digest, Sha384Config, F},
    jobs::Unit,
};

#[derive(Clone, Copy, Debug)]
pub struct NvBuses {
    pub alu: UBuses,
    pub h: HashBuses,
    pub tr: TrBuses,
}

impl NvBuses {
    pub fn new() -> Self {
        let mut i: BusIndex = 0;
        let mut next = || {
            i += 1;
            i - 1
        };
        let slot = next();
        let job = next();
        let digest = next();
        let mut alu = UBuses {
            mem: next(),
            slot,
            job,
            digest,
            bind: next(),
            acc: next(),
            chain_start: 0,
        };
        let h = HashBuses {
            ctl: next(),
            k: next(),
            lb: next(),
            iface: next(),
            word: next(),
            slot,
            job,
            digest,
            byte: next(),
        };
        let tr = TrBuses {
            sample: next(),
            word: next(),
            chain: next(),
            // [agg] allocated LAST so every pre-existing bus keeps its index
            chain_start: next(),
        };
        alu.chain_start = tr.chain_start;
        Self { alu, h, tr }
    }
}

impl Default for NvBuses {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone)]
pub struct NvCircuit {
    pub buses: NvBuses,
    /// WHIR folding factor of the child (coset tree height)
    pub k: usize,
    /// NvAir height 2^log_rows
    pub log_rows: usize,
    /// program length 2^prog_log (env NV_PROG_LOG, default log_rows - 2)
    pub prog_log: usize,
    pub sha_instances: usize,
    /// bind the child's ALU program to ours (child must be NV with the same program)
    pub bind: bool,
    /// fixed trace heights (AIR order of `airs`); None = natural (next power of two)
    pub heights: Option<Vec<usize>>,
    /// the child is an NV proof: pass its statement digest through and bind its program
    pub child_nv: bool,
    /// TEST ONLY: passthrough without program binding (child of a different size)
    #[cfg(test)]
    pub test_no_bind: bool,
    /// G2: P0..P3 as a cached main part (NV levels); false = in common main (FINAL)
    pub program_part: bool,
    /// G2 anchor (M, C_M): a child at level M is bound by its cached program root = C_M, the
    /// setup commitment of the level-M program; a child at any other level by BIND (child
    /// program = own).  M = 1 while the program has converged by level 2; with tight heights the
    /// program depends on the child's committed heights, so M is the last level whose program
    /// differs from the converged one (levels <= M each anchor at their own child level).
    pub anchor: Option<(u32, crate::sha384::config::Digest)>,
    /// G2 + tight heights: minimum committed rows per AIR (AIR order) of this level's own traces
    /// (prover-side floor, `stacked_pcs::set_tight_floor`).  The parent's program depends on its
    /// child's committed heights; pinning them to setup constants makes the program converge
    /// (`NvCircuit::select_anchor` then switches to BIND).  None = natural tight heights.
    pub tight_floor: Option<Vec<usize>>,
}

impl NvCircuit {
    /// A copy of this circuit (same shape, constants and flags).
    pub fn clone_shape(&self) -> Self {
        self.clone()
    }

    pub fn new(k: usize, log_rows: usize, sha_instances: usize) -> Self {
        Self {
            buses: NvBuses::new(),
            k,
            log_rows,
            prog_log: std::env::var("NV_PROG_LOG")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(log_rows - 2),
            sha_instances,
            bind: false,
            heights: None,
            child_nv: false,
            #[cfg(test)]
            test_no_bind: false,
            program_part: false,
            anchor: None,
            tight_floor: None,
        }
    }

    pub fn layout(&self) -> Layout {
        Layout::new(sha_k())
    }

    pub fn airs<SC: StarkProtocolConfig<F = F>>(&self) -> Vec<AirRef<SC>> {
        let b = self.buses;
        let lay = self.layout();
        assert_eq!(self.sha_instances, 1, "NV v1 uses one compression AIR");
        vec![
            Arc::new(NvAir { buses: b.alu, h: b.h, t: b.tr, program_part: self.program_part }) as AirRef<SC>,
            Arc::new(Sha512Air4 {
                lay,
                buses: b.h.sha(),
                cid_offset: 0,
            }),
            Arc::new(TableAir4 {
                lay,
                buses: b.h.sha(),
            }),
            Arc::new(ByteAir { buses: b.h }),
        ]
    }

    pub fn reserved(&self) -> usize {
        E1_SIZE + (1 << (self.prog_log - E1_BITS))
    }

    /// Execute the verifier program and generate every trace (AIR order as `airs`).
    pub fn generate(
        &self,
        vk: &MultiStarkVerifyingKey<Sha384Config>,
        proof: &Proof<Sha384Config>,
    ) -> (Vec<RowMajorMatrix<F>>, Builder) {
        // program binding is on whenever the child is an NV proof (G1 / V_d: the program is
        // pinned, so every NV child's program must be bound to this level's)
        #[allow(unused_mut)]
        let mut bind = self.bind || self.child_nv;
        #[cfg(test)]
        {
            bind &= !self.test_no_bind;
        }
        let child_nv = self.child_nv;
        self.generate_with(move |b| {
            b.bind = bind;
            b.child_nv = child_nv;
            build_verifier(b, vk, proof);
        })
    }

    /// The verifier program's words for this child (no trace generation).
    pub fn program_words(&self, vk: &MultiStarkVerifyingKey<Sha384Config>, proof: &Proof<Sha384Config>) -> Vec<[u32; 4]> {
        #[allow(unused_mut)]
        let mut bind = self.bind || self.child_nv;
        #[cfg(test)]
        {
            bind &= !self.test_no_bind;
        }
        let mut b = Builder::new(self.log_rows, self.reserved());
        b.prog_log = self.prog_log;
        b.begin();
        b.anchor = self.anchor;
        b.bind = bind;
        b.child_nv = self.child_nv;
        build_verifier(&mut b, vk, proof);
        b.finish();
        b.instrs.iter().map(|i| i.words()).collect()
    }

    /// [agg] Execute an arbitrary verifier program (e.g. the k-child aggregation program of
    /// nv/agg.rs) and generate every trace.  `generate` is this with `build_verifier` as the body.
    pub fn generate_with(&self, program: impl FnOnce(&mut Builder)) -> (Vec<RowMajorMatrix<F>>, Builder) {
        self.generate_traces_of(program)
    }

    /// G2 anchor rule (setup, deterministic) for the level verifying `child` at level
    /// `child_level` >= 1, whose program words are `child_words` and cached program root
    /// `child_root`:
    /// * keep the current anchor (M, C_M) if, with it, this level's program equals the child's
    ///   (the program has converged: the child is then bound by BIND, child level != M);
    /// * otherwise anchor at the child: (child_level, child_root), bound by the root check.
    /// With tight heights the program depends on the child's committed heights, so the first
    /// levels each anchor at their child until the heights (and so the program) stop changing;
    /// V_d pins the converged program, which embeds the final (M, C_M).
    pub fn select_anchor(
        &self,
        vk: &MultiStarkVerifyingKey<Sha384Config>,
        proof: &Proof<Sha384Config>,
        child_level: u32,
        child_words: &[[u32; 4]],
        child_root: crate::sha384::config::Digest,
    ) -> (u32, crate::sha384::config::Digest) {
        if let Some(a) = self.anchor.filter(|&(m, _)| m < child_level) {
            let mut c = self.clone();
            c.anchor = Some(a);
            if c.program_words(vk, proof) == child_words {
                return a;
            }
        }
        (child_level, child_root)
    }

    /// Run an arbitrary program body (the verifier, or a test forgery) and generate every trace.
    pub fn generate_program(&self, body: impl FnOnce(&mut Builder)) -> (Vec<RowMajorMatrix<F>>, Builder) {
        self.generate_traces_of(body)
    }

    /// [`Self::generate_program`] body under the name the agg overlay uses.
    fn generate_traces_of(&self, body: impl FnOnce(&mut Builder)) -> (Vec<RowMajorMatrix<F>>, Builder) {
        let mut b = Builder::new(self.log_rows, self.reserved());
        b.prog_log = self.prog_log;
        b.begin();
        b.anchor = self.anchor;
        body(&mut b);
        b.finish();
        let _ = self.k; // per-round folding factors come from the child vk

        // leaf and Merkle-node jobs (ids 0..), then the transcript jobs
        let leaf_jobs: Vec<Job2> = b.jobs();
        let log = b.transcript.clone().into_log();
        let tr_jobs = replay2_multi(&log, &b.transcript.starts);
        let hh = |i: usize| self.heights.as_ref().map_or(1, |h| h[i]);
        let mut work = Work2 {
            jobs: leaf_jobs,
            nodes: vec![],
        };
        work.jobs.extend(tr_jobs.iter().map(|j| j.job()));
        let sha = generate2(
            &work,
            self.layout(),
            self.heights.as_ref().map(|_| hh(1)),
        );
        let tr = tr2_traces(&tr_jobs);
        let mut counts = sha.byte_counts.clone();
        for (c, t) in counts.iter_mut().zip(&tr.byte_counts) {
            *c += t;
        }
        let nv = nv_trace(&b.instrs, &b.vals, &b.wits, &b.wits_x, &sha.glue_rows, &tr.hash, &tr.samp, self.log_rows, &mut counts);
        let mats = vec![nv, sha.compress, sha.table, byte_table2(&counts)];
        if let Some(h) = &self.heights {
            use p3_matrix::Matrix;
            for (i, m) in mats.iter().enumerate() {
                assert_eq!(m.height(), h[i], "AIR {i}: natural height exceeds the fixed height");
            }
        }
        (mats, b)
    }
}

/// The statement the chain exposes, as V_d checks it: the app proof's public values (all AIRs in
/// order) **and** the base proof's cached commitments, in the order the NV program appends them
/// (AIR order, then each AIR's cached mains in proof order).  The base's cached tables are the
/// TAPE table and the join's host-wire commitments; their roots are proof values, so they are only
/// in the statement if they are listed here.
///
/// `cached_roots` is what the claim *says* those roots are.  For TAPE it is recomputed from the
/// claim's public messages (`tapeCanon`); V_d does not take it from the proof.
#[derive(Clone, Debug, Default)]
pub struct StatementClaim {
    pub public_values: Vec<Vec<F>>,
    /// The base proof's cached commitments in the order the NV program chains them (AIR order,
    /// then each AIR's cached mains in proof order).  Empty = the pre-P4 statement.
    pub cached_roots: Vec<Digest>,
}

impl StatementClaim {
    pub fn new(public_values: Vec<Vec<F>>) -> Self {
        Self { public_values, cached_roots: vec![] }
    }

    /// The statement digest the chain exposes: the G1 digest over the public values, then each
    /// cached root folded in by one Merkle-node compression (the in-circuit order).
    pub fn digest(&self) -> Digest {
        use openvm_stark_backend::hasher::MerkleHasher;
        let mut d = crate::sha384::config::statement_digest(&self.public_values);
        for r in &self.cached_roots {
            d = crate::sha384::config::ShaHasher.compress(d, *r);
        }
        d
    }
}

/// Native statement check of the final proof (final-soundness G1 + P4): NvAir public values
/// 1..19 must be the statement digest of the claimed chunk statement (the app proof's public
/// values and, when the base carries cached tables, their roots).
pub fn check_statement(nv_public_values: &[F], app_public_values: &[Vec<F>]) -> bool {
    check_statement_claim(nv_public_values, &StatementClaim::new(app_public_values.to_vec()))
}

/// The same check against a claim that also names the base's cached roots (P4: TAPE and the
/// host-wire commitments).
pub fn check_statement_claim(nv_public_values: &[F], claim: &StatementClaim) -> bool {
    let d = claim.digest();
    let (lo, hi) = super::builder::digest_cells(d);
    nv_public_values.len() == super::uair::NV_NUM_PVS
        && nv_public_values[1..13] == lo[..]
        && nv_public_values[13..19] == hi[..6]
}

/// Natural tight heights of a level's traces (AIR order): rows up to the last non-zero row,
/// rounded up to a multiple of 2^l_skip (as `stacked_pcs::tight_height`).
pub fn natural_tight_heights(mats: &[RowMajorMatrix<F>], l_skip: usize) -> Vec<usize> {
    use p3_matrix::Matrix;
    mats.iter()
        .map(|m| {
            let w = m.width();
            let last = (0..m.height()).rev().find(|&r| m.values[r * w..(r + 1) * w].iter().any(|v| *v != F::ZERO)).map_or(0, |r| r + 1);
            last.max(1).next_multiple_of(1 << l_skip)
        })
        .collect()
}

/// The level's program part P0..P3 (G2) committed as a cached main trace under `config`.
/// Always committed with tight heights OFF (last argument), even when the level's own traces use
/// the tight lever: a cached trace committed tight is rejected by the native verifier (auditor
/// R5, `native_r5_cached_tight_commit`).  The program part is a full-height column set anyway.
pub fn commit_program_part(
    config: &Sha384Config,
    prog: openvm_stark_backend::prover::ColMajorMatrix<F>,
) -> (crate::sha384::config::Digest, openvm_stark_backend::prover::stacked_pcs::StackedPcsData<F, crate::sha384::config::Digest>) {
    use openvm_stark_backend::StarkProtocolConfig;
    let p = config.params();
    openvm_stark_backend::prover::stacked_pcs::stacked_commit_odd(
        config.hasher(),
        p.l_skip,
        p.n_stack,
        p.log_blowup,
        p.whir.k_first(),
        p.whir.domain_odd_factor,
        &[&prog],
        false,
    )
    .expect("program part commitment")
}

/// C_L1 (G2): the commitment of a level's program part, from its NvAir trace (setup, native).
pub fn program_commitment(config: &Sha384Config, nv_trace: &RowMajorMatrix<F>) -> crate::sha384::config::Digest {
    let (_, prog) = super::uair::split_program_part(nv_trace);
    commit_program_part(config, openvm_stark_backend::prover::ColMajorMatrix::from_row_major(&prog)).0
}

/// Proving contexts of an NV level: AIR 0 with the builder's public values (and, with the
/// program part, the common main without P0..P3 plus the committed cached part).
pub fn nv_contexts(
    circ: &NvCircuit,
    config: &Sha384Config,
    mats: Vec<RowMajorMatrix<F>>,
    pvs: Vec<F>,
) -> Vec<openvm_stark_backend::prover::AirProvingContext<openvm_cpu_backend::CpuBackend<Sha384Config>>> {
    use openvm_stark_backend::prover::{AirProvingContext, CommittedTraceData};
    mats.into_iter()
        .enumerate()
        .map(|(i, m)| {
            if i == 0 && circ.program_part {
                let (common, prog) = super::uair::split_program_part(&m);
                let (commitment, data) =
                    commit_program_part(config, openvm_stark_backend::prover::ColMajorMatrix::from_row_major(&prog));
                AirProvingContext {
                    cached_mains: vec![CommittedTraceData { commitment, trace: prog, data: std::sync::Arc::new(data) }],
                    common_main: common,
                    public_values: pvs.clone(),
                }
            } else if i == 0 {
                AirProvingContext::simple(m, pvs.clone())
            } else {
                AirProvingContext::simple_no_pis(m)
            }
        })
        .collect()
}

/// Prove one NV level; returns (vk, proof, executed builder, trace matrices' shapes).
pub fn prove_level(
    circ: &NvCircuit,
    engine: &crate::sha384::config::Sha384CpuEngine,
    child_vk: &MultiStarkVerifyingKey<Sha384Config>,
    child: &Proof<Sha384Config>,
) -> (
    MultiStarkVerifyingKey<Sha384Config>,
    Proof<Sha384Config>,
    Builder,
    Vec<(usize, usize)>,
) {
    let (mats, b) = circ.generate(child_vk, child);
    let (vk, proof, shapes) = prove_mats(circ, engine, mats, &b);
    (vk, proof, b, shapes)
}

/// Prove executed NV traces (public values from the builder).
pub fn prove_mats(
    circ: &NvCircuit,
    engine: &crate::sha384::config::Sha384CpuEngine,
    mats: Vec<RowMajorMatrix<F>>,
    b: &Builder,
) -> (MultiStarkVerifyingKey<Sha384Config>, Proof<Sha384Config>, Vec<(usize, usize)>) {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::{
        prover::{AirProvingContext, DeviceDataTransporter, MatrixDimensions, ProvingContext},
        StarkEngine,
    };
    let airs = circ.airs::<Sha384Config>();
    let (pk, vk) = engine.keygen(&airs);
    assert!(b.failures.is_empty(), "verifier program failures: {:?}", b.failures);
    let shapes = mats.iter().map(|m| (m.height(), m.width())).collect();
    let pvs = b.public_values();
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = nv_contexts(circ, engine.config(), mats, pvs);
    let d_pk = engine.device().transport_pk_to_device(&pk);
    if let Some(fl) = &circ.tight_floor {
        let f: Vec<(usize, usize, usize)> = ctxs
            .iter()
            .zip(fl)
            .map(|(c, &m)| (c.common_main.width(), c.common_main.height().trailing_zeros() as usize, m))
            .collect();
        openvm_stark_backend::prover::stacked_pcs::set_tight_floor(Some(f));
    }
    let proof = engine.prove(&d_pk, ProvingContext::new(ctxs.into_iter().enumerate().collect()));
    openvm_stark_backend::prover::stacked_pcs::set_tight_floor(None);
    let proof = proof.unwrap();
    if let Some(fl) = &circ.tight_floor {
        for (i, &m) in fl.iter().enumerate() {
            if let Some(h) = proof.trace_vdata[i].as_ref().and_then(|v| v.tight_height) {
                assert!(h >= m.min(1 << proof.trace_vdata[i].as_ref().unwrap().log_height), "AIR {i}: committed {h} below the floor {m}");
            }
        }
    }
    engine.verify(&vk, &proof).unwrap();
    (vk, proof, shapes)
}
