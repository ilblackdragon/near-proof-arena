//! NV in-circuit SHA-384 transcript, word format v2 (see transcript/sha_transcript.rs for
//! the protocol).  Differences: the state and commit digests are 18 air2 limbs and are
//! framed as word units; commit events are 18 limb events; samples are extracted per
//! 64-bit state word (two little-endian u32 candidates per word).
//! v3 (U2): observed felts and commitment words are pushed by the ALU directly as units of
//! statically numbered flush / commit jobs (ids TJOB_STATIC_BASE + i, anchored by the ALU
//! with (job, t_start, count)); squeeze jobs are numbered TJOB_SQUEEZE_BASE + i.  The
//! hash-chain AIR forwards each job's output state as the state units of the next job.
//! Samples travel on the slot bus as (0, tidx, 0, KIND_SAMPLE, value, 0, 0).
use core::borrow::{Borrow, BorrowMut};

use openvm_recursion_circuit_derive::AlignedBorrow;
use openvm_stark_backend::{
    interaction::{BusIndex, InteractionBuilder, PermutationCheckBus},
    BaseAirWithPublicValues, PartitionedBaseAir,
};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use super::{
    fmt::{digest_limbs, limbs_digest, limbs_from_bytes, split_bits, wl, NV_DIGEST},
    hash::{HashBuses, Job2, U2},
};
use crate::sha384::config::{
    digest_bytes, digest_words, hash_parts, initial_state, ShaTranscriptLog, F, KIND_COMMIT,
    KIND_OBSERVE, KIND_SAMPLE, SAMPLE_BOUND, TAG_COMMIT, TAG_FLUSH, TAG_SQUEEZE,
};

#[derive(Clone, Copy, Debug)]
pub struct TrBuses {
    pub sample: BusIndex,
    pub word: BusIndex,
    /// hash-chain link (job, input state limbs): the previous row provides the next row's state
    pub chain: BusIndex,
}

pub const TJOB_STATIC_BASE: u32 = 1 << 24;
pub const TJOB_SQUEEZE_BASE: u32 = 1 << 25;
pub const SLOT_ANCHOR: u32 = 2;
pub const SLOT_POW: u32 = 3;

/// Units of a transcript job's initial-state block (for the first job of the chain).
pub fn initial_state_words() -> [u64; 6] {
    state_words(&initial_state())
}

fn state_words(state: &[u8; 48]) -> [u64; 6] {
    std::array::from_fn(|i| u64::from_be_bytes(state[8 * i..8 * i + 8].try_into().unwrap()))
}
fn state_limbs(state: &[u8; 48]) -> [u32; NV_DIGEST] {
    let w = state_words(state);
    std::array::from_fn(|i| wl(w[i / 3])[i % 3])
}

fn emit<AB: InteractionBuilder>(
    b: &mut AB,
    slot: BusIndex,
    tidx: AB::Expr,
    kind: AB::Expr,
    value: AB::Expr,
    mult: AB::Expr,
) {
    PermutationCheckBus::new(slot).send(
        b,
        [
            AB::Expr::ZERO,
            tidx,
            AB::Expr::ZERO,
            kind,
            value,
            AB::Expr::ZERO,
            AB::Expr::ZERO,
        ],
        mult,
    );
}

// ---------------------------------------------------------------------------------------
// Replay
// ---------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op2 {
    Flush,
    Commit,
    /// T* squeeze block B_j = H(5, kappa || le32(j))
    Squeeze,
    /// T* PoW block B_1 = H(7, sigma || w || le32(1)) (anchored; PoW on its leading bits)
    Pow,
    /// T* PoW-run block B_j = H(7, sigma || w || le32(j)), j >= 2
    PowQ,
}

#[derive(Clone, Debug)]
pub struct Read2 {
    pub wi: usize,
    pub n: u32,
    pub acc: bool,
}

#[derive(Clone, Debug)]
pub struct TrJob2 {
    pub id: u32,
    pub op: Op2,
    pub t_start: usize,
    pub cnt: usize,
    pub state_in: [u8; 48],
    pub state_out: [u8; 48],
    pub payload: [F; NV_DIGEST],
    pub obs: Vec<F>,
    pub reads: Vec<Read2>,
    /// T*: block counter j (squeeze / PoW blocks), PoW witness felts, samples read from B_1
    pub ctr: u32,
    pub wit: Vec<F>,
    pub scnt: usize,
    /// [agg] first job of a transcript chain (its input state is the initial state; anchored
    /// by the ALU with P3 = 1)
    pub first: bool,
}

impl TrJob2 {
    pub fn job(&self) -> Job2 {
        let mut units = vec![U2::Felt(48), U2::Felt(0)];
        units.extend(state_words(&self.state_in).map(U2::Word));
        let tag = match self.op {
            Op2::Flush => {
                units.push(U2::Felt(4 * self.obs.len() as u32));
                units.push(U2::Felt(0));
                units.extend(self.obs.iter().map(|x| U2::Felt(x.as_canonical_u32())));
                TAG_FLUSH
            }
            Op2::Pow | Op2::PowQ => {
                units.push(U2::Felt(4 * (self.wit.len() as u32 + 1)));
                units.push(U2::Felt(0));
                units.extend(self.wit.iter().map(|x| U2::Felt(x.as_canonical_u32())));
                units.push(U2::Felt(self.ctr));
                crate::sha384::config::TAG_POW
            }
            Op2::Commit => {
                units.push(U2::Felt(crate::sha384::config::sha_levers().digest_bytes as u32));
                units.push(U2::Felt(0));
                units.extend(super::hash::digest_units(digest_words(limbs_digest(&self.payload))));
                TAG_COMMIT
            }
            Op2::Squeeze => {
                units.push(U2::Felt(4));
                units.push(U2::Felt(0));
                units.push(U2::Felt(self.ctr));
                TAG_SQUEEZE
            }
        };
        let wread = self.reads.iter().fold(0u8, |m, r| m | (1 << (r.wi / 2)));
        Job2 { id: self.id, node: false, tag, units, wread }
    }
}

/// Replay a transcript log as hash-chain jobs (T* transcript only).
pub fn replay2(log: &ShaTranscriptLog) -> Vec<TrJob2> {
    replay2_multi(log, &[])
}

/// [agg] Replay a log that holds several independent transcripts back to back: a fresh chain
/// (initial state) starts at each tidx in `starts` (and at 0).  Job ids and tidx stay global.
pub fn replay2_multi(log: &ShaTranscriptLog, starts: &[usize]) -> Vec<TrJob2> {
    use crate::sha384::config::{felt_bytes, pow_skip_words, SqueezeSrc, KIND_POW, KIND_POW_CONT, TAG_POW};
    assert!(crate::sha384::config::sha_levers().tstar, "the NV transcript requires the T* transcript");
    let mut jobs: Vec<TrJob2> = vec![];
    let mut state = initial_state();
    let mut src = SqueezeSrc::Key(state);
    let mut ctr = 0u32;
    let mut nw = 12usize;
    let mut pending: Vec<F> = vec![];
    let mut pstart = 0usize;
    let mut n_static = 0u32;
    let mut n_squeeze = 0u32;
    let mut pow_wit: Vec<F> = vec![];
    let blank = |id: u32, op: Op2, t_start: usize, cnt: usize, state_in: [u8; 48], state_out: [u8; 48]| TrJob2 {
        id,
        op,
        t_start,
        cnt,
        state_in,
        state_out,
        payload: [F::ZERO; NV_DIGEST],
        obs: vec![],
        reads: vec![],
        ctr: 0,
        wit: vec![],
        scnt: 0,
        first: false,
    };
    macro_rules! absorbed {
        ($k:expr) => {{
            state = $k;
            src = SqueezeSrc::Key(state);
            ctr = 0;
            nw = 12;
        }};
    }
    macro_rules! flush {
        () => {{
            if !pending.is_empty() {
                let id = TJOB_STATIC_BASE + n_static;
                n_static += 1;
                let out = hash_parts(TAG_FLUSH, &[&state[..], &felt_bytes(&pending)]);
                let mut jb = blank(id, Op2::Flush, pstart, pending.len(), state, out);
                jb.obs = std::mem::take(&mut pending);
                jobs.push(jb);
                absorbed!(out);
            }
        }};
    }
    let n = log.len();
    let mut i = 0;
    let mut chain_start = 0usize; // jobs.len() at the start of the current chain
    while i < n {
        if i > 0 && starts.contains(&i) {
            flush!();
            state = initial_state();
            src = SqueezeSrc::Key(state);
            ctr = 0;
            nw = 12;
            pow_wit.clear();
            chain_start = jobs.len();
        }
        let before = jobs.len();
        match log.kinds[i] {
            KIND_OBSERVE => {
                if pending.is_empty() {
                    pstart = i;
                }
                pending.push(log.values[i]);
                i += 1;
            }
            KIND_COMMIT => {
                flush!();
                let payload: [F; NV_DIGEST] = log.values[i..i + NV_DIGEST].try_into().unwrap();
                let d = limbs_digest(&payload);
                let out = hash_parts(TAG_COMMIT, &[&state[..], &crate::sha384::config::digest_wire(d)]);
                let id = TJOB_STATIC_BASE + n_static;
                n_static += 1;
                let mut jb = blank(id, Op2::Commit, i, NV_DIGEST, state, out);
                jb.payload = payload;
                jobs.push(jb);
                absorbed!(out);
                i += NV_DIGEST;
            }
            KIND_SAMPLE => {
                flush!();
                assert!(!jobs.is_empty(), "the transcript must absorb before the first challenge");
                loop {
                    if nw == 12 {
                        ctr += 1;
                        let out = src.block(ctr);
                        let mut jb = match &src {
                            SqueezeSrc::Key(k) => {
                                let id = TJOB_SQUEEZE_BASE + n_squeeze;
                                n_squeeze += 1;
                                blank(id, Op2::Squeeze, i, 0, *k, out)
                            }
                            SqueezeSrc::Pow(sg, _) => {
                                let id = TJOB_SQUEEZE_BASE + n_squeeze;
                                n_squeeze += 1;
                                let mut jb = blank(id, Op2::PowQ, i, 0, *sg, out);
                                jb.wit = pow_wit.clone();
                                jb
                            }
                        };
                        jb.ctr = ctr;
                        jobs.push(jb);
                        state = out;
                        nw = 0;
                    }
                    let w = u32::from_le_bytes(state[4 * nw..4 * nw + 4].try_into().unwrap());
                    let acc = (w as u64) < SAMPLE_BOUND;
                    let job = jobs.last_mut().unwrap();
                    job.reads.push(Read2 { wi: nw, n: w, acc });
                    nw += 1;
                    if acc {
                        if job.op == Op2::Pow {
                            job.scnt += 1;
                        } else {
                            job.cnt += 1;
                        }
                        assert_eq!(F::from_u32(w), log.values[i], "replay disagrees at tidx {i}");
                        break;
                    }
                }
                i += 1;
            }
            KIND_POW => {
                flush!();
                let mut w = vec![log.values[i]];
                let mut j = i + 1;
                while j < n && log.kinds[j] == KIND_POW_CONT {
                    w.push(log.values[j]);
                    j += 1;
                }
                let wb = felt_bytes(&w);
                let mut m = wb.clone();
                m.extend_from_slice(&1u32.to_le_bytes());
                let out = hash_parts(TAG_POW, &[&state[..], &m]);
                let id = TJOB_STATIC_BASE + n_static;
                n_static += 1;
                let mut jb = blank(id, Op2::Pow, i, w.len(), state, out);
                jb.ctr = 1;
                jb.wit = w.clone();
                jobs.push(jb);
                src = SqueezeSrc::Pow(state, wb);
                ctr = 1;
                pow_wit = w;
                state = out;
                // challenges start after the PoW bits (bits <= 64: the first 64-bit word)
                nw = pow_skip_words(1);
                i = j;
            }
            k => panic!("bad kind {k}"),
        }
        if before == chain_start && jobs.len() > chain_start {
            jobs[chain_start].first = true;
        }
    }
    // a trailing observe run is flushed at the end of the log (the ALU closes it)
    assert!(pending.is_empty());
    if let Some(j) = jobs.first_mut() {
        j.first = true;
    }
    jobs
}

// ---------------------------------------------------------------------------------------
// Hash-chain role: one row per transcript job (gated by the role flag kh)
// ---------------------------------------------------------------------------------------

#[repr(C)]
#[derive(AlignedBorrow, Debug)]
pub struct Hash2Cols<T> {
    pub is_first: T,
    pub op_f: T,
    pub op_c: T,
    pub op_s: T,
    /// PoW block B_1 (tag 7, anchored)
    pub op_p: T,
    /// PoW-run block B_j, j >= 2 (tag 7)
    pub op_q: T,
    pub job: T,
    /// job id of the next row
    pub nxt: T,
    /// has a next job
    pub hn: T,
    pub t_start: T,
    /// observe / commit / PoW-witness count (anchored), or accepted samples (op_s, op_q)
    pub cnt: T,
    /// accepted samples read from B_1 (op_p only)
    pub scnt: T,
    /// T* block counter j (op_s, op_p, op_q)
    pub ctr: T,
    /// PoW witness felts (op_p = cnt, op_q = inherited)
    pub nwit: T,
    /// this row's block is read by the sample role
    pub rd: T,
    /// the next row is a squeeze / PoW-run block (= next.op_s + next.op_q)
    pub nsq: T,
    /// the next row is a PoW-run block (= next.op_q)
    pub nq: T,
    /// PoW witness felts (op_p / op_q: units 16, 17 of the block, sent by this row; zero
    /// elsewhere): the PoW blocks are proof-shaped, so nothing of them is in the ALU program
    pub w: [T; 2],
    /// input state units (key kappa for op_s, sigma for op_p / op_q, previous state otherwise)
    pub state_in: [T; NV_DIGEST],
    pub state_out: [T; NV_DIGEST],
    /// state words read by the sample role (prefix from word 0, or from word 1 for op_p)
    pub rdw: [T; 6],
    pub last_word: T,
    pub last_half: T,
    pub last_acc: T,
    /// = rdw[5] * last_half (all 12 candidates read)
    pub full: T,
    /// squeeze / PoW-run blocks before this row (their job ids are TJOB_SQUEEZE_BASE + ns: unique)
    pub ns: T,
}
pub const HASH2_WIDTH: usize = Hash2Cols::<u8>::width();

pub fn eval_hash<AB: AirBuilder + InteractionBuilder>(
    builder: &mut AB,
    l: &Hash2Cols<AB::Var>,
    n: &Hash2Cols<AB::Var>,
    kh: AB::Expr,
    nkh: AB::Expr,
    h: &HashBuses,
    t: &TrBuses,
) {
    let one = AB::Expr::ONE;
    let c = |v: u64| AB::Expr::from_u64(v);
    let g = |x: AB::Expr| kh.clone() * x;
    for x in [l.is_first, l.op_f, l.op_c, l.op_s, l.op_p, l.op_q, l.last_acc, l.last_half, l.hn, l.rd].into_iter().chain(l.rdw) {
        builder.assert_zero(g(x * (x - one.clone())));
    }
    let sq: AB::Expr = l.op_s + l.op_q; // blocks read from word 0
    let pw: AB::Expr = l.op_p + l.op_q; // tag-7 blocks
    builder.assert_zero(g(l.op_f + l.op_c + l.op_s + l.op_p + l.op_q - one.clone()));
    // [agg] chain starts may occur on any row; their t_start is pinned by the anchor
    builder.assert_zero(g(l.is_first * sq.clone()));
    // squeeze and PoW-run job ids are pinned (unique, disjoint from leaf / node / static ids):
    // without this a prover could give two jobs one id and mix their units / words (audit B5)
    builder.assert_zero(g(l.is_first * l.ns));
    builder.assert_zero(g(sq.clone() * (l.job - c(TJOB_SQUEEZE_BASE as u64) - l.ns)));
    let init = state_limbs(&initial_state());
    for i in 0..NV_DIGEST {
        builder.assert_zero(g(l.is_first * (l.state_in[i] - c(init[i] as u64))));
    }
    builder.assert_zero(g(l.op_c * (l.cnt - c(NV_DIGEST as u64))));
    builder.assert_zero(g(l.op_p * (l.ctr - one.clone())));
    builder.assert_zero(g(l.op_p * (l.nwit - l.cnt)));
    builder.assert_zero(g(l.scnt * (one.clone() - l.op_p)));
    // reads: squeeze-type blocks from word 0, B_1 from word 1 (its word 0 holds the PoW bits)
    builder.assert_zero(g(l.rd - sq.clone() - l.op_p * l.rdw[1]));
    builder.assert_zero(g(l.rdw[0] - sq.clone()));
    builder.assert_zero(g(l.rdw[1] * (one.clone() - l.rdw[0] - l.op_p)));
    for i in 1..5 {
        builder.assert_zero(g(l.rdw[i + 1] * (one.clone() - l.rdw[i])));
    }
    let rd_sum = l.rdw.iter().fold(AB::Expr::ZERO, |a, &x| a + x);
    builder.assert_zero(g(rd_sum - l.last_word - sq.clone()));
    builder.assert_zero(g(l.last_acc * (one.clone() - l.rd)));
    builder.assert_zero(g(l.last_half * (one.clone() - l.rd)));
    builder.assert_zero(g(l.full - l.rdw[5] * l.last_half));
    let rej = l.rd - l.last_acc;
    builder.assert_zero(g(rej.clone() * (one.clone() - l.full)));
    builder.when_first_row().assert_zero(g(one.clone() - l.is_first));
    {
        let mut tr = builder.when_transition();
        let both = kh.clone() * nkh.clone();
        tr.assert_zero(nkh.clone() * (one.clone() - kh.clone()) * (one.clone() - n.is_first));
        // [agg] a row has a next job unless the next row starts a new chain
        tr.assert_zero(kh.clone() * (l.hn - nkh.clone() * (one.clone() - n.is_first)));
        tr.assert_zero(both.clone() * (n.job - l.nxt));
        tr.assert_zero(both.clone() * (n.t_start - l.t_start - l.cnt - l.scnt));
        tr.assert_zero(both.clone() * (n.ns - l.ns - l.op_s - l.op_q));
        tr.assert_zero(both.clone() * l.op_f * n.op_f);
        tr.assert_zero(kh.clone() * l.op_f * (one.clone() - l.hn));
        // a squeeze block follows an absorb or a fully read squeeze block (same key)
        tr.assert_zero(both.clone() * n.op_s * (l.op_p + l.op_q));
        tr.assert_zero(both.clone() * n.op_s * l.op_s * (one.clone() - l.full));
        // a PoW-run block follows a fully read PoW block of the same run
        tr.assert_zero(both.clone() * n.op_q * (one.clone() - l.full));
        tr.assert_zero(both.clone() * n.op_q * (l.op_f + l.op_c + l.op_s));
        tr.assert_zero(kh.clone() * rej.clone() * (one.clone() - nkh.clone() * (n.op_s + n.op_q)));
        // counters: squeeze j = 1 after an absorb, else j + 1; PoW-run j + 1
        tr.assert_zero(both.clone() * n.op_s * (n.ctr - one.clone() - l.op_s * l.ctr));
        tr.assert_zero(both.clone() * n.op_q * (n.ctr - l.ctr - one.clone()));
        tr.assert_zero(both.clone() * n.op_q * (n.nwit - l.nwit));
        tr.assert_zero(both.clone() * (l.nsq - n.op_s - n.op_q));
        tr.assert_zero(both.clone() * (l.nq - n.op_q));
    }
    builder.assert_zero(g(l.nsq * (one.clone() - l.hn)));
    builder.when_last_row().assert_zero(g(l.op_f.into()));
    builder.when_last_row().assert_zero(g(rej));
    builder.when_last_row().assert_zero(g(l.hn.into()));

    let tag = l.op_f * c(TAG_FLUSH as u64)
        + l.op_c * c(TAG_COMMIT as u64)
        + l.op_s * c(TAG_SQUEEZE as u64)
        + pw.clone() * c(crate::sha384::config::TAG_POW as u64);
    h.send_job(builder, l.job, tag.clone(), kh.clone());
    h.send_felt(builder, l.job, c(0), c(48), kh.clone());
    h.send_felt(builder, l.job, c(1), c(0), kh.clone());
    for i in 0..6 {
        h.send_word(
            builder,
            l.job,
            c(2 + 2 * i as u64),
            core::array::from_fn(|k| l.state_in[3 * i + k].into()),
            kh.clone(),
        );
    }
    let len = l.op_c * c(crate::sha384::config::sha_levers().digest_bytes as u64)
        + l.op_f * l.cnt * c(4)
        + pw.clone() * (l.nwit + one.clone()) * c(4)
        + l.op_s * c(4);
    h.send_felt(builder, l.job, c(14), len, kh.clone());
    h.send_felt(builder, l.job, c(15), c(0), kh.clone());
    // the block counter: unit 16 (squeeze) or 16 + nwit (after the PoW witness units)
    h.send_felt(builder, l.job, c(16) + pw.clone() * l.nwit, l.ctr, g(l.op_s + pw.clone()));
    // the PoW witness: units 16 (and 17 when nwit = 2) of every PoW block, sent here (gap G1:
    // the number of PoW-run blocks depends on the proof, so their units cannot come from the
    // program). B_1's witness is free (any w with leading-zero B_1 is valid); the run's later
    // blocks carry the same w (chain bus below).
    builder.assert_zero(g(pw.clone() * (l.nwit - one.clone()) * (l.nwit - c(2))));
    builder.assert_zero(g(pw.clone() * (c(2) - l.nwit) * l.w[1]));
    for t in 0..2 {
        builder.assert_zero(g((one.clone() - pw.clone()) * l.w[t]));
    }
    h.send_felt(builder, l.job, c(16), l.w[0], g(pw.clone()));
    h.send_felt(builder, l.job, c(17), l.w[1], g(pw.clone() * (l.nwit - one.clone())));
    builder.assert_zero(g(l.nq * (l.nq - one.clone())));
    builder.assert_zero(g(l.nq * (one.clone() - l.hn)));
    // PoW jobs: B_1's word 0 (limbs) goes to the ALU's leading-zero check
    PermutationCheckBus::new(h.slot).send(
        builder,
        [
            c(SLOT_POW as u64),
            l.job.into(),
            AB::Expr::ZERO,
            AB::Expr::ZERO,
            l.state_out[0].into(),
            l.state_out[1].into(),
            l.state_out[2].into(),
        ],
        g(l.op_p.into()),
    );
    let sout: Vec<AB::Expr> = l.state_out.iter().map(|&x| x.into()).collect();
    h.receive_digest(builder, l.job, &sout, kh.clone());
    // hash chain: the next job's input state = the key / sigma within a run (squeeze after
    // squeeze, PoW-run block), else this block's output (the last block consumed)
    let keep = l.nsq * (l.op_s + l.op_p + l.op_q);
    let chain = PermutationCheckBus::new(t.chain);
    chain.send(
        builder,
        core::iter::once(l.nxt.into())
            .chain((0..NV_DIGEST).map(|i| l.state_out[i] + keep.clone() * (l.state_in[i] - l.state_out[i])))
            .chain((0..2).map(|t| l.nq * l.w[t]))
            .collect::<Vec<AB::Expr>>(),
        g(l.hn.into()),
    );
    chain.receive(
        builder,
        core::iter::once(l.job.into())
            .chain(l.state_in.iter().map(|&x| x.into()))
            .chain((0..2).map(|t| l.op_q * l.w[t]))
            .collect::<Vec<AB::Expr>>(),
        g(one.clone() - l.is_first),
    );
    // flush / commit / PoW jobs are anchored by the ALU: (2, job, 0, 0, t_start, cnt, tag); the tag
    // binds the job's op to the program (otherwise a commit could be relabeled as a flush, audit B6)
    PermutationCheckBus::new(h.slot).receive(
        builder,
        [
            c(SLOT_ANCHOR as u64),
            l.job.into(),
            AB::Expr::ZERO,
            AB::Expr::ZERO,
            l.t_start.into(),
            l.cnt.into(),
            // [agg] the anchor's k2 carries the hash tag in its low bits (binds the job's op
            // to the program, audit B6) and the chain-start flag at ANCHOR_FIRST_BIT, so one
            // bus term declares both.  `is_first` is read below as bit ANCHOR_FIRST_BIT.
            tag.clone() + l.is_first * c(1u64 << super::builder::ANCHOR_FIRST_BIT),
        ],
        g(l.op_f + l.op_c + l.op_p),
    );
    PermutationCheckBus::new(t.sample).receive(
        builder,
        [
            l.job.into(),
            l.t_start + l.op_p * l.cnt,
            sq * l.cnt + l.op_p * l.scnt,
            l.last_word.into(),
            l.last_half.into(),
            l.last_acc.into(),
            l.op_p.into(),
        ],
        g(l.rd.into()),
    );
    // the words read by the sample role come from GLUE's digest rows (digest bus, word keys
    // 8 + w); this row pins the run (t.sample: job, start, count, last word / half / accept)
}

// ---------------------------------------------------------------------------------------
// Sample role: one row per state word, two candidates (gated by ks)
// ---------------------------------------------------------------------------------------

#[repr(C)]
#[derive(AlignedBorrow, Debug)]
pub struct Samp2Cols<T> {
    pub job: T,
    /// word index 0..5
    pub wi: T,
    pub t_job: T,
    /// accepted samples in the run before this row
    pub mbefore: T,
    /// first word of the run (0: squeeze / PoW-run block, 1: B_1 after a PoW); constant in a run
    pub w0: T,
    pub is_first: T,
    pub is_last: T,
    /// big-endian bytes of the state word; candidate 0 = LE(b0..b3), 1 = LE(b4..b7)
    pub b: [T; 8],
    pub lo5: T,
    pub lo2: T,
    /// candidate 1 read
    pub h1: T,
    /// per candidate: c3 >= 0xF0, is_zero(c3 - 0xF0) + inv, is_zero(v) + inv, is_zero(c0(c0-1)) + inv, acc
    pub g: [T; 2],
    pub z: [T; 2],
    pub iz: [T; 2],
    pub zv: [T; 2],
    pub iv: [T; 2],
    pub zc: [T; 2],
    pub ic: [T; 2],
    pub acc: [T; 2],
}
pub const SAMP2_WIDTH: usize = Samp2Cols::<u8>::width();

pub fn eval_samp<AB: AirBuilder + InteractionBuilder>(
    builder: &mut AB,
    l: &Samp2Cols<AB::Var>,
    n: &Samp2Cols<AB::Var>,
    ks: AB::Expr,
    nks: AB::Expr,
    hb: &HashBuses,
    t: &TrBuses,
) {
    let one = AB::Expr::ONE;
    let c = |v: u64| AB::Expr::from_u64(v);
    let g = |x: AB::Expr| ks.clone() * x;
    // runs (per squeeze job): is_first .. is_last
    for x in [l.is_first, l.is_last, l.h1, l.w0].into_iter().chain(l.g) {
        builder.assert_zero(g(x * (x - one.clone())));
    }
    builder.when_first_row().assert_zero(g(one.clone() - l.is_first));
    builder.when_last_row().assert_zero(g(one.clone() - l.is_last));
    {
        let mut tr = builder.when_transition();
        tr.assert_zero(nks.clone() * (one.clone() - ks.clone()) * (one.clone() - n.is_first));
        tr.assert_zero(nks.clone() * ks.clone() * (n.is_first - l.is_last));
        tr.assert_zero(ks.clone() * (one.clone() - nks.clone()) * (one.clone() - l.is_last));
    }
    // only the last row may skip candidate 1
    builder.assert_zero(g((one.clone() - l.h1) * (one.clone() - l.is_last)));
    // a run starts at word 0 (squeeze blocks) or word 1 (B_1 after a PoW); the word bus pins it
    builder.assert_zero(g(l.is_first * (l.wi - l.w0)));
    builder.assert_zero(g(l.is_first * l.mbefore));
    let macc = l.mbefore + l.acc[0] + l.h1 * l.acc[1];
    {
        let mut tr = builder.when_transition();
        let same = ks.clone() * nks.clone() * (one.clone() - n.is_first);
        tr.assert_zero(same.clone() * (n.job - l.job));
        tr.assert_zero(same.clone() * (n.wi - l.wi - one.clone()));
        tr.assert_zero(same.clone() * (n.t_job - l.t_job));
        tr.assert_zero(same.clone() * (n.w0 - l.w0));
        tr.assert_zero(same * (n.mbefore - macc.clone()));
    }
    use super::hash::lookup_pair;
    for k in 0..4 {
        lookup_pair(builder, hb.byte, l.b[2 * k], l.b[2 * k + 1], ks.clone());
    }
    let (a5, a2) = split_bits();
    lookup_pair(builder, hb.byte, l.lo5 * c(1 << (8 - a5)), l.lo2 * c(1 << (8 - a2)), ks.clone());
    let mut us: Vec<AB::Expr> = vec![];
    let bw: [AB::Expr; 8] = core::array::from_fn(|k| l.b[k].into());
    let [w0, w1, w2] = limbs_from_bytes(&bw, l.lo5.into(), l.lo2.into());
    // the word itself: GLUE's digest row of this job (key 8 + word index; limbs, 0, 0, 0)
    PermutationCheckBus::new(hb.digest).receive(
        builder,
        [l.job.into(), l.wi + c(8), w0, w1, w2, AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO],
        ks.clone(),
    );
    let mut tidx = l.t_job + l.mbefore;
    for h in 0..2usize {
        let cb = [l.b[4 * h], l.b[4 * h + 1], l.b[4 * h + 2], l.b[4 * h + 3]];
        let d3 = cb[3] - c(0xF0);
        builder.assert_zero(g(l.z[h] * d3.clone()));
        builder.assert_zero(g(d3 * l.iz[h] - (one.clone() - l.z[h])));
        let v = cb[1] * c(1 << 8) + cb[2] * c(1 << 16);
        builder.assert_zero(g(l.zv[h] * v.clone()));
        builder.assert_zero(g(v * l.iv[h] - (one.clone() - l.zv[h])));
        let w = cb[0] * cb[0] - cb[0];
        builder.assert_zero(g(l.zc[h] * w.clone()));
        builder.assert_zero(g(w * l.ic[h] - (one.clone() - l.zc[h])));
        builder.assert_zero(g(l.acc[h] - (one.clone() - l.g[h] + l.g[h] * l.z[h] * l.zv[h] * l.zc[h])));
        let u = l.g[h] * (cb[3] - c(0xF0)) + (one.clone() - l.g[h]) * (c(0xEF) - cb[3]);
        us.push(u);
        let value = cb[0] + cb[1] * c(1 << 8) + cb[2] * c(1 << 16) + cb[3] * c(1 << 24);
        let read: AB::Expr = if h == 0 { one.clone() } else { l.h1.into() };
        emit(builder, hb.slot, tidx.clone(), c(KIND_SAMPLE as u64), value, g(l.acc[h] * read));
        tidx = tidx + l.acc[h];
    }
    lookup_pair(builder, hb.byte, us[0].clone(), us[1].clone(), ks.clone());
    PermutationCheckBus::new(t.sample).send(
        builder,
        [l.job.into(), l.t_job.into(), macc, l.wi.into(), l.h1.into(), l.acc[0] + l.h1 * (l.acc[1] - l.acc[0]), l.w0.into()],
        g(l.is_last.into()),
    );
}

// ---------------------------------------------------------------------------------------
// Trace generation
// ---------------------------------------------------------------------------------------

pub struct Tr2Traces {
    pub hash: Vec<[F; HASH2_WIDTH]>,
    pub samp: Vec<[F; SAMP2_WIDTH]>,
    pub byte_counts: Vec<u32>,
}


/// Fill candidate h's gadgets; returns (accepted, u) with u the range-checked byte.
pub(crate) fn fill_cand(s: &mut Samp2Cols<F>, h: usize, cb: [u8; 4]) -> (bool, u8) {
    let g = cb[3] >= 0xF0;
    s.g[h] = F::from_bool(g);
    let u = if g { cb[3] - 0xF0 } else { 0xEF - cb[3] };
    let d3 = F::from_u8(cb[3]) - F::from_u32(0xF0);
    s.z[h] = F::from_bool(d3 == F::ZERO);
    s.iz[h] = if d3 == F::ZERO { F::ZERO } else { d3.inverse() };
    let v = F::from_u32((cb[1] as u32) << 8 | (cb[2] as u32) << 16);
    s.zv[h] = F::from_bool(v == F::ZERO);
    s.iv[h] = if v == F::ZERO { F::ZERO } else { v.inverse() };
    let w = F::from_u32(cb[0] as u32 * cb[0] as u32) - F::from_u8(cb[0]);
    s.zc[h] = F::from_bool(w == F::ZERO);
    s.ic[h] = if w == F::ZERO { F::ZERO } else { w.inverse() };
    let acc = !g || (cb[3] == 0xF0 && cb[1] == 0 && cb[2] == 0 && cb[0] <= 1);
    s.acc[h] = F::from_bool(acc);
    (acc, u)
}

/// Hash-chain and sample role rows (unpadded).
pub fn tr2_traces(jobs: &[TrJob2]) -> Tr2Traces {
    let n_words: usize = jobs.iter().map(|j| j.reads.len().div_ceil(2)).sum();
    let mut hash = F::zero_vec(jobs.len() * HASH2_WIDTH);
    let mut samp = F::zero_vec(n_words * SAMP2_WIDTH);
    let mut counts = vec![0u32; super::hash::BYTE_TABLE];
    let (a5, a2) = split_bits();
    let mut srow = 0usize;
    let mut ns = 0usize;
    let fu = |x: usize| F::from_usize(x);
    for (k, j) in jobs.iter().enumerate() {
        let job = j.id as usize;
        let r: &mut Hash2Cols<F> = hash[k * HASH2_WIDTH..(k + 1) * HASH2_WIDTH].borrow_mut();
        r.is_first = F::from_bool(k == 0 || j.first);
        r.op_f = F::from_bool(j.op == Op2::Flush);
        r.op_c = F::from_bool(j.op == Op2::Commit);
        r.op_s = F::from_bool(j.op == Op2::Squeeze);
        r.op_p = F::from_bool(j.op == Op2::Pow);
        r.op_q = F::from_bool(j.op == Op2::PowQ);
        r.job = fu(job);
        r.t_start = fu(j.t_start);
        r.cnt = fu(j.cnt);
        r.scnt = fu(j.scnt);
        r.ctr = F::from_u32(j.ctr);
        r.nwit = fu(j.wit.len());
        for (t, &x) in j.wit.iter().enumerate() {
            r.w[t] = x;
        }
        r.ns = fu(ns);
        if matches!(j.op, Op2::Squeeze | Op2::PowQ) {
            assert_eq!(j.id, TJOB_SQUEEZE_BASE + ns as u32, "squeeze / PoW-run blocks numbered in chain order");
            ns += 1;
        }
        if k + 1 < jobs.len() {
            r.nxt = F::from_u32(jobs[k + 1].id);
            if !jobs[k + 1].first {
                r.hn = F::ONE;
                r.nsq = F::from_bool(matches!(jobs[k + 1].op, Op2::Squeeze | Op2::PowQ));
                r.nq = F::from_bool(jobs[k + 1].op == Op2::PowQ);
            }
        }
        let si = state_limbs(&j.state_in);
        let so = state_limbs(&j.state_out);
        for i in 0..NV_DIGEST {
            r.state_in[i] = F::from_u32(si[i]);
            r.state_out[i] = F::from_u32(so[i]);
        }
        if let (Some(first), Some(last)) = (j.reads.first(), j.reads.last()) {
            r.rd = F::ONE;
            for i in first.wi / 2..=last.wi / 2 {
                r.rdw[i] = F::ONE;
            }
            r.last_word = fu(last.wi / 2);
            r.last_half = F::from_bool(last.wi % 2 == 1);
            r.last_acc = F::from_bool(last.acc);
            r.full = F::from_bool(last.wi == 11);
        }
        let nrows = j.reads.len().div_ceil(2);
        let w0 = j.reads.first().map_or(0, |r| r.wi / 2);
        debug_assert!(j.reads.first().is_none_or(|r| r.wi % 2 == 0));
        let t_job = j.t_start + if j.op == Op2::Pow { j.cnt } else { 0 };
        let mut mbefore = 0usize;
        let sw = state_words(&j.state_out);
        for q in 0..nrows {
            let wi = w0 + q;
            let s: &mut Samp2Cols<F> = samp[srow * SAMP2_WIDTH..(srow + 1) * SAMP2_WIDTH].borrow_mut();
            srow += 1;
            s.job = fu(job);
            s.wi = fu(wi);
            s.t_job = fu(t_job);
            s.mbefore = fu(mbefore);
            s.w0 = fu(w0);
            s.is_first = F::from_bool(q == 0);
            s.is_last = F::from_bool(q + 1 == nrows);
            let bytes = sw[wi].to_be_bytes();
            for t in 0..8 {
                s.b[t] = F::from_u8(bytes[t]);
            }
            for t in 0..4 {
                super::hash::cnt2(&mut counts, bytes[2 * t] as usize, bytes[2 * t + 1] as usize);
            }
            let lo5 = bytes[5] & ((1 << a5) - 1);
            let lo2 = bytes[2] & ((1 << a2) - 1);
            s.lo5 = F::from_u8(lo5);
            s.lo2 = F::from_u8(lo2);
            super::hash::cnt2(&mut counts, (lo5 as usize) << (8 - a5), (lo2 as usize) << (8 - a2));
            let h1 = 2 * q + 1 < j.reads.len();
            s.h1 = F::from_bool(h1);
            let mut us = [0u8; 2];
            for h in 0..2 {
                let cb = [bytes[4 * h], bytes[4 * h + 1], bytes[4 * h + 2], bytes[4 * h + 3]];
                let (acc, u) = fill_cand(s, h, cb);
                us[h] = u;
                if h == 0 || h1 {
                    debug_assert_eq!(acc, j.reads[2 * q + h].acc);
                    mbefore += acc as usize;
                }
            }
            super::hash::cnt2(&mut counts, us[0] as usize, us[1] as usize);
        }
    }
    let _ = digest_limbs;
    Tr2Traces {
        hash: hash.chunks_exact(HASH2_WIDTH).map(|c| c.try_into().unwrap()).collect(),
        samp: samp.chunks_exact(SAMP2_WIDTH).map(|c| c.try_into().unwrap()).collect(),
        byte_counts: counts,
    }
}

#[allow(dead_code)]
fn _m(m: &RowMajorMatrix<F>) -> usize {
    m.width()
}
