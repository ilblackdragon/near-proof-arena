//! Program builder + executor.  Verifier code calls the builder with concrete values; each
//! call appends a fixed instruction (independent of the values, by construction) and
//! computes its result, so one pass yields the program and the full ALU witness.
use std::collections::HashMap;

use openvm_stark_backend::FiatShamirTranscript;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};

use super::isa::{Instr, Op, ADDR_BITS};

/// [agg] Bit of the Anchor `k2` field that marks a transcript chain start (every hash tag is
/// < 16, so the low bits stay the tag).
pub const ANCHOR_FIRST_BIT: u32 = 8;
use super::fmt::{digest_limbs, limbs_digest, NV_DIGEST};
use super::hash::{Job2, NODE_TAG, U2};
use crate::sha384::config::{
    digest_words, Digest, Sha384Config, ShaTranscript, ShaTranscriptLog, KIND_COMMIT, KIND_OBSERVE,
    KIND_SAMPLE, EF, F,
};

/// Transcript recorder with NV event granularity: a commitment is NV_DIGEST limb events.
#[derive(Clone, Debug, Default)]
pub struct NvRecorder {
    pub inner: ShaTranscript,
    pub values: Vec<F>,
    pub kinds: Vec<u32>,
    /// [agg] tidx at which a fresh transcript chain starts (besides 0)
    pub starts: Vec<usize>,
}
impl NvRecorder {
    pub fn into_log(self) -> ShaTranscriptLog {
        ShaTranscriptLog {
            values: self.values,
            kinds: self.kinds,
        }
    }
}
impl FiatShamirTranscript<Sha384Config> for NvRecorder {
    fn observe(&mut self, v: F) {
        self.inner.observe(v);
        self.values.push(v);
        self.kinds.push(KIND_OBSERVE);
    }
    fn observe_commit(&mut self, d: Digest) {
        self.inner.observe_commit(d);
        self.values.extend(digest_limbs(d));
        self.kinds.extend([KIND_COMMIT; NV_DIGEST]);
    }
    fn sample(&mut self) -> F {
        let s = self.inner.sample();
        self.values.push(s);
        self.kinds.push(KIND_SAMPLE);
        s
    }
    fn check_witness(&mut self, bits: usize, witness: F) -> bool {
        if bits == 0 {
            return self.inner.check_witness(0, witness);
        }
        self.values.push(witness);
        self.kinds.push(crate::sha384::config::KIND_POW);
        self.inner.check_witness(bits, witness)
    }
    fn check_witness_wide(&mut self, bits: usize, w: [F; 2]) -> bool {
        if bits == 0 {
            return self.inner.check_witness_wide(0, w);
        }
        self.values.extend(w);
        self.kinds.extend([crate::sha384::config::KIND_POW, crate::sha384::config::KIND_POW_CONT]);
        self.inner.check_witness_wide(bits, w)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct V {
    pub addr: u32,
    pub val: EF,
}

/// A digest held in two ALU cells: lo = words 0..3 (12 limbs), hi = words 4, 5 (6 limbs).
#[derive(Clone, Copy, Debug)]
pub struct DigestCells {
    pub lo: V,
    pub hi: V,
    pub digest: Digest,
}

/// A digest as two cells: words 0..3 (12 limbs) and words 4, 5 (6 limbs, rest zero).
pub fn digest_cells(d: Digest) -> ([F; 12], [F; 12]) {
    let l = digest_limbs(d);
    let mut lo = [F::ZERO; 12];
    let mut hi = [F::ZERO; 12];
    lo.copy_from_slice(&l[..12]);
    hi[..6].copy_from_slice(&l[12..]);
    (lo, hi)
}

/// A job under construction.
#[derive(Clone, Debug)]
pub struct BJob {
    pub tag: u8,
    pub node: bool,
    pub units: Vec<Option<U2>>,
}

pub fn coeffs(x: EF) -> [F; 12] {
    x.as_basis_coefficients_slice().try_into().unwrap()
}
pub fn ef_from(c: [F; 12]) -> EF {
    EF::from_basis_coefficients_slice(&c).unwrap()
}

pub struct Builder {
    pub instrs: Vec<Instr>,
    pub vals: Vec<EF>,
    pub wits: Vec<F>,
    /// Horn2 rows: their second and third base witnesses
    pub wits_x: std::collections::BTreeMap<usize, F>,
    /// rows [0, reserved) are filled at the end (binding tables)
    pub reserved: usize,
    consts: HashMap<u32, u32>,
    pub transcript: NvRecorder,
    pub failures: Vec<String>,
    pub job_units: Vec<BJob>,
    /// Merkle node jobs (statistics)
    pub merkle_nodes: usize,
    pub log_rows: usize,
    /// program length 2^prog_log (ALU rows of NvAir)
    pub prog_log: usize,
    /// deferred binding check: (sub row, zero row, child program evaluation)
    pub acc_check: Option<(u32, u32, EF)>,
    pub acc_flag: Option<EF>,
    /// instructions re-evaluated at finish (they read the ACC / ACC2 rows); the last is a Zero
    pub late: Vec<usize>,
    /// addresses of the ACC2 / ACC rows (allocated by `begin`, right after the data region)
    pub acc_slots: Option<(u32, u32)>,
    /// debug: batch point and the child's per-trace openings
    pub dbg_rs: Vec<EF>,
    pub dbg_openings: Vec<Vec<EF>>,
    pub dbg_tid: Vec<usize>,
    /// bind the child's ALU program (air 0) to this program
    pub bind: bool,
    /// own recursion level (public value of the ALU AIR)
    pub level: u32,
    /// exposed statement digest (public values 1..19; final-soundness G1)
    pub statement: Option<Digest>,
    /// the child is an NV proof (statement passthrough even without program binding)
    pub child_nv: bool,
    /// G2 anchor (M, C_M): a child at level M is bound by its cached program root = C_M, the
    /// setup commitment of the level-M program; a child at any other level by BIND (child
    /// program = own).  M = 1 while the program has converged by level 2; with tight heights the
    /// program depends on the child's committed heights, so M is the last level whose program
    /// differs from the converged one (levels <= M each anchor at their own child level).
    pub anchor: Option<(u32, Digest)>,
    /// open flush job (job id, t_start, observed felts)
    tr_pending: Option<(u32, u32, u32)>,
    /// static transcript jobs allocated so far
    tr_static: u32,
    tr_started: bool,
    /// witness cells of the last PoW (pushed into every later block of its run, T*)
    pow_wit: Vec<V>,
    /// squeeze / PoW-run blocks so far (their job ids)
    tr_blocks: u32,
    /// [agg] the next allocated transcript job starts a chain
    start_pending: bool,
    /// [agg] a chain opened by `restart_transcript` still needs its `ChainStart` row
    chain_pending: bool,
    /// [agg] the static job that starts the current chain
    chain_first: Option<u32>,
    /// [agg] build_verifier leaves level / statement exposure to the caller
    pub agg: bool,
    /// [agg] bind the child's program (set for NV children of an aggregation node; `agg` alone
    /// suppresses the level/statement exposure, this enables the program binding specifically)
    pub bind_child: bool,
}

impl Builder {
    pub fn new(log_rows: usize, reserved: usize) -> Self {
        // log_rows = UAIR height H; the program occupies the ALU half (2^(H-1) rows)
        assert!(log_rows - 1 <= ADDR_BITS as usize);
        Self {
            instrs: vec![Instr::NOP; reserved],
            vals: vec![EF::ZERO; reserved],
            wits: vec![F::ZERO; reserved],
            wits_x: Default::default(),
            reserved,
            consts: HashMap::new(),
            transcript: NvRecorder::default(),
            failures: vec![],
            job_units: vec![],
            merkle_nodes: 0,
            log_rows,
            prog_log: log_rows - 1,
            acc_check: None,
            acc_flag: None,
            late: vec![],
            acc_slots: None,
            dbg_rs: vec![],
            dbg_openings: vec![],
            dbg_tid: vec![],
            bind: false,
            level: 0,
            statement: None,
            child_nv: false,
            anchor: None,
            tr_pending: None,
            tr_static: 0,
            tr_started: false,
            pow_wit: vec![],
            tr_blocks: 0,
            start_pending: true,
            chain_pending: true,
            chain_first: None,
            agg: false,
            bind_child: false,
        }
    }

    /// Program length (ALU rows of the UAIR) = 2^(log_rows - 1).
    pub fn prog_len(&self) -> usize {
        1usize << self.prog_log
    }

    /// Fill reserved row `row` with c = x * y.
    pub fn set_reserved_mul(&mut self, row: usize, x: V, y: V) -> V {
        assert!(row < self.reserved);
        self.instrs[row] = Instr {
            op: Op::Mul,
            a: x.addr,
            b: y.addr,
            k1: 0,
            k2: 0,
        };
        self.vals[row] = x.val * y.val;
        V {
            addr: row as u32,
            val: self.vals[row],
        }
    }

    /// Expose the statement digest held in cells (lo, hi) as public values 1..19.
    pub fn pv_digest(&mut self, d: &DigestCells) {
        self.statement = Some(d.digest);
        self.push(Op::PvD, d.lo.addr, 0, 0, 0, d.lo.val, F::ZERO);
        self.push(Op::PvD, d.hi.addr, 0, 1, 0, d.hi.val, F::ZERO);
    }
    /// NvAir public values: [level, statement digest limbs] (zeros if no digest is exposed).
    pub fn public_values(&self) -> Vec<F> {
        let mut v = vec![F::from_u32(self.level)];
        match self.statement {
            Some(d) => {
                let (lo, hi) = digest_cells(d);
                v.extend_from_slice(&lo);
                v.extend_from_slice(&hi[..6]);
            }
            None => v.extend([F::ZERO; NV_DIGEST]),
        }
        v
    }
    /// One base-field cell as unit `uidx` of leaf job `job`.
    pub fn unit1(&mut self, x: V, job: u32, uidx: u32) -> V {
        let c = coeffs(x.val);
        debug_assert!(c[1..].iter().all(|v| *v == F::ZERO));
        self.job_unit(job, uidx, c[0]);
        self.push(Op::Unit1, x.addr, 0, job, uidx, x.val, F::ZERO)
    }
    pub fn pv_level(&mut self, x: V) {
        self.level = coeffs(x.val)[0].as_canonical_u32();
        self.push(Op::Pv, x.addr, 0, 0, 0, x.val, F::ZERO);
    }

    /// Allocate the ACC2 / ACC rows at fixed addresses (after reserved rows and the data region).
    pub fn begin(&mut self) {
        assert!(self.acc_slots.is_none());
        let a2 = self.instrs.len() as u32;
        for _ in 0..2 {
            self.instrs.push(Instr::NOP);
            self.vals.push(EF::ZERO);
            self.wits.push(F::ZERO);
        }
        self.acc_slots = Some((a2, a2 + 1));
    }

    /// Program binding check, evaluated at finish (ACC = own binding total at row L-1):
    /// flag * (own - phat) == 0.  (A level-1 child, flag = 0, is pinned by its cached root C_L1.)
    pub fn defer_acc_check(&mut self, phat: V, flag: V) {
        let (_l2, l1) = self.acc_slots.expect("Builder::begin not called");
        let mut late = vec![];
        let mut op = |b: &mut Self, o: Op, x: u32, y: u32| -> u32 {
            let v = b.push(o, x, y, 0, 0, EF::ZERO, F::ZERO);
            late.push(v.addr as usize);
            v.addr
        };
        let d = op(self, Op::Sub, l1, phat.addr);
        let g = op(self, Op::Mul, d, flag.addr);
        op(self, Op::Zero, g, 0);
        self.late = late;
        self.acc_flag = Some(flag.val);
        let _ = &self.acc_check;
    }

    fn push(&mut self, op: Op, a: u32, b: u32, k1: u32, k2: u32, val: EF, wit: F) -> V {
        let addr = self.instrs.len() as u32;
        assert!(
            (addr as usize) < self.prog_len() - 2,
            "program exceeds 2^{} rows",
            self.prog_log
        );
        self.instrs.push(Instr { op, a, b, k1, k2 });
        self.vals.push(val);
        self.wits.push(wit);
        V { addr, val }
    }

    pub fn tidx(&self) -> u32 {
        self.transcript.values.len() as u32
    }

    // ---- arithmetic ----
    pub fn mul(&mut self, x: V, y: V) -> V {
        self.push(Op::Mul, x.addr, y.addr, 0, 0, x.val * y.val, F::ZERO)
    }
    pub fn add(&mut self, x: V, y: V) -> V {
        self.push(Op::Add, x.addr, y.addr, 0, 0, x.val + y.val, F::ZERO)
    }
    pub fn sub(&mut self, x: V, y: V) -> V {
        self.push(Op::Sub, x.addr, y.addr, 0, 0, x.val - y.val, F::ZERO)
    }
    pub fn dbl_add(&mut self, x: V, y: V) -> V {
        self.push(Op::DblAdd, x.addr, y.addr, 0, 0, x.val.double() + y.val, F::ZERO)
    }
    /// sum_i coeffs[i] x^i by a Horner chain: HornS, HornR per further coefficient, HornE
    /// (n + 1 rows for n coefficients, instead of 2n).
    pub fn horner_chain(&mut self, coeffs: &[V], x: V) -> V {
        let n = coeffs.len();
        if n == 1 {
            return coeffs[0];
        }
        let top = coeffs[n - 1];
        self.push(Op::HornS, top.addr, 0, 0, 0, top.val, F::ZERO);
        let mut acc = top.val;
        for i in (0..n - 1).rev() {
            let c = coeffs[i];
            self.push(Op::HornR, c.addr, x.addr, 0, 0, acc, F::ZERO);
            acc = acc * x.val + c.val;
        }
        self.push(Op::HornE, 0, 0, 0, 0, acc, F::ZERO)
    }
    pub fn mul_add_a(&mut self, x: V, y: V) -> V {
        self.push(Op::MulAddA, x.addr, y.addr, 0, 0, x.val * y.val + x.val, F::ZERO)
    }
    pub fn neg(&mut self, x: V) -> V {
        let z = self.c(F::ZERO);
        self.sub(z, x)
    }
    pub fn square(&mut self, x: V) -> V {
        self.mul(x, x)
    }
    /// Base constant (deduplicated).
    pub fn c(&mut self, x: F) -> V {
        let k = x.as_canonical_u32();
        if let Some(&addr) = self.consts.get(&k) {
            return V {
                addr,
                val: EF::from(x),
            };
        }
        let v = self.push(Op::Const, k, 0, 0, 0, EF::from(x), F::ZERO);
        self.consts.insert(k, v.addr);
        v
    }
    pub fn cu(&mut self, x: u64) -> V {
        self.c(F::from_u64(x))
    }
    /// Extension constant via Horner in X.
    pub fn ce(&mut self, x: EF) -> V {
        let cs = coeffs(x);
        if cs[1..].iter().all(|c| *c == F::ZERO) {
            return self.c(cs[0]);
        }
        let xv = {
            let mut c = [F::ZERO; 12];
            c[1] = F::ONE;
            self.push(Op::ConstX, 1, 0, 0, 0, ef_from(c), F::ZERO)
        };
        let mut acc = self.c(cs[11]);
        for k in (0..11).rev() {
            let t = self.mul(acc, xv);
            let ck = self.c(cs[k]);
            acc = self.add(t, ck);
        }
        debug_assert_eq!(acc.val, x);
        acc
    }
    pub fn mul_c(&mut self, x: V, k: F) -> V {
        let kv = self.c(k);
        self.mul(x, kv)
    }
    pub fn add_c(&mut self, x: V, k: F) -> V {
        let kv = self.c(k);
        self.add(x, kv)
    }
    pub fn one_minus(&mut self, x: V) -> V {
        let one = self.c(F::ONE);
        self.sub(one, x)
    }

    // ---- assertions ----
    pub fn zero(&mut self, x: V, what: &str) {
        if x.val != EF::ZERO {
            self.failures.push(what.to_string());
        }
        self.push(Op::Zero, x.addr, 0, 0, 0, EF::ZERO, F::ZERO);
    }
    pub fn assert_eq(&mut self, x: V, y: V, what: &str) {
        let d = self.sub(x, y);
        self.zero(d, what);
    }

    // ---- witness / transcript ----
    pub fn load(&mut self, x: EF) -> V {
        self.push(Op::Load, 0, 0, 0, 0, x, F::ZERO)
    }
    /// A witness bit in one row (LoadBit: c0 in {0,1}, other coefficients zero).
    pub fn load_bit(&mut self, bit: bool) -> V {
        self.push(Op::LoadBit, 0, 0, 0, 0, EF::from(F::from_bool(bit)), F::ZERO)
    }
    /// A base-field witness (LoadF: c1..c11 = 0).
    pub fn load_f(&mut self, x: F) -> V {
        self.push(Op::LoadF, 0, 0, 0, 0, EF::from(x), F::ZERO)
    }
    /// First transcript job of the chain: push the initial state as its state units 2..13.
    fn tr_first(&mut self, job: u32) {
        // T*: every hash-chain row sends its own input-state units; the first row's are the
        // initial state (constants of the hash-chain role)
        self.tr_started = true;
        if self.start_pending {
            self.start_pending = false;
            self.chain_first = Some(job);
            // declare the chain's first job; the initial chain included, so the ALU send and the
            // hash receive have the same count by construction
            self.chain_pending = false;
            self.emit_chain_start(job);
        }
    }
    /// [agg] Value of the Anchor's `k2` field contributed by a chain start: 0 or
    /// `1 << ANCHOR_FIRST_BIT`.
    ///
    /// The anchor's `k2` carries **both** pieces the circuit needs: the low bits are the hash tag
    /// (TAG_FLUSH / TAG_POW / TAG_COMMIT, which binds the job's op to the program, audit B6) and
    /// bit `ANCHOR_FIRST_BIT` is the chain-start flag the hash-chain role reads as `is_first`.
    /// One field, so no extra bus term per anchor; the tag check reads `k2 mod 2^ANCHOR_FIRST_BIT`.
    fn anchor_first(&self, _job: u32) -> u32 {
        0
    }
    /// [agg] Emit the `ChainStart` row declaring static job `job` begins a transcript chain.
    /// A program row (op `ChainStart`, job id in `k1`), not a bit in the anchor's `k2`.
    fn emit_chain_start(&mut self, job: u32) {
        self.push(Op::ChainStart, 0, 0, job, 0, EF::ZERO, F::ZERO);
    }
    /// [agg] Start an independent transcript (the next child's verifier): close the open
    /// flush, reset the sponge to the initial state.  tidx and job ids stay global; the
    /// hash-chain role starts a new chain at the next job (anchored with P3 = 1).
    pub fn restart_transcript(&mut self) {
        self.tr_close();
        self.transcript.inner = ShaTranscript::default();
        let t = self.tidx() as usize;
        self.transcript.starts.push(t);
        self.tr_started = false;
        self.start_pending = true;
        self.chain_pending = true;
        self.pow_wit.clear();
    }
    /// T*: blocks B_j (j >= 2) of a PoW run created by the last sample: push the PoW witness as
    /// their units 16.. (the hash-chain row adds the counter).
    fn tr_pow_blocks(&mut self, _ctr_before: u32) {
        // gap G1: squeeze / PoW-run blocks are proof-shaped (their number depends on sampling
        // rejections), so the program never refers to them; the hash-chain rows carry the PoW
        // witness units themselves
    }
    /// The open flush job (allocated at the first observe of a run): (job, unit index).
    fn tr_obs_slot(&mut self, n: u32) -> (u32, u32) {
        if self.tr_pending.is_none() {
            let job = super::transcript2::TJOB_STATIC_BASE + self.tr_static;
            self.tr_static += 1;
            self.tr_first(job);
            self.tr_pending = Some((job, self.tidx(), 0));
        }
        let p = self.tr_pending.as_mut().unwrap();
        let slot = (p.0, 16 + p.2);
        p.2 += n;
        slot
    }
    /// Close the open flush job: anchor (job, t_start, count).
    fn tr_close(&mut self) {
        if let Some((job, t, cnt)) = self.tr_pending.take() {
            let p3 = crate::sha384::config::TAG_FLUSH as u32 + self.anchor_first(job);
            self.push(Op::Anchor, t, cnt, job, p3, EF::ZERO, F::ZERO);
        }
    }
    /// Proof-of-work check (levers spec, tag 7): flush; job H(7, [state, witness]) with the
    /// witness elements as units; the ALU receives the output's word 0 (limbs) and checks that
    /// its top `bits` bits are zero (low limb free; the kept low bits of limbs 1, 2 recomposed
    /// from BIT rows).
    pub fn pow(&mut self, bits: usize, witness: &[F]) {
        if bits == 0 {
            // G-11: no PoW, the witness must be zero (no transcript event)
            let zero = self.c(F::ZERO);
            for &w in witness {
                let v = self.load_f(w);
                self.assert_eq(v, zero, "zero PoW witness (bits = 0)");
            }
            return;
        }
        self.tr_close();
        let job = super::transcript2::TJOB_STATIC_BASE + self.tr_static;
        self.tr_static += 1;
        self.tr_first(job);
        let t = self.tidx();
        let ok = if witness.len() == 1 {
            FiatShamirTranscript::<Sha384Config>::check_witness(&mut self.transcript, bits, witness[0])
        } else {
            FiatShamirTranscript::<Sha384Config>::check_witness_wide(&mut self.transcript, bits, [witness[0], witness[1]])
        };
        if !ok {
            self.failures.push(format!("pow ({bits} bits)"));
        }
        // The witness units are sent by the hash-chain row of this PoW block, not the program:
        // the number of PoW-run blocks depends on the proof, so their units cannot come from a
        // fixed program instruction (gap G1; see `tr_pow_blocks`).
        let _ = &self.pow_wit;
        let p3 = crate::sha384::config::TAG_POW as u32 + self.anchor_first(job);
        self.push(Op::Anchor, t, witness.len() as u32, job, p3, EF::ZERO, F::ZERO);
        // output word 0 as limbs (l0, l1, l2) from the hash chain
        let state = self.transcript.inner.state;
        let w0 = u64::from_be_bytes(state[..8].try_into().unwrap());
        let l = super::fmt::wl(w0);
        let mut c = [F::ZERO; 12];
        for k in 0..3 {
            c[k] = F::from_u32(l[k]);
        }
        let cell = self.push(Op::PowChk, 0, 0, job, 0, ef_from(c), F::ZERO);
        // keep = number of low bits of limb k that may be non-zero
        let o = super::fmt::limb_off();
        // the low limb is not range-checked here (free Load): every zero bit must lie in limbs 1, 2
        assert!(bits <= 64 - o[1], "PoW bits {bits} exceed the checked limbs (max {})", 64 - o[1]);
        let mut acc = if !ok && super::verifier::tamper_now(super::verifier::Tamper::PowFreeLimb) {
            // test hook (bug B3 demo): at 3c9d479ab the base-field load was a Load row with free c1..c11, so the low-limb cell
            // can absorb the non-zero top bits of limbs 1, 2 that the BIT rows cannot express
            let mut c = [F::ZERO; 12];
            c[0] = F::from_u32(l[0]);
            for k in 1..3 {
                let free_top = 64usize.saturating_sub(bits);
                let keep = free_top.saturating_sub(o[k]).min(o[k + 1] - o[k]);
                c[k] = F::from_u32(l[k]) - F::from_u32(l[k] & ((1u32 << keep) - 1));
            }
            // same program word as the honest LoadF row; only the witness value carries junk
            self.push(Op::LoadF, 0, 0, 0, 0, ef_from(c), F::ZERO)
        } else {
            self.load_f(F::from_u32(l[0]))
        };
        for k in 1..3 {
            let width = o[k + 1] - o[k];
            let free_top = 64usize.saturating_sub(bits); // bits [0, 64 - bits) may be non-zero
            let keep = free_top.saturating_sub(o[k]).min(width);
            let mut x = self.c(F::ZERO);
            for j in (0..keep).rev() {
                let bc = self.load_bit((l[k] >> j) & 1 == 1);
                x = self.dbl_add(x, bc);
            }
            // x * X^k
            let mut basis = [F::ZERO; 12];
            basis[k] = F::ONE;
            let xk = self.ce(ef_from(basis));
            let term = self.mul(x, xk);
            acc = self.add(acc, term);
        }
        self.assert_eq(acc, cell, "pow leading zero bits");
    }
    pub fn obs1(&mut self, x: V) -> V {
        let c0 = coeffs(x.val)[0];
        debug_assert!(coeffs(x.val)[1..].iter().all(|c| *c == F::ZERO));
        let (job, u) = self.tr_obs_slot(1);
        self.transcript.observe(c0);
        self.push(Op::Unit1, x.addr, 0, job, u, x.val, F::ZERO)
    }
    pub fn obs12(&mut self, x: V) -> V {
        let (job, u) = self.tr_obs_slot(12);
        self.transcript.observe_ext(x.val);
        self.push(Op::Unit12, x.addr, 0, job, u, x.val, F::ZERO)
    }
    pub fn load_obs(&mut self, x: EF) -> V {
        let v = self.load(x);
        self.obs12(v)
    }
    pub fn load_obs_f(&mut self, x: F) -> V {
        let v = self.load_f(x);
        self.obs1(v)
    }
    pub fn smp1(&mut self) -> V {
        self.tr_close();
        if !self.tr_started {
            self.tr_first(super::transcript2::TJOB_SQUEEZE_BASE);
        }
        let t = self.tidx();
        // absorb pending observes first, so the block counter is read after the key is set
        self.transcript.inner.flush();
        let c0 = self.transcript.inner.ctr;
        let s = self.transcript.sample();
        let out = self.push(Op::Smp1, 0, 0, t, 0, EF::from(s), F::ZERO);
        self.tr_pow_blocks(c0);
        out
    }
    pub fn smp12(&mut self) -> V {
        self.tr_close();
        if !self.tr_started {
            self.tr_first(super::transcript2::TJOB_SQUEEZE_BASE);
        }
        let t = self.tidx();
        // absorb pending observes first, so the block counter is read after the key is set
        self.transcript.inner.flush();
        let c0 = self.transcript.inner.ctr;
        let s = FiatShamirTranscript::<crate::sha384::config::Sha384Config>::sample_ext(
            &mut self.transcript,
        );
        let out = self.push(Op::Smp12, 0, 0, t, 0, s, F::ZERO);
        self.tr_pow_blocks(c0);
        out
    }
    /// Load a digest as two cells and observe it as a commitment (24 limb events).
    pub fn load_commit(&mut self, d: Digest) -> DigestCells {
        let (lo, hi) = digest_cells(d);
        let lo = self.load(ef_from(lo));
        let hi = self.load(ef_from(hi));
        self.observe_commit_cells(lo, hi, d)
    }
    /// Constant digest as cells (not observed).
    pub fn const_digest(&mut self, d: Digest) -> DigestCells {
        let (lo, hi) = digest_cells(d);
        let lo = self.ce(ef_from(lo));
        let hi = self.ce(ef_from(hi));
        DigestCells { lo, hi, digest: d }
    }
    /// Constant digest (e.g. the vk pre-hash) as cells, observed as a commitment.
    pub fn const_commit(&mut self, d: Digest) -> DigestCells {
        let (lo, hi) = digest_cells(d);
        let lo = self.ce(ef_from(lo));
        let hi = self.ce(ef_from(hi));
        self.observe_commit_cells(lo, hi, d)
    }
    fn observe_commit_cells(&mut self, lo: V, hi: V, d: Digest) -> DigestCells {
        self.tr_close();
        let job = super::transcript2::TJOB_STATIC_BASE + self.tr_static;
        self.tr_static += 1;
        self.tr_first(job);
        let t = self.tidx();
        FiatShamirTranscript::<crate::sha384::config::Sha384Config>::observe_commit(
            &mut self.transcript,
            d,
        );
        debug_assert_eq!(
            limbs_digest(&[&coeffs(lo.val)[..12], &coeffs(hi.val)[..6]].concat()),
            d
        );
        let lo = self.push(Op::UnitW, lo.addr, 4, job, 16, lo.val, F::ZERO);
        // 42-B digests: word 5 is a 2-byte tail (its own unit kind, see glue.rs)
        let hi = if crate::sha384::config::sha_levers().digest_bytes == 42 {
            self.push(Op::UnitWT, hi.addr, 0, job, 24, hi.val, F::ZERO)
        } else {
            self.push(Op::UnitW, hi.addr, 2, job, 24, hi.val, F::ZERO)
        };
        let p3 = crate::sha384::config::TAG_COMMIT as u32 + self.anchor_first(job);
        self.push(Op::Anchor, t, NV_DIGEST as u32, job, p3, EF::ZERO, F::ZERO);
        DigestCells { lo, hi, digest: d }
    }
    // ---- SHA jobs (leaf messages) ----
    /// Start a leaf job (tag 0) with `nbytes` of payload; returns the job id.
    pub fn job_start(&mut self, tag: u8, nbytes: usize) -> u32 {
        let id = self.job_units.len() as u32;
        assert_eq!(nbytes % 4, 0);
        let mut units = vec![None; 2 + nbytes / 4];
        units[0] = Some(U2::Felt(nbytes as u32));
        units[1] = Some(U2::Felt(0));
        self.job_units.push(BJob { tag, node: false, units });
        self.push(Op::Job, tag as u32, nbytes as u32, id, 0, EF::ZERO, F::ZERO);
        id
    }
    fn job_unit(&mut self, job: u32, uidx: u32, x: F) {
        let slot = &mut self.job_units[job as usize].units[uidx as usize];
        assert!(slot.is_none(), "unit pushed twice");
        *slot = Some(U2::Felt(x.as_canonical_u32()));
    }
    /// The leaf and node jobs (ids 0..), all units filled.
    pub fn jobs(&self) -> Vec<Job2> {
        self.job_units
            .iter()
            .enumerate()
            .map(|(i, j)| {
                let mut units: Vec<U2> = vec![];
                let mut k = 0;
                while k < j.units.len() {
                    let u = j.units[k].expect("missing unit");
                    units.push(u);
                    k += u.nunits();
                }
                Job2 { id: i as u32, node: j.node, tag: j.tag, units, wread: 0 }
            })
            .collect()
    }
    /// Two Horner steps: c = acc mu^2 + w[0] mu + w[1]; w[1], w[0] are units uidx, uidx + 1 of
    /// `job`.
    pub fn horn2(&mut self, acc: V, mu: V, w: [F; 2], job: u32, uidx: u32) -> V {
        self.job_unit(job, uidx, w[1]);
        self.job_unit(job, uidx + 1, w[0]);
        let m = mu.val;
        let val = (acc.val * m + EF::from(w[0])) * m + EF::from(w[1]);
        let v = self.push(Op::Horn2, acc.addr, mu.addr, job, uidx, val, w[0]);
        self.wits_x.insert(v.addr as usize, w[1]);
        v
    }
    /// c = acc * mu + w, where w (a base witness) is also unit `uidx` of `job`.
    pub fn horn(&mut self, acc: V, mu: V, w: F, job: u32, uidx: u32) -> V {
        self.job_unit(job, uidx, w);
        self.push(
            Op::Horn,
            acc.addr,
            mu.addr,
            job,
            uidx,
            acc.val * mu.val + EF::from(w),
            w,
        )
    }
    /// Push the 12 coefficients of x as units uidx..uidx+11 of `job`.
    pub fn unit12(&mut self, x: V, job: u32, uidx: u32) -> V {
        for (k, c) in coeffs(x.val).into_iter().enumerate() {
            self.job_unit(job, uidx + k as u32, c);
        }
        self.push(Op::Unit12, x.addr, 0, job, uidx, x.val, F::ZERO)
    }

    // ---- bits / Merkle keys ----
    pub fn bit(&mut self, x: V, qid: u32, level: u32) -> V {
        let c = coeffs(x.val);
        if !(c[0] == F::ZERO || c[0] == F::ONE) || c[1..].iter().any(|v| *v != F::ZERO) {
            self.failures.push("non-boolean bit".into());
        }
        let _ = (qid, level);
        self.push(Op::Bit, x.addr, 0, 0, 0, x.val, F::ZERO)
    }
    /// Digest of job `job` as cells (Dig ops; the digest bus pairs 0, 1 | 2).
    pub fn dig(&mut self, job: u32, d: Digest) -> DigestCells {
        let (lo, hi) = digest_cells(d);
        let lo = self.push(Op::Dig, 0, 2, job, 0, ef_from(lo), F::ZERO);
        let hi = self.push(Op::Dig, 0, 1, job, 2, ef_from(hi), F::ZERO);
        DigestCells { lo, hi, digest: d }
    }
    /// Merkle node job SHA384(NODE_WORD || l || r) from digest cells; returns its digest.
    pub fn node(&mut self, l: &DigestCells, r: &DigestCells) -> DigestCells {
        use openvm_stark_backend::hasher::MerkleHasher;
        let id = self.job_units.len() as u32;
        let units: Vec<Option<U2>> = super::hash::digest_units(digest_words(l.digest))
            .into_iter()
            .chain(super::hash::digest_units(digest_words(r.digest)))
            .flat_map(|u| [Some(u), None])
            .collect();
        self.job_units.push(BJob { tag: 0, node: true, units });
        self.merkle_nodes += 1;
        self.push(Op::NodeJob, NODE_TAG, 0, id, 0, EF::ZERO, F::ZERO);
        for (i, (c, n)) in [(l.lo, 4u32), (l.hi, 2), (r.lo, 4), (r.hi, 2)].into_iter().enumerate() {
            let u = [0u32, 8, 12, 20][i];
            self.push(Op::UnitW, c.addr, n, id, u, c.val, F::ZERO);
        }
        let d = crate::sha384::config::ShaHasher.compress(l.digest, r.digest);
        self.dig(id, d)
    }
    /// Authentication path: leaf jobs job_base..job_base + 2^k (coset tree), then the
    /// Merkle path with direction bits `bits` (LSB first), checked against `root`.
    pub fn merkle_path(&mut self, job_base: u32, leaf_digests: &[Digest], siblings: &[Digest], bits: &[V], root: &DigestCells) {
        assert_eq!(bits.len(), siblings.len());
        // the current node as (job id, digest); its digest goes from the digest bus straight into
        // the parent's units (DigWS*), so no digest cells per level
        // (coset trees of per-row leaf jobs end in digest cells: the first level reads those)
        let mut cur_cells: Option<DigestCells> = None;
        let (mut cur_job, mut cur_d) = if leaf_digests.len() == 1 {
            (job_base, leaf_digests[0])
        } else {
            let mut layer: Vec<DigestCells> = leaf_digests
                .iter()
                .enumerate()
                .map(|(j, &d)| self.dig(job_base + j as u32, d))
                .collect();
            while layer.len() > 1 {
                layer = (0..layer.len() / 2).map(|i| self.node(&layer[2 * i].clone(), &layer[2 * i + 1].clone())).collect();
            }
            cur_cells = Some(layer[0]);
            (self.job_units.len() as u32 - 1, layer[0].digest)
        };
        for (lv, &sd) in siblings.iter().enumerate() {
            let (slo, shi) = digest_cells(sd);
            let bit = bits[lv];
            let swap = lv == 0 && super::verifier::tamper_now(super::verifier::Tamper::MerkleSwapLr);
            let b1 = coeffs(bit.val)[0] == F::ONE;
            let (ld, rd) = if b1 { (sd, cur_d) } else { (cur_d, sd) };
            // node job: the current digest goes left iff bit = 0 (unit index + 12 * bit), the
            // sibling to the other side (12 (1 - bit)); 4 rows per level
            use openvm_stark_backend::hasher::MerkleHasher;
            let id = self.job_units.len() as u32;
            let units: Vec<Option<U2>> = super::hash::digest_units(digest_words(ld))
                .into_iter()
                .chain(super::hash::digest_units(digest_words(rd)))
                .flat_map(|u| [Some(u), None])
                .collect();
            self.job_units.push(BJob { tag: 0, node: true, units });
            self.merkle_nodes += 1;
            // the node job's start (job id, NODE_TAG) is sent by the SibWS4 row (P0 = NODE_TAG,
            // otherwise unused by SibWS4); only the swap test hook, which has no SibWS4 row,
            // keeps a separate NodeJob row.  4 rows per level.
            if swap {
                self.push(Op::NodeJob, NODE_TAG, 0, id, 0, EF::ZERO, F::ZERO);
            }
            if let Some(c) = cur_cells.take() {
                self.push(Op::UnitWS4, c.lo.addr, bit.addr, id, 0, c.lo.val, F::ZERO);
                self.push(Op::UnitWS2, c.hi.addr, bit.addr, id, 8, c.hi.val, F::ZERO);
            } else {
                let (clo, chi) = digest_cells(cur_d);
                self.push(Op::DigWS4, cur_job, bit.addr, id, 0, ef_from(clo), F::ZERO);
                self.push(Op::DigWS2, cur_job, bit.addr, id, 8, ef_from(chi), F::ZERO);
            }
            if swap {
                // test hook: the sibling on the same side as the current digest
                let l4 = self.load(ef_from(slo));
                let l2 = self.load(ef_from(shi));
                self.push(Op::UnitWS4, l4.addr, bit.addr, id, 0, l4.val, F::ZERO);
                self.push(Op::UnitWS2, l2.addr, bit.addr, id, 8, l2.val, F::ZERO);
            } else {
                self.push(Op::SibWS4, NODE_TAG, bit.addr, id, 0, ef_from(slo), F::ZERO);
                self.push(Op::SibWS2, 0, bit.addr, id, 8, ef_from(shi), F::ZERO);
            }
            cur_d = crate::sha384::config::ShaHasher.compress(ld, rd);
            cur_job = id;
        }
        let cur = match cur_cells {
            Some(c) => c,
            None => self.dig(cur_job, cur_d),
        };
        if cur.digest != root.digest {
            self.failures.push("merkle root".into());
        }
        self.assert_eq(cur.lo, root.lo, "merkle root lo");
        self.assert_eq(cur.hi, root.hi, "merkle root hi");
    }

    /// Finish: pad with NOPs, put the accumulator row last.  Returns the program length 2^log_rows.
    pub fn finish(&mut self) {
        self.tr_close();
        if self.acc_slots.is_none() {
            self.begin();
        }
        let (s2, s1) = self.acc_slots.unwrap();
        // program length: even (BIND rows cover two rows each); no power-of-two padding
        if self.instrs.len() % 2 == 1 {
            self.instrs.push(Instr::NOP);
            self.vals.push(EF::ZERO);
            self.wits.push(F::ZERO);
        }
        let n = self.instrs.len();
        assert!(n <= self.prog_len());
        assert_horner_chains(&self.instrs);
        let tp = super::uair::tau_pows();
        let e1n = super::uair::E1_SIZE;
        let pw = |w: [u32; 4]| -> EF { (0..4).map(|j| tp[j] * F::from_u32(w[j])).sum() };
        let _ = s2; // former ACC2 slot (app table, removed with G2): stays a Nop
        // ACC: P0 = last BIND pair index, pinning the BIND region to the whole program
        self.instrs[s1 as usize] = Instr { op: Op::Acc, a: n as u32 - 2, b: 0, k1: 0, k2: 0 };
        // binding sum over all rows (including the ACC row itself)
        let mut acc = EF::ZERO;
        for (x, ins) in self.instrs.iter().enumerate() {
            acc += self.vals[x % e1n] * self.vals[e1n + x / e1n] * pw(ins.words());
        }
        self.vals[s1 as usize] = acc;
        // re-evaluate the deferred check
        let late = std::mem::take(&mut self.late);
        for &i in &late {
            let ins = self.instrs[i];
            let (a, b) = (self.vals[ins.a as usize], self.vals[ins.b as usize]);
            self.vals[i] = match ins.op {
                Op::Add => a + b,
                Op::Sub => a - b,
                Op::Mul => a * b,
                Op::Zero => {
                    if a != EF::ZERO {
                        self.failures.push("program binding".into());
                    }
                    EF::ZERO
                }
                _ => unreachable!(),
            };
        }
        self.late = late;
    }

    /// Read counts per address (memory multiplicities).
    pub fn read_counts(&self) -> Vec<u32> {
        let mut m = vec![0u32; self.instrs.len()];
        for ins in &self.instrs {
            if ins.op.reads_a() {
                m[ins.a as usize] += 1;
            }
            if ins.op.reads_b() {
                m[ins.b as usize] += 1;
            }
        }
        m
    }
}



/// Horner chains must be complete (FAITHFUL.md §W): a HornR / HornE row's own c is pinned only by
/// the previous row's transition constraint, so it must follow HornS or HornR; a HornS / HornR
/// row constrains the next row's c, so it must be followed by HornR or HornE (never the last
/// program row, whose next row is BIND's first row).
pub fn assert_horner_chains(instrs: &[Instr]) {
    use Op::*;
    for (i, ins) in instrs.iter().enumerate() {
        if matches!(ins.op, HornR | HornE) {
            assert!(i > 0 && matches!(instrs[i - 1].op, HornS | HornR), "row {i}: {:?} not preceded by HornS / HornR", ins.op);
        }
        if matches!(ins.op, HornS | HornR) {
            assert!(i + 1 < instrs.len() && matches!(instrs[i + 1].op, HornR | HornE), "row {i}: {:?} not followed by HornR / HornE", ins.op);
        }
    }
}
