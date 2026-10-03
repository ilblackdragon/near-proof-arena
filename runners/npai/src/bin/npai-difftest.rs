//! `npai-difftest`: differential testing of the Rust NPAI interpreter against
//! the Lean reference executable (`formal-core`: `lake exe arena-interp-ref`).
//!
//! ```text
//! npai-difftest --ref <path/to/arena-interp-ref> [--cases N] [--seed S]
//!               [--jobs J] [--work DIR] [--shard-size K]
//! ```
//!
//! Generates N cases (random/mutated/structured images and tapes, fuel
//! boundaries, bounds edges, max sizes), writes them in `arena-interp-ref
//! batch` format, runs the Lean reference on shards in parallel and compares
//! every result byte-for-byte with `arena_npai::report::expect_json` of the
//! Rust interpreter. Exit 0 iff zero disagreements; failing cases are written
//! to `<work>/mismatch-*.txt` (one batch line each, replayable).
#![forbid(unsafe_code)]

use arena_npai::interp::{self, encode, BinOp, Inputs, Instr, Program, Tape};
use arena_npai::report::{expect_json, to_hex};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;
use std::time::Instant;

/// SplitMix64: deterministic, dependency-free.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize]
    }
}

struct Case {
    kind: &'static str,
    image: Vec<u8>,
    public: Vec<u8>,
    claim: Vec<u8>,
    proof: Vec<u8>,
    fuel: u64,
}

impl Case {
    fn line(&self) -> String {
        format!(
            "{},{},{},{},{}",
            to_hex(&self.image),
            to_hex(&self.public),
            to_hex(&self.claim),
            to_hex(&self.proof),
            self.fuel
        )
    }
    fn rust(&self) -> String {
        let inp = Inputs {
            public: &self.public,
            claim: &self.claim,
            proof: &self.proof,
        };
        expect_json(&interp::expect(&self.image, &inp, self.fuel))
    }
}

const TAPES: [Tape; 3] = [Tape::Pub, Tape::Claim, Tape::Proof];
const BINOPS: [BinOp; 10] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::Shr,
    BinOp::Eq,
    BinOp::Ltu,
];

/// Interesting 64-bit values relative to the program/tape sizes.
fn interesting(r: &mut Rng, mem: u64, tlen: u64) -> u64 {
    let m = |d: i64| (mem as i64 + d) as u64;
    let t = |d: i64| (tlen as i64 + d) as u64;
    match r.below(24) {
        0 => 0,
        1 => 1,
        2 => r.below(8),
        3 => 32,
        4 => 63,
        5 => 64,
        6 => 65,
        7 => m(-1),
        8 => mem,
        9 => m(-32),
        10 => m(-31),
        11 => m(1),
        12 => t(-1),
        13 => tlen,
        14 => t(1),
        15 => u32::MAX as u64,
        16 => 1 << 32,
        17 => 1 << 63,
        18 => u64::MAX,
        19 => u64::MAX - 31,
        20 => u64::MAX - mem + 1,
        21 => r.below(mem + 1),
        22 => r.below(256),
        _ => r.next(),
    }
}

/// Prologue loading 64-bit values into registers (CONST/SHL/OR).
fn load64(code: &mut Vec<Instr>, reg: usize, tmp: usize, v: u64) {
    let (hi, lo) = ((v >> 32) as u32, v as u32);
    if hi == 0 {
        code.push(Instr::Const(reg, lo));
        return;
    }
    code.push(Instr::Const(reg, hi));
    code.push(Instr::Const(tmp, 32));
    code.push(Instr::Bin(BinOp::Shl, reg, reg, tmp));
    code.push(Instr::Const(tmp, lo));
    code.push(Instr::Bin(BinOp::Or, reg, reg, tmp));
}

/// `forward_from = Some(pc)`: jump targets only go forward (terminating
/// programs, so more runs reach HALT instead of running out of fuel).
fn rand_instr(r: &mut Rng, n_code: u32, forward_from: Option<u32>) -> Instr {
    let g = |r: &mut Rng| r.below(16) as usize;
    let target = |r: &mut Rng| match (forward_from, r.below(10)) {
        (_, 0) => n_code,
        (_, 1) => n_code + 1,
        (_, 3) => 0,
        (None, 2) => r.next() as u32,
        (None, _) => r.below(n_code as u64 + 1) as u32,
        (Some(pc), _) => pc + 1 + r.below((n_code - pc) as u64) as u32,
    };
    let imm = |r: &mut Rng| match r.below(4) {
        0 => r.below(64) as u32,
        1 => u32::MAX - r.below(4) as u32,
        _ => r.next() as u32,
    };
    match r.below(22) {
        0 => Instr::Halt(g(r)),
        1 => Instr::Const(g(r), imm(r)),
        2 => Instr::Mov(g(r), g(r)),
        3..=5 => Instr::Bin(r.pick(&BINOPS), g(r), g(r), g(r)),
        6 => Instr::Addi(g(r), g(r), imm(r)),
        7 => Instr::Jmp(target(r)),
        8 => Instr::Jz(g(r), target(r)),
        9 => Instr::Jnz(g(r), target(r)),
        10 => Instr::Tlen(g(r), r.pick(&TAPES)),
        11 => Instr::Tload(g(r), g(r), r.pick(&TAPES)),
        12 | 13 => Instr::Tcopy(g(r), g(r), g(r), r.pick(&TAPES)),
        14 => Instr::Ld8(g(r), g(r)),
        15 => Instr::St8(g(r), g(r)),
        16 => Instr::Sha256(g(r), g(r), g(r)),
        17 => Instr::RoHash(g(r), g(r), g(r)),
        18 => Instr::MemEq(g(r), g(r), g(r), g(r)),
        19 => Instr::Out(r.below(2) as u8, g(r), g(r)),
        _ => Instr::Halt(g(r)),
    }
}

fn tapes(r: &mut Rng, max: usize) -> [Vec<u8>; 3] {
    let mut t = || {
        let n = match r.below(4) {
            0 => 0,
            1 => r.below(8) as usize,
            _ => r.below(max as u64 + 1) as usize,
        };
        r.bytes(n)
    };
    [t(), t(), t()]
}

/// Observability epilogue: OUT the whole memory, then write every register
/// (except two temporaries) little-endian into memory and OUT it, then HALT,
/// so register- and memory-level divergences become visible. Needs mem >= 128.
fn dump_epilogue(r: &mut Rng, code: &mut Vec<Instr>, mem: u32) {
    let (t1, t2) = (r.below(16) as usize, r.below(16) as usize);
    let t2 = if t2 == t1 { (t1 + 1) % 16 } else { t2 };
    code.push(Instr::Const(t1, 0));
    code.push(Instr::Const(t2, mem));
    code.push(Instr::Out(1, t1, t2));
    let mut at = 0u32;
    for reg in (0..16).filter(|&x| x != t1 && x != t2) {
        for _ in 0..8 {
            code.push(Instr::Const(t1, at));
            code.push(Instr::St8(t1, reg));
            code.push(Instr::Const(t2, 8));
            code.push(Instr::Bin(BinOp::Shr, reg, reg, t2));
            at += 1;
        }
    }
    code.push(Instr::Const(t1, 0));
    code.push(Instr::Const(t2, at));
    code.push(Instr::Out(0, t1, t2));
    code.push(Instr::Halt(t2));
}

/// "alu": straight-line ALU/control code over interesting register values,
/// with every register dumped at the end (fuel always sufficient), so the
/// exact value semantics of every BinOp/ADDI/CONST/MOV/JZ/JNZ is observed.
fn alu_program(r: &mut Rng) -> Program {
    let mem = 256u32;
    let mut code = vec![];
    for reg in 0..16usize {
        let v = interesting(r, mem as u64, 100);
        // shift amounts: often >= 64 to exercise `mod 64`
        let v = if r.chance(1, 4) {
            r.pick(&[
                63,
                64,
                65,
                127,
                128,
                129,
                200,
                1 << 32,
                (1 << 32) + 1,
                u64::MAX,
            ])
        } else {
            v
        };
        load64(&mut code, reg, (reg + 1) % 16, v);
    }
    let n = 4 + r.below(24) as usize;
    for _ in 0..n {
        let g = |r: &mut Rng| r.below(16) as usize;
        let here = code.len() as u32;
        code.push(match r.below(10) {
            0..=5 => Instr::Bin(r.pick(&BINOPS), g(r), g(r), g(r)),
            6 => {
                let x = r.next() as u32;
                Instr::Addi(g(r), g(r), r.pick(&[0, 1, u32::MAX, 1 << 31, x]))
            }
            7 => Instr::Mov(g(r), g(r)),
            // forward skip of 0..2 instructions (or a back-jump to 0 once in a while)
            8 => Instr::Jz(
                g(r),
                if r.chance(1, 16) {
                    0
                } else {
                    here + 1 + r.below(3) as u32
                },
            ),
            _ => Instr::Jnz(
                g(r),
                if r.chance(1, 16) {
                    0
                } else {
                    here + 1 + r.below(3) as u32
                },
            ),
        });
    }
    // Pad so forward skips stay inside the program.
    code.push(Instr::Mov(0, 0));
    code.push(Instr::Mov(0, 0));
    dump_epilogue(r, &mut code, mem);
    Program {
        mem_size: mem,
        data: r.bytes(64),
        code,
    }
}

/// "bulk": straight-line bulk operations with lengths around the 64-byte
/// cost steps and the SHA-256 padding boundaries, overlapping src/dst,
/// then a full dump.
fn bulk_program(r: &mut Rng, tlen: u64) -> Program {
    let mem = r.pick(&[128u32, 256, 300, 1024]);
    let mut code = vec![];
    let n = 1 + r.below(6) as usize;
    let lens = [
        0u64, 1, 31, 32, 33, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 191, 192,
    ];
    for _ in 0..n {
        let (a, b, c) = (r.below(13) as usize, 13usize, 14usize);
        let a = if a == b || a == c { 0 } else { a };
        let len = if r.chance(3, 4) {
            r.pick(&lens)
        } else {
            interesting(r, mem as u64, tlen)
        };
        let lim = |r: &mut Rng, m: u64| {
            if r.chance(3, 4) {
                r.below((m.saturating_sub(len)) + 1)
            } else {
                interesting(r, m, tlen)
            }
        };
        let x = lim(r, mem as u64);
        let ylim = if r.chance(1, 2) { mem as u64 } else { tlen };
        let y = lim(r, ylim);
        load64(&mut code, a, 15, x);
        load64(&mut code, b, 15, y);
        load64(&mut code, c, 15, len);
        code.push(match r.below(6) {
            0 => Instr::Sha256(a, b, c),
            1 => Instr::RoHash(a, b, c),
            2 => Instr::MemEq(r.below(16) as usize, a, b, c),
            3 => Instr::Out(r.below(2) as u8, a, c),
            _ => Instr::Tcopy(a, b, c, r.pick(&TAPES)),
        });
    }
    dump_epilogue(r, &mut code, mem);
    let dl = r.below(mem as u64 + 1) as usize;
    Program {
        mem_size: mem,
        data: r.bytes(dl),
        code,
    }
}

/// Structured, mostly-valid program: interesting register prologue + random body.
fn structured(r: &mut Rng, big: bool) -> (Program, [Vec<u8>; 3]) {
    let mem: u32 = if big {
        r.pick(&[1 << 16, 1 << 18, 1 << 20, (1 << 20) + 7])
    } else {
        match r.below(6) {
            0 => 0,
            1 => r.below(40) as u32,
            2 => 32,
            _ => r.below(4096) as u32,
        }
    };
    let data_len = if mem == 0 {
        0
    } else {
        r.below(mem.min(512) as u64 + 1) as usize
    };
    let tp = tapes(r, if big { 4096 } else { 300 });
    let tlen = tp[r.below(3) as usize].len() as u64;
    let mut code = vec![];
    for reg in 0..14usize {
        if r.chance(3, 4) {
            let v = interesting(r, mem as u64, tlen);
            load64(&mut code, reg, 15, v);
        }
    }
    let body = 1 + r.below(if big { 12 } else { 40 }) as usize;
    // Slots: a single random instruction, or a 4-instruction "bulk template"
    // (CONST dst/src/len near valid ranges, then TCOPY/SHA256/ROHASH/MEMEQ/OUT)
    // so that bulk operations frequently succeed with mid-size lengths.
    let templ: Vec<bool> = (0..body).map(|_| r.chance(1, 4)).collect();
    let n_code = (code.len() + body + 3 * templ.iter().filter(|t| **t).count() + 1) as u32;
    let forward = r.chance(1, 2);
    let span = (mem as u64).max(tlen) + 64;
    for t in templ {
        if t {
            let (a, b, c) = (
                r.below(16) as usize,
                r.below(16) as usize,
                r.below(16) as usize,
            );
            let near = |r: &mut Rng, lim: u64| {
                if r.chance(1, 2) {
                    r.below(lim + 1)
                } else {
                    lim.saturating_sub(r.below(70))
                }
            };
            let len = near(r, span) as u32;
            let x = near(r, mem as u64) as u32;
            let y = near(r, span) as u32;
            code.push(Instr::Const(c, len));
            code.push(Instr::Const(a, x));
            code.push(Instr::Const(b, y));
            code.push(match r.below(6) {
                0 => Instr::Sha256(a, b, c),
                1 => Instr::RoHash(a, b, c),
                2 => Instr::MemEq(r.below(16) as usize, a, b, c),
                3 => Instr::Out(r.below(2) as u8, a, c),
                _ => Instr::Tcopy(a, b, c, r.pick(&TAPES)),
            });
        } else {
            let pc = code.len() as u32;
            code.push(rand_instr(r, n_code, forward.then_some(pc)));
        }
    }
    if mem >= 128 && r.chance(1, 2) {
        dump_epilogue(r, &mut code, mem);
    } else if r.chance(9, 10) {
        code.push(Instr::Halt(r.below(16) as usize));
    }
    (
        Program {
            mem_size: mem,
            data: r.bytes(data_len),
            code,
        },
        tp,
    )
}

/// Mutate an image at the byte level (decoder edge cases).
fn mutate(r: &mut Rng, mut img: Vec<u8>) -> Vec<u8> {
    for _ in 0..1 + r.below(3) {
        if img.is_empty() {
            img.push(r.next() as u8);
            continue;
        }
        let n = img.len();
        match r.below(9) {
            0 => {
                let i = r.below(n as u64) as usize;
                img[i] ^= 1 << r.below(8);
            }
            1 => {
                let i = r.below(n as u64) as usize;
                img[i] = r.next() as u8;
            }
            2 => img.truncate(r.below(n as u64) as usize),
            3 => {
                let k = 1 + r.below(9) as usize;
                img.extend(r.bytes(k))
            }
            4 if n >= 9 => {
                // memSize around limits
                let x = r.next() as u32;
                let v: u32 = r.pick(&[0, 1, 1 << 24, (1 << 24) + 1, u32::MAX, x]);
                img[5..9].copy_from_slice(&v.to_le_bytes());
            }
            5 if n >= 13 => {
                // dataLen +- 1
                let d = u32::from_le_bytes([img[9], img[10], img[11], img[12]]);
                let v = if r.chance(1, 2) {
                    d.wrapping_add(1)
                } else {
                    d.wrapping_sub(1)
                };
                img[9..13].copy_from_slice(&v.to_le_bytes());
            }
            6 if n >= 21 => {
                // perturb one instruction field (op/a/b/c/imm) in the code tail
                let words = (n - 17) / 8;
                if words > 0 {
                    let w = n - 8 * (1 + r.below(words as u64) as usize);
                    let f = r.below(8) as usize;
                    let x = r.next() as u8;
                    img[w + f] = r.pick(&[0, 1, 2, 3, 15, 16, 17, 0x0E, 0x13, 0x43, 0x51, 0xFF, x]);
                }
            }
            7 if n >= 17 => {
                // codeLen +- 1 (last 4 bytes before code unknown; rewrite at end-based guess)
                let d = u32::from_le_bytes([img[9], img[10], img[11], img[12]]) as usize;
                if 13 + d + 4 <= n {
                    let at = 13 + d;
                    let c = u32::from_le_bytes([img[at], img[at + 1], img[at + 2], img[at + 3]]);
                    let v = r.pick(&[
                        c.wrapping_add(1),
                        c.wrapping_sub(1),
                        1 << 16,
                        (1 << 16) + 1,
                        u32::MAX,
                    ]);
                    img[at..at + 4].copy_from_slice(&v.to_le_bytes());
                }
            }
            _ => {
                let i = r.below(n as u64 + 1) as usize;
                img.insert(i, r.next() as u8);
            }
        }
    }
    img
}

/// Raw instruction word near the canonicality rules: a random *valid*
/// instruction with (usually) exactly one field set to a boundary value, or
/// a fully random word.
fn raw_word(r: &mut Rng) -> [u8; 8] {
    let mut w = rand_instr(r, 4, None).encode();
    match r.below(8) {
        0 => {}
        1 => {
            for b in &mut w {
                *b = r.pick(&[0u8, 0, 0, 1, 2, 3, 15, 16, 255]);
            }
            w[0] = r.pick(&[
                0x00, 0x01, 0x02, 0x03, 0x0A, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x20,
                0x21, 0x22, 0x23, 0x30, 0x31, 0x40, 0x41, 0x42, 0x43, 0x50, 0x51, 0xFF,
            ]);
        }
        2 | 3 => {
            // imm field to a boundary value
            let imm: u32 = r.pick(&[0, 1, 2, 3, 15, 16, 16, 16, 17, 255, 256, u32::MAX]);
            w[4..8].copy_from_slice(&imm.to_le_bytes());
        }
        _ => {
            let f = 1 + r.below(3) as usize;
            w[f] = r.pick(&[0u8, 1, 15, 16, 17, 128, 255]);
        }
    }
    w
}

fn raw_words_image(r: &mut Rng) -> Vec<u8> {
    let n = 1 + r.below(4) as usize;
    let mut img = b"NPAI\x01".to_vec();
    img.extend_from_slice(&64u32.to_le_bytes());
    img.extend_from_slice(&0u32.to_le_bytes());
    img.extend_from_slice(&(n as u32 + 1).to_le_bytes());
    for _ in 0..n {
        img.extend_from_slice(&raw_word(r));
    }
    img.extend_from_slice(&Instr::Halt(r.below(16) as usize).encode());
    img
}

/// Fixed edge cases (max sizes, hash of large inputs, boundary programs).
fn fixed_cases() -> Vec<Case> {
    let mk = |kind, p: &Program, fuel| Case {
        kind,
        image: encode(p),
        public: vec![],
        claim: vec![],
        proof: vec![],
        fuel,
    };
    let mut v = vec![];
    // Max memory, SHA256 over 1 MiB and over the whole 2^24 - 32 bytes.
    for (len, fuel) in [(1u32 << 20, 1u64 << 20), ((1u32 << 24) - 32, 1 << 22)] {
        for op in [0u8, 1] {
            let mut code = vec![
                Instr::Const(1, 0),
                Instr::Const(3, len),
                Instr::Const(2, (1 << 24) - 32),
            ];
            code.push(if op == 0 {
                Instr::Sha256(2, 1, 3)
            } else {
                Instr::RoHash(2, 1, 3)
            });
            code.extend([Instr::Const(4, 32), Instr::Out(0, 2, 4), Instr::Halt(4)]);
            let p = Program {
                mem_size: 1 << 24,
                data: vec![0xAB; 1000],
                code,
            };
            v.push(mk("fixed-maxmem-hash", &p, fuel));
        }
    }
    // Max memory +1: decode error.
    let mut img = encode(&Program {
        mem_size: 1 << 24,
        data: vec![],
        code: vec![Instr::Halt(0)],
    });
    img[5..9].copy_from_slice(&((1u32 << 24) + 1).to_le_bytes());
    v.push(Case {
        kind: "fixed-mem-limit",
        image: img,
        public: vec![],
        claim: vec![],
        proof: vec![],
        fuel: 10,
    });
    // Max code length (2^16): a jmp chain through the whole program, and 2^16 + 1.
    let mut code: Vec<Instr> = (1..(1u32 << 16)).map(Instr::Jmp).collect();
    code[(1 << 16) - 2] = Instr::Const(0, 7);
    code.push(Instr::Halt(0));
    let p = Program {
        mem_size: 0,
        data: vec![],
        code: code.clone(),
    };
    v.push(mk("fixed-maxcode", &p, 1 << 17));
    v.push(mk("fixed-maxcode-oof", &p, (1 << 16) - 1));
    let mut img = encode(&p);
    img.extend_from_slice(&Instr::Halt(0).encode());
    let at = 13;
    img[at..at + 4].copy_from_slice(&((1u32 << 16) + 1).to_le_bytes());
    v.push(Case {
        kind: "fixed-code-limit",
        image: img,
        public: vec![],
        claim: vec![],
        proof: vec![],
        fuel: 10,
    });
    // Full data segment of 64 KiB, memeq over it.
    let p = Program {
        mem_size: 1 << 17,
        data: (0..(1u32 << 16)).map(|i| (i * 7) as u8).collect(),
        code: vec![
            Instr::Const(1, 0),
            Instr::Const(2, 1 << 16),
            Instr::Const(3, 1 << 16),
            Instr::Tcopy(2, 1, 3, Tape::Proof),
            Instr::MemEq(4, 1, 2, 3),
            Instr::Halt(4),
        ],
    };
    let mut c = mk("fixed-memeq-64k", &p, 1 << 12);
    c.proof = (0..(1u32 << 16)).map(|i| (i * 7) as u8).collect();
    v.push(c);
    v
}

fn gen_case(r: &mut Rng) -> Vec<Case> {
    let roll = r.below(100);
    let fuel_rand = |r: &mut Rng| match r.below(5) {
        0 => r.below(4),
        1 => r.below(64),
        2 => u64::MAX,
        _ => r.below(5000),
    };
    if roll < 3 {
        // garbage bytes, sometimes with a valid magic prefix
        let k = r.below(64) as usize;
        let mut img = r.bytes(k);
        if r.chance(1, 2) {
            let mut h = b"NPAI\x01".to_vec();
            h.extend(img);
            img = h;
        }
        return vec![Case {
            kind: "garbage",
            image: img,
            public: vec![],
            claim: vec![],
            proof: vec![],
            fuel: 100,
        }];
    }
    if roll < 14 {
        let img = raw_words_image(r);
        return vec![Case {
            kind: "raw-words",
            image: img,
            public: vec![],
            claim: vec![],
            proof: vec![],
            fuel: 100,
        }];
    }
    if (33..48).contains(&roll) {
        let p = alu_program(r);
        return vec![Case {
            kind: "alu",
            image: encode(&p),
            public: vec![],
            claim: vec![],
            proof: vec![],
            fuel: 1_000_000,
        }];
    }
    if (48..60).contains(&roll) {
        let [public, claim, proof] = tapes(r, 300);
        let p = bulk_program(r, public.len().max(claim.len()).max(proof.len()) as u64);
        return vec![Case {
            kind: "bulk",
            image: encode(&p),
            public,
            claim,
            proof,
            fuel: 1_000_000,
        }];
    }
    let big = (30..33).contains(&roll);
    let (p, tp) = structured(r, big);
    let [public, claim, proof] = tp;
    let img = encode(&p);
    if roll < 30 {
        let fuel = fuel_rand(r);
        return vec![Case {
            kind: "mutated",
            image: mutate(r, img),
            public,
            claim,
            proof,
            fuel,
        }];
    }
    // Valid program; also probe the exact fuel boundary.
    let fuel = if big { 1 << 16 } else { fuel_rand(r) };
    let base = Case {
        kind: if big { "structured-big" } else { "structured" },
        image: img,
        public,
        claim,
        proof,
        fuel,
    };
    let inp = Inputs {
        public: &base.public,
        claim: &base.claim,
        proof: &base.proof,
    };
    let mut out = vec![];
    if let Some((_, used, _, _)) = interp::expect(&base.image, &inp, 20_000) {
        if r.chance(1, 3) && used > 0 && used < 20_000 {
            for f in [used - 1, used, used + 1] {
                out.push(Case {
                    kind: "fuel-boundary",
                    image: base.image.clone(),
                    public: base.public.clone(),
                    claim: base.claim.clone(),
                    proof: base.proof.clone(),
                    fuel: f,
                });
            }
        }
    }
    out.push(base);
    out
}

/// Programs may loop: never hand the Lean reference a huge fuel budget unless
/// the program halts within a small one.
fn cap_fuel(mut cs: Vec<Case>) -> Vec<Case> {
    const CAP: u64 = 20_000;
    for c in &mut cs {
        if c.fuel > CAP {
            let inp = Inputs {
                public: &c.public,
                claim: &c.claim,
                proof: &c.proof,
            };
            if let Some((interp::Outcome::OutOfFuel, ..)) = interp::expect(&c.image, &inp, CAP) {
                c.fuel = CAP;
            }
        }
    }
    cs
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |k: &str| {
        args.iter()
            .position(|a| a == k)
            .and_then(|i| args.get(i + 1))
            .cloned()
    };
    let refexe =
        get("--ref").unwrap_or_else(|| "formal-core/.lake/build/bin/arena-interp-ref".into());
    let n: usize = get("--cases")
        .map(|s| s.parse().expect("--cases"))
        .unwrap_or(10_000);
    let seed: u64 = get("--seed")
        .map(|s| s.parse().expect("--seed"))
        .unwrap_or(1);
    let jobs: usize = get("--jobs")
        .map(|s| s.parse().expect("--jobs"))
        .unwrap_or(8);
    let shard_timeout = std::time::Duration::from_secs(
        get("--shard-timeout")
            .map(|s| s.parse().expect("--shard-timeout"))
            .unwrap_or(900),
    );
    let shard: usize = get("--shard-size")
        .map(|s| s.parse().expect("--shard-size"))
        .unwrap_or(2000);
    let work = PathBuf::from(get("--work").unwrap_or_else(|| {
        std::env::temp_dir()
            .join("npai-difftest")
            .display()
            .to_string()
    }));
    std::fs::create_dir_all(&work).expect("create work dir");

    let t0 = Instant::now();
    let mut r = Rng(seed);
    let mut cases = if args.iter().any(|a| a == "--no-fixed") {
        vec![]
    } else {
        fixed_cases()
    };
    while cases.len() < n {
        cases.extend(cap_fuel(gen_case(&mut r)));
    }
    let rust: Vec<String> = cases.iter().map(Case::rust).collect();
    let t_rust = t0.elapsed();
    eprintln!(
        "generated {} cases + Rust results in {:.2?}",
        cases.len(),
        t_rust
    );

    // Shards -> Lean reference: a pool of `jobs` worker threads, each running
    // one `arena-interp-ref batch` process at a time.
    let chunks: Vec<(usize, usize)> = (0..cases.len())
        .step_by(shard)
        .map(|s| (s, (s + shard).min(cases.len())))
        .collect();
    let t1 = Instant::now();
    let next = std::sync::atomic::AtomicUsize::new(0);
    type ShardResult = Option<(Vec<String>, std::time::Duration)>;
    let results: std::sync::Mutex<Vec<ShardResult>> =
        std::sync::Mutex::new(vec![None; chunks.len()]);
    std::thread::scope(|sc| {
        for _ in 0..jobs {
            sc.spawn(|| loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                let Some(&(s, e)) = chunks.get(k) else { break };
                let inp = work.join(format!("shard-{s}.in"));
                let out = work.join(format!("shard-{s}.out"));
                let body: String = cases[s..e].iter().map(|c| c.line() + "\n").collect();
                std::fs::write(&inp, body).expect("write shard");
                let t = Instant::now();
                let mut child = Command::new(&refexe)
                    .arg("batch")
                    .arg(&inp)
                    .arg(&out)
                    .spawn()
                    .expect("spawn arena-interp-ref");
                // A shard that exceeds the timeout (e.g. the reference runs a
                // program the Rust side considered terminating) counts as a
                // disagreement on all its cases, never as a pass.
                let st = loop {
                    if let Some(st) = child.try_wait().expect("wait") {
                        break Some(st);
                    }
                    if t.elapsed() > shard_timeout {
                        let _ = child.kill();
                        let _ = child.wait();
                        break None;
                    }
                    std::thread::sleep(std::time::Duration::from_millis(5));
                };
                let dt = t.elapsed();
                let lines: Vec<String> = match st {
                    Some(st) => {
                        assert!(
                            st.success(),
                            "arena-interp-ref failed on {} ({st})",
                            inp.display()
                        );
                        let text = std::fs::read_to_string(&out).expect("read shard output");
                        let lines: Vec<String> = text.lines().map(str::to_string).collect();
                        assert_eq!(lines.len(), e - s, "shard {} line count", inp.display());
                        lines
                    }
                    None => {
                        eprintln!("shard {} timed out after {dt:.2?}", inp.display());
                        vec!["{\"outcome\":\"lean_timeout\"}".to_string(); e - s]
                    }
                };
                let _ = std::fs::remove_file(&inp);
                let _ = std::fs::remove_file(&out);
                results.lock().unwrap()[k] = Some((lines, dt));
            });
        }
    });
    let mut lean: Vec<String> = Vec::with_capacity(cases.len());
    let (mut lean_cpu, mut slowest) = (
        std::time::Duration::ZERO,
        (std::time::Duration::ZERO, 0usize),
    );
    for (k, r) in results.into_inner().unwrap().into_iter().enumerate() {
        let (lines, dt) = r.expect("shard result");
        lean_cpu += dt;
        if dt > slowest.0 {
            slowest = (dt, chunks[k].0);
        }
        lean.extend(lines);
    }
    let t_lean = t1.elapsed();

    let mut by_kind: BTreeMap<&str, usize> = BTreeMap::new();
    let mut by_outcome: BTreeMap<String, usize> = BTreeMap::new();
    let mut bad = 0usize;
    for (i, c) in cases.iter().enumerate() {
        *by_kind.entry(c.kind).or_default() += 1;
        let o = rust[i].split('"').nth(3).unwrap_or("?").to_string();
        *by_outcome.entry(o).or_default() += 1;
        if rust[i] != lean[i] {
            bad += 1;
            if bad <= 20 {
                let f = work.join(format!("mismatch-{i}.txt"));
                std::fs::write(&f, c.line() + "\n").expect("write mismatch");
                eprintln!(
                    "MISMATCH case {i} ({}): rust={} lean={} -> {}",
                    c.kind,
                    rust[i],
                    lean[i],
                    f.display()
                );
            }
        }
    }
    println!("cases: {}  disagreements: {bad}  seed: {seed}", cases.len());
    println!("by kind: {by_kind:?}");
    println!("by outcome: {by_outcome:?}");
    println!(
        "time: rust {:.2?} (incl. generation); lean {:.2?} wall, {:.2?} summed over shards ({jobs} workers); slowest shard {:.2?} (cases from {})",
        t_rust, t_lean, lean_cpu, slowest.0, slowest.1
    );
    std::process::exit(if bad == 0 { 0 } else { 1 });
}
