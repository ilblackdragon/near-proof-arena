//! VERBATIM COPY of runners/npai/src/interp.rs (the judge's NPAI v1 interpreter),
//! used only by the local `out/verify` convenience wrapper. The arena never runs
//! the candidate's `verify` on the `npai-v1` route: it runs its own
//! `npai-verify` on `out/verifier.npai`. Not in any trust path.

//! NPAI v1 interpreter — **trusted computing base**.
//!
//! This module is a line-by-line transcription of
//! `formal-core/ArenaCore/Interp.lean` (`decode`, `step`/`exec1`/`cost`,
//! `runWith deployedRO`, `run`, `runOut`). The Lean definition is
//! normative; `docs/INTERP_SPEC.md` restates it. Each item below names the
//! Lean definition it mirrors. Keep this file small and obviously correct:
//! no unsafe, no dependencies besides `sha2`, every offset computed in
//! `u128` so that `off + len` can never wrap.
//!
//! Domain restriction w.r.t. Lean: `fuel` is a `u64` here (a `Nat` in Lean).
//! All register values are `< 2^64` in both, tapes are `< 2^32` bytes (the
//! pre-check), memory is `<= 2^24` bytes, code `<= 2^16` instructions.

use sha2::{Digest, Sha256};

#[cfg(not(target_pointer_width = "64"))]
compile_error!("arena-npai assumes a 64-bit target (tape offsets up to 2^32 must fit usize)");

/// `maxMemSize` (2^24).
pub const MAX_MEM_SIZE: u64 = 1 << 24;
/// `maxCodeLen` (2^16).
pub const MAX_CODE_LEN: u64 = 1 << 16;
/// `maxTapeLen` (2^32): a tape of this length or more traps before execution.
pub const MAX_TAPE_LEN: u64 = 1 << 32;
/// `numRegs`.
pub const NUM_REGS: usize = 16;
/// `magic` ("NPAI").
pub const MAGIC: [u8; 4] = *b"NPAI";
/// `version`.
pub const VERSION: u8 = 1;
/// `roTag`: domain separation of the protocol hash, ASCII "NPAI-RO-v1".
pub const RO_TAG: &[u8] = b"NPAI-RO-v1";

/// `TapeId` (0 = public, 1 = claim, 2 = proof).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tape {
    Pub,
    Claim,
    Proof,
}

impl Tape {
    /// `TapeId.ofNat?`
    pub fn from_imm(x: u32) -> Option<Tape> {
        match x {
            0 => Some(Tape::Pub),
            1 => Some(Tape::Claim),
            2 => Some(Tape::Proof),
            _ => None,
        }
    }
    /// `TapeId.toNat`
    pub fn to_imm(self) -> u32 {
        match self {
            Tape::Pub => 0,
            Tape::Claim => 1,
            Tape::Proof => 2,
        }
    }
}

/// `BinOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ltu,
}

impl BinOp {
    /// `BinOp.ofOpcode?`
    pub fn from_opcode(op: u8) -> Option<BinOp> {
        Some(match op {
            0x03 => BinOp::Add,
            0x04 => BinOp::Sub,
            0x05 => BinOp::Mul,
            0x06 => BinOp::And,
            0x07 => BinOp::Or,
            0x08 => BinOp::Xor,
            0x09 => BinOp::Shl,
            0x0A => BinOp::Shr,
            0x0B => BinOp::Eq,
            0x0C => BinOp::Ltu,
            _ => return None,
        })
    }
    /// `BinOp.opcode`
    pub fn opcode(self) -> u8 {
        match self {
            BinOp::Add => 0x03,
            BinOp::Sub => 0x04,
            BinOp::Mul => 0x05,
            BinOp::And => 0x06,
            BinOp::Or => 0x07,
            BinOp::Xor => 0x08,
            BinOp::Shl => 0x09,
            BinOp::Shr => 0x0A,
            BinOp::Eq => 0x0B,
            BinOp::Ltu => 0x0C,
        }
    }
    /// `BinOp.eval` on values `< 2^64` (all results wrap mod 2^64).
    pub fn eval(self, x: u64, y: u64) -> u64 {
        match self {
            BinOp::Add => x.wrapping_add(y),
            BinOp::Sub => x.wrapping_sub(y),
            BinOp::Mul => x.wrapping_mul(y),
            BinOp::And => x & y,
            BinOp::Or => x | y,
            BinOp::Xor => x ^ y,
            // (x <<< (y % 64)) % 2^64: bits shifted past 63 are dropped.
            BinOp::Shl => x << (y % 64),
            BinOp::Shr => x >> (y % 64),
            BinOp::Eq => (x == y) as u64,
            BinOp::Ltu => (x < y) as u64,
        }
    }
}

/// `Instr`. Register operands are `< 16` (enforced by `decode`); `R` is a
/// register index stored as `usize` for direct indexing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Instr {
    Halt(usize),
    Const(usize, u32),
    Mov(usize, usize),
    Bin(BinOp, usize, usize, usize),
    Addi(usize, usize, u32),
    Jmp(u32),
    Jz(usize, u32),
    Jnz(usize, u32),
    Tlen(usize, Tape),
    Tload(usize, usize, Tape),
    Tcopy(usize, usize, usize, Tape),
    Ld8(usize, usize),
    St8(usize, usize),
    Sha256(usize, usize, usize),
    RoHash(usize, usize, usize),
    MemEq(usize, usize, usize, usize),
    /// `out k a b`: buffer `k` (0 or 1), address reg `a`, length reg `b`.
    Out(u8, usize, usize),
}

impl Instr {
    /// `Instr.decode`: canonical decoding of one 8-byte word
    /// `[op, a, b, c, imm:u32le]`; unused fields must be zero.
    pub fn decode(op: u8, a: u8, b: u8, c: u8, imm: u32) -> Option<Instr> {
        let r = |x: u8| (x as usize) < NUM_REGS;
        let (ra, rb, rc) = (a as usize, b as usize, c as usize);
        let ok = |cond: bool, i: Instr| if cond { Some(i) } else { None };
        match op {
            0x00 => ok(r(a) && b == 0 && c == 0 && imm == 0, Instr::Halt(ra)),
            0x01 => ok(r(a) && b == 0 && c == 0, Instr::Const(ra, imm)),
            0x02 => ok(r(a) && r(b) && c == 0 && imm == 0, Instr::Mov(ra, rb)),
            0x0D => ok(r(a) && r(b) && c == 0, Instr::Addi(ra, rb, imm)),
            0x10 => ok(a == 0 && b == 0 && c == 0, Instr::Jmp(imm)),
            0x11 => ok(r(a) && b == 0 && c == 0, Instr::Jz(ra, imm)),
            0x12 => ok(r(a) && b == 0 && c == 0, Instr::Jnz(ra, imm)),
            0x20 => {
                if r(a) && b == 0 && c == 0 {
                    Tape::from_imm(imm).map(|t| Instr::Tlen(ra, t))
                } else {
                    None
                }
            }
            0x21 => {
                if r(a) && r(b) && c == 0 {
                    Tape::from_imm(imm).map(|t| Instr::Tload(ra, rb, t))
                } else {
                    None
                }
            }
            0x22 => {
                if r(a) && r(b) && r(c) {
                    Tape::from_imm(imm).map(|t| Instr::Tcopy(ra, rb, rc, t))
                } else {
                    None
                }
            }
            0x30 => ok(r(a) && r(b) && c == 0 && imm == 0, Instr::Ld8(ra, rb)),
            0x31 => ok(r(a) && r(b) && c == 0 && imm == 0, Instr::St8(ra, rb)),
            0x40 => ok(r(a) && r(b) && r(c) && imm == 0, Instr::Sha256(ra, rb, rc)),
            0x42 => ok(r(a) && r(b) && r(c) && imm == 0, Instr::RoHash(ra, rb, rc)),
            0x41 => ok(
                r(a) && r(b) && r(c) && imm < NUM_REGS as u32,
                Instr::MemEq(ra, rb, rc, imm as usize),
            ),
            0x50 => ok(
                r(a) && r(b) && c == 0 && imm < 2,
                Instr::Out(imm as u8, ra, rb),
            ),
            _ => match BinOp::from_opcode(op) {
                Some(bop) => ok(
                    r(a) && r(b) && r(c) && imm == 0,
                    Instr::Bin(bop, ra, rb, rc),
                ),
                None => None,
            },
        }
    }

    /// `Instr.fields`: `(op, a, b, c, imm)`.
    pub fn fields(self) -> (u8, u8, u8, u8, u32) {
        let r = |x: usize| x as u8;
        match self {
            Instr::Halt(a) => (0x00, r(a), 0, 0, 0),
            Instr::Const(a, imm) => (0x01, r(a), 0, 0, imm),
            Instr::Mov(a, b) => (0x02, r(a), r(b), 0, 0),
            Instr::Bin(op, a, b, c) => (op.opcode(), r(a), r(b), r(c), 0),
            Instr::Addi(a, b, imm) => (0x0D, r(a), r(b), 0, imm),
            Instr::Jmp(t) => (0x10, 0, 0, 0, t),
            Instr::Jz(a, t) => (0x11, r(a), 0, 0, t),
            Instr::Jnz(a, t) => (0x12, r(a), 0, 0, t),
            Instr::Tlen(a, t) => (0x20, r(a), 0, 0, t.to_imm()),
            Instr::Tload(a, b, t) => (0x21, r(a), r(b), 0, t.to_imm()),
            Instr::Tcopy(a, b, c, t) => (0x22, r(a), r(b), r(c), t.to_imm()),
            Instr::Ld8(a, b) => (0x30, r(a), r(b), 0, 0),
            Instr::St8(a, b) => (0x31, r(a), r(b), 0, 0),
            Instr::Sha256(a, b, c) => (0x40, r(a), r(b), r(c), 0),
            Instr::RoHash(a, b, c) => (0x42, r(a), r(b), r(c), 0),
            Instr::MemEq(a, b, c, d) => (0x41, r(a), r(b), r(c), d as u32),
            Instr::Out(k, a, b) => (0x50, r(a), r(b), 0, k as u32),
        }
    }

    /// `Instr.encode`: 8 bytes.
    pub fn encode(self) -> [u8; 8] {
        let (op, a, b, c, imm) = self.fields();
        let i = imm.to_le_bytes();
        [op, a, b, c, i[0], i[1], i[2], i[3]]
    }
}

/// `Program`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    /// `<= MAX_MEM_SIZE`.
    pub mem_size: u32,
    /// `data.len() <= mem_size`.
    pub data: Vec<u8>,
    /// `code.len() <= MAX_CODE_LEN`.
    pub code: Vec<Instr>,
}

fn u32le(b: &[u8]) -> u32 {
    u32::from_le_bytes([b[0], b[1], b[2], b[3]])
}

/// `decode`: `"NPAI" ‖ 0x01 ‖ memSize:u32le ‖ dataLen:u32le ‖ data ‖
/// codeLen:u32le ‖ code`, trailing bytes rejected. `None` = decode error.
pub fn decode(b: &[u8]) -> Option<Program> {
    if b.len() < 13 || b[0..4] != MAGIC || b[4] != VERSION {
        return None;
    }
    let mem_size = u32le(&b[5..9]);
    let data_len = u32le(&b[9..13]);
    let rest = &b[13..];
    if !(mem_size as u64 <= MAX_MEM_SIZE
        && data_len <= mem_size
        && data_len as u64 <= rest.len() as u64)
    {
        return None;
    }
    let (data, after) = rest.split_at(data_len as usize);
    if after.len() < 4 {
        return None;
    }
    let code_len = u32le(&after[0..4]);
    if code_len as u64 > MAX_CODE_LEN {
        return None;
    }
    let code_bytes = &after[4..];
    // decodeCode: exactly `code_len` words, nothing after.
    if code_bytes.len() as u64 != code_len as u64 * 8 {
        return None;
    }
    let mut code = Vec::with_capacity(code_len as usize);
    for w in code_bytes.chunks_exact(8) {
        code.push(Instr::decode(w[0], w[1], w[2], w[3], u32le(&w[4..8]))?);
    }
    Some(Program {
        mem_size,
        data: data.to_vec(),
        code,
    })
}

/// `encode` (inverse of `decode` on well-formed programs).
pub fn encode(p: &Program) -> Vec<u8> {
    let mut out = Vec::with_capacity(17 + p.data.len() + 8 * p.code.len());
    out.extend_from_slice(&MAGIC);
    out.push(VERSION);
    out.extend_from_slice(&p.mem_size.to_le_bytes());
    out.extend_from_slice(&(p.data.len() as u32).to_le_bytes());
    out.extend_from_slice(&p.data);
    out.extend_from_slice(&(p.code.len() as u32).to_le_bytes());
    for i in &p.code {
        out.extend_from_slice(&i.encode());
    }
    out
}

/// `Inputs`.
#[derive(Clone, Copy, Debug)]
pub struct Inputs<'a> {
    pub public: &'a [u8],
    pub claim: &'a [u8],
    pub proof: &'a [u8],
}

impl<'a> Inputs<'a> {
    /// `Inputs.tape`
    fn tape(&self, t: Tape) -> &'a [u8] {
        match t {
            Tape::Pub => self.public,
            Tape::Claim => self.claim,
            Tape::Proof => self.proof,
        }
    }
}

/// `Outcome`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Accept,
    Reject,
    Trap,
    OutOfFuel,
}

impl Outcome {
    pub fn as_str(self) -> &'static str {
        match self {
            Outcome::Accept => "accept",
            Outcome::Reject => "reject",
            Outcome::Trap => "trap",
            Outcome::OutOfFuel => "out_of_fuel",
        }
    }
}

/// `State Unit` (deployed hash oracle has no state).
#[derive(Clone, Debug)]
pub struct State {
    pub pc: u64,
    pub regs: [u64; NUM_REGS],
    /// Exactly `mem_size` bytes (Lean: a total function, only `[0, memSize)`
    /// is ever observable because every access is bounds-checked).
    pub mem: Vec<u8>,
    pub fuel: u64,
    pub out0: Vec<u8>,
    pub out1: Vec<u8>,
}

/// `init`.
pub fn init(p: &Program, fuel: u64) -> State {
    let mut mem = vec![0u8; p.mem_size as usize];
    mem[..p.data.len()].copy_from_slice(&p.data);
    State {
        pc: 0,
        regs: [0; NUM_REGS],
        mem,
        fuel,
        out0: vec![],
        out1: vec![],
    }
}

/// `off + len <= limit` in unbounded arithmetic (Lean `Nat.ble (off + len) limit`).
fn fits(off: u64, len: u64, limit: u64) -> bool {
    off as u128 + len as u128 <= limit as u128
}

/// `cost`.
pub fn cost(regs: &[u64; NUM_REGS], i: &Instr) -> u64 {
    match *i {
        Instr::Tcopy(_, _, c, _) => 1 + regs[c] / 64,
        Instr::Sha256(_, _, c) => 1 + regs[c] / 64,
        Instr::RoHash(_, _, c) => 1 + regs[c] / 64,
        Instr::MemEq(_, _, _, d) => 1 + regs[d] / 64,
        Instr::Out(_, _, b) => 1 + regs[b] / 64,
        _ => 1,
    }
}

/// Result of one `step`: `None` = `.next`, `Some(o)` = `.done o`.
type Step = Option<Outcome>;

/// `exec1`: execute one already-fetched and already-paid instruction,
/// mutating `s` in place. On `.done` the state is left as Lean leaves it
/// (unchanged by the instruction, fuel already charged). `record_outputs`
/// only controls whether `OUT` bytes are retained; it never affects control
/// flow, fuel or the outcome (Lean `run` ignores the output buffers).
fn exec1(p: &Program, inp: &Inputs<'_>, s: &mut State, i: Instr, record_outputs: bool) -> Step {
    let mem_size = p.mem_size as u64;
    let next = |s: &mut State| s.pc += 1;
    match i {
        Instr::Halt(a) => {
            return Some(if s.regs[a] == 0 {
                Outcome::Reject
            } else {
                Outcome::Accept
            })
        }
        Instr::Const(a, imm) => {
            s.regs[a] = imm as u64;
            next(s)
        }
        Instr::Mov(a, b) => {
            s.regs[a] = s.regs[b];
            next(s)
        }
        Instr::Bin(op, a, b, c) => {
            s.regs[a] = op.eval(s.regs[b], s.regs[c]);
            next(s)
        }
        Instr::Addi(a, b, imm) => {
            s.regs[a] = s.regs[b].wrapping_add(imm as u64);
            next(s)
        }
        Instr::Jmp(t) => s.pc = t as u64,
        Instr::Jz(a, t) => s.pc = if s.regs[a] == 0 { t as u64 } else { s.pc + 1 },
        Instr::Jnz(a, t) => s.pc = if s.regs[a] == 0 { s.pc + 1 } else { t as u64 },
        Instr::Tlen(a, t) => {
            // Pre-check guarantees len < 2^32, so `% 2^64` is the identity.
            s.regs[a] = inp.tape(t).len() as u64;
            next(s)
        }
        Instr::Tload(a, b, t) => {
            let tp = inp.tape(t);
            let off = s.regs[b];
            if off < tp.len() as u64 {
                s.regs[a] = tp[off as usize] as u64;
                next(s)
            } else {
                return Some(Outcome::Trap);
            }
        }
        Instr::Tcopy(a, b, c, t) => {
            let tp = inp.tape(t);
            let (dst, src, len) = (s.regs[a], s.regs[b], s.regs[c]);
            if fits(src, len, tp.len() as u64) && fits(dst, len, mem_size) {
                // All three are now <= 2^32: usize arithmetic cannot overflow.
                let (dst, src, len) = (dst as usize, src as usize, len as usize);
                s.mem[dst..dst + len].copy_from_slice(&tp[src..src + len]);
                next(s)
            } else {
                return Some(Outcome::Trap);
            }
        }
        Instr::Ld8(a, b) => {
            let addr = s.regs[b];
            if addr < mem_size {
                s.regs[a] = s.mem[addr as usize] as u64;
                next(s)
            } else {
                return Some(Outcome::Trap);
            }
        }
        Instr::St8(a, b) => {
            let addr = s.regs[a];
            if addr < mem_size {
                s.mem[addr as usize] = (s.regs[b] % 256) as u8;
                next(s)
            } else {
                return Some(Outcome::Trap);
            }
        }
        Instr::Sha256(a, b, c) | Instr::RoHash(a, b, c) => {
            let (dst, src, len) = (s.regs[a], s.regs[b], s.regs[c]);
            if fits(src, len, mem_size) && fits(dst, 32, mem_size) {
                let (dst, src, len) = (dst as usize, src as usize, len as usize);
                let mut h = Sha256::new();
                if matches!(i, Instr::RoHash(..)) {
                    h.update(RO_TAG);
                }
                // Read before write: the digest is computed from the
                // pre-instruction memory, then written.
                h.update(&s.mem[src..src + len]);
                let d = h.finalize();
                s.mem[dst..dst + 32].copy_from_slice(&d);
                next(s)
            } else {
                return Some(Outcome::Trap);
            }
        }
        Instr::MemEq(a, b, c, d) => {
            let (x, y, len) = (s.regs[b], s.regs[c], s.regs[d]);
            if fits(x, len, mem_size) && fits(y, len, mem_size) {
                let (x, y, len) = (x as usize, y as usize, len as usize);
                s.regs[a] = (s.mem[x..x + len] == s.mem[y..y + len]) as u64;
                next(s)
            } else {
                return Some(Outcome::Trap);
            }
        }
        Instr::Out(k, a, b) => {
            let (x, len) = (s.regs[a], s.regs[b]);
            if fits(x, len, mem_size) {
                if record_outputs {
                    let (x, len) = (x as usize, len as usize);
                    let bytes = &s.mem[x..x + len];
                    if k == 0 {
                        s.out0.extend_from_slice(bytes);
                    } else {
                        s.out1.extend_from_slice(bytes);
                    }
                }
                next(s)
            } else {
                return Some(Outcome::Trap);
            }
        }
    }
    None
}

/// `step`: fetch (trap if `pc` out of range, no charge), charge fuel
/// (`outOfFuel` with the state unchanged if insufficient), execute.
fn step(p: &Program, inp: &Inputs<'_>, s: &mut State, record_outputs: bool) -> Step {
    let ins = match usize::try_from(s.pc).ok().and_then(|pc| p.code.get(pc)) {
        None => return Some(Outcome::Trap),
        Some(i) => *i,
    };
    let c = cost(&s.regs, &ins);
    if s.fuel < c {
        return Some(Outcome::OutOfFuel);
    }
    s.fuel -= c;
    exec1(p, inp, s, ins, record_outputs)
}

/// `runWith deployedRO ()` / `runFull`: tape-length pre-check, then `exec`.
///
/// Lean's `exec` additionally bounds the loop by `gas = fuel + 1`; every
/// executed step costs >= 1 fuel, so that bound is never reached before
/// `outOfFuel` and is omitted here (see `docs/INTERP_SPEC.md` §5).
pub fn run_full(
    p: &Program,
    inp: &Inputs<'_>,
    fuel: u64,
    record_outputs: bool,
) -> (Outcome, State) {
    let mut s = init(p, fuel);
    let too_long = |t: &[u8]| t.len() as u64 >= MAX_TAPE_LEN;
    if too_long(inp.public) || too_long(inp.claim) || too_long(inp.proof) {
        return (Outcome::Trap, s);
    }
    loop {
        if let Some(o) = step(p, inp, &mut s, record_outputs) {
            return (o, s);
        }
    }
}

/// `run`: `Some(true)` accept, `Some(false)` reject, `None` trap/out of fuel.
pub fn run(p: &Program, inp: &Inputs<'_>, fuel: u64) -> Option<bool> {
    match run_full(p, inp, fuel, false).0 {
        Outcome::Accept => Some(true),
        Outcome::Reject => Some(false),
        _ => None,
    }
}

/// `runOut`: output buffers of an accepting run.
pub fn run_out(p: &Program, inp: &Inputs<'_>, fuel: u64) -> Option<(Vec<u8>, Vec<u8>)> {
    match run_full(p, inp, fuel, true) {
        (Outcome::Accept, s) => Some((s.out0, s.out1)),
        _ => None,
    }
}

/// `interpVerify`: decode the image and run it; anything but `accept`
/// (including a decode error) is rejection.
pub fn interp_verify(image: &[u8], fuel: u64, inp: &Inputs<'_>) -> bool {
    match decode(image) {
        Some(p) => run(&p, inp, fuel) == Some(true),
        None => false,
    }
}

/// Full observable result in the format of `arena-interp-ref` (`expect`):
/// `None` = decode error, else `(outcome, fuel_used, out0, out1)`.
pub fn expect(
    image: &[u8],
    inp: &Inputs<'_>,
    fuel: u64,
) -> Option<(Outcome, u64, Vec<u8>, Vec<u8>)> {
    let p = decode(image)?;
    let (o, s) = run_full(&p, inp, fuel, true);
    Some((o, fuel - s.fuel, s.out0, s.out1))
}
