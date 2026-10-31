//! In-circuit Wasm VM execution table (Phase 2 vertical slice) — NPMWASM02.
//!
//! Design (binius64 frontend, no lookup tables — every op is explicit
//! AND-constraints; per-op cost is the central measurement):
//!
//! One witness row per step: pc/tag/a/b/out/c, height, br_taken/br_h/
//! br_ar, mem_addr/mem_word, full stack[64]/locals[16] snapshots. The
//! stack is a fixed-depth register array with a height register:
//!   stack_k[j] = sel(br_taken,
//!       sel(j < br_h, prev[j], sel(j == br_h ∧ ar==1, prev[prev_h-1], 0)),
//!     sel(j < h_k, sel(write ∧ j == h_k-1, out, prev[j]), 0))
//! (branch arities in this interpreter are 0/1, so the branch layer is one
//! value mux; the branch value is the pre-branch TOP, moved to br_h).
//!
//! Height deltas: const/local.get/global.get +1; drop/local.set/global.set
//! /br_if(not taken) −1; eqz/load 0 (replace top); alu −1 (pops2 push1);
//! select/store −2. Write slot = h_k − 1 for pushes, loads, eqz, alu,
//! select.
//!
//! MSB-bool discipline (the vmul/shortmac lessons): icmp/select/bnot
//! carry truth in bit 63 ONLY; they gate asserts/selects directly.
//! Comparison RESULTS pushed as data go through bool01 (0/1 word).
//! Barrel bits are icmp_ne(band(x,1<<k),0) — never bare 0/1 words.
//!
//! Banks: memory (128 words) and globals (8) are running registers
//! threaded across steps with per-word selects (read-over-write scans
//! measured ~5x costlier and were rejected). Loads assert against the
//! bank (fresh by construction). Stores rebuild the addressed word from
//! the bank word (unchanged bytes) and b (written bytes) at the byte
//! position addr&7, per store width (unaligned 4/1-byte ops supported).
//! Alignment asserts: i64 ops %8; 4-byte ops %4; byte ops any (a slice
//! bound — the interpreter itself is byte-granular).
//!
//! Bindings (anti-fabrication): code words (witness) tight_sha256 == the
//! PUBLIC code digest + PUBLIC code_len; init words (witness) tight_sha256
//! == the PUBLIC init digest. The trace runs on the audited bytecode from
//! the audited state. The tag-sequence <-> code correspondence (opcode
//! byte read per step + label-table walk) is the stated code-walk
//! follow-up: this rung trusts the fixture's step order/branch metadata
//! (an honest, named bound, host-audited by regeneration + battery).
//!
//! Gas: +1 per active step (slice profile), asserted == the public total.
//! NOT full NEAR validity: bounded slice per WASM_SLICE_DEF.md; no div in
//! circuit rungs; no host calls; single function; fixed trips.
use binius_frontend::{CircuitBuilder, Wire};
use binius_circuits::fixed_byte_vec::ByteVec;
use binius_circuits::multiplexer::single_wire_multiplex;
use crate::tight_sha;

pub const MAX_STEPS: usize = 2048;
pub const N_STACK: usize = 64;
pub const N_LOCALS: usize = 16;
pub const N_GLOBALS: usize = 8;
pub const MEM_WORDS: usize = 128; // 1024 B
pub const CODE_WORDS: usize = 2048; // 16384 B

// Opcode tags (wasm_trace_export.OP_TAGS): i32 family 1..=22 (eqz at 1),
// i64 family 23..=44 (eqz at 23), misc 45..=68.
pub const T_I32_FIRST: u64 = 1;
pub const T_EQZ_I32: u64 = 1;
pub const T_I64_FIRST: u64 = 23;
pub const T_EQZ_I64: u64 = 23;
pub const T_MISC_FIRST: u64 = 45;
pub const T_I32_CONST: u64 = 45;
pub const T_I64_CONST: u64 = 46;
pub const T_DROP: u64 = 47;
pub const T_SELECT: u64 = 48;
pub const T_LOCAL_GET: u64 = 49;
pub const T_LOCAL_SET: u64 = 50;
pub const T_LOCAL_TEE: u64 = 51;
pub const T_GLOBAL_GET: u64 = 52;
pub const T_GLOBAL_SET: u64 = 53;
pub const T_BLOCK: u64 = 54;
pub const T_LOOP: u64 = 55;
pub const T_BR: u64 = 56;
pub const T_BR_IF: u64 = 57;
pub const T_RETURN: u64 = 58;
pub const T_END: u64 = 59;
pub const T_NOP: u64 = 60;
pub const T_I32_LOAD: u64 = 61;
pub const T_I64_LOAD: u64 = 62;
pub const T_I32_LOAD8U: u64 = 63;
pub const T_I64_LOAD32U: u64 = 64;
pub const T_I32_STORE: u64 = 65;
pub const T_I64_STORE: u64 = 66;
pub const T_I32_STORE8: u64 = 67;
pub const T_I64_STORE32: u64 = 68;

pub struct ExecTable {
    pub n_steps: Wire,
    pub gas_total: Wire,
    pub result: Wire,
    pub code_len: Wire,
    pub code_digest: [Wire; 4],
    pub init_digest: [Wire; 4],
    pub steps: Vec<StepRow>,
    pub init_stack: Vec<Wire>,
    pub init_locals: Vec<Wire>,
    pub init_globals: Vec<Wire>,
    pub init_mem: Vec<Wire>,
    pub fin_stack: Vec<Wire>,
    pub fin_locals: Vec<Wire>,
    pub fin_globals: Vec<Wire>,
    pub code_words: Vec<Wire>,
}

pub struct StepRow {
    pub pc: Wire,
    pub tag: Wire,
    pub a: Wire,
    pub b: Wire,
    pub out: Wire,
    pub c: Wire,
    pub height: Wire,
    pub br_taken: Wire,
    pub br_h: Wire,
    pub br_ar: Wire,
    pub mem_addr: Wire,
    pub mem_word: Wire,
    pub stack: Vec<Wire>,
    pub locals: Vec<Wire>,
}

// ---- MSB-bool primitives ----

#[inline]
fn bool01(b: &CircuitBuilder, c: Wire) -> Wire {
    b.select(c, b.add_constant_64(1), b.add_constant_64(0))
}

#[inline]
fn is_tag(b: &CircuitBuilder, tag: Wire, k: u64) -> Wire {
    b.icmp_eq(tag, b.add_constant_64(k))
}

fn tag_in(b: &CircuitBuilder, tag: Wire, lo: u64, hi: u64) -> Wire {
    b.band(b.icmp_uge(tag, b.add_constant_64(lo)), b.icmp_ule(tag, b.add_constant_64(hi)))
}

// ---- class fans (MSB-bools) ----

/// Two-operand ALU ops (both families minus eqz).
fn is_alu(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(tag_in(b, tag, T_I32_FIRST + 1, T_I64_FIRST - 1),
          tag_in(b, tag, T_I64_FIRST + 1, T_MISC_FIRST - 1))
}

fn is_eqz(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(is_tag(b, tag, T_EQZ_I32), is_tag(b, tag, T_EQZ_I64))
}

fn is_load(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(b.bor(is_tag(b, tag, T_I32_LOAD), is_tag(b, tag, T_I64_LOAD)),
          b.bor(is_tag(b, tag, T_I32_LOAD8U), is_tag(b, tag, T_I64_LOAD32U)))
}

fn is_store(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(b.bor(is_tag(b, tag, T_I32_STORE), is_tag(b, tag, T_I64_STORE)),
          b.bor(is_tag(b, tag, T_I32_STORE8), is_tag(b, tag, T_I64_STORE32)))
}

/// Net height +1 (pushes a new slot).
fn is_push(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(b.bor(is_tag(b, tag, T_I32_CONST), is_tag(b, tag, T_I64_CONST)),
          b.bor(is_tag(b, tag, T_LOCAL_GET), is_tag(b, tag, T_GLOBAL_GET)))
}

/// Net height -1.
fn is_pop1(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(b.bor(is_tag(b, tag, T_DROP), is_tag(b, tag, T_LOCAL_SET)),
          b.bor(is_tag(b, tag, T_GLOBAL_SET), is_tag(b, tag, T_BR_IF)))
}

/// Net height -2.
fn is_pop2(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(is_tag(b, tag, T_SELECT), is_store(b, tag))
}

/// Writes a result at slot h_k - 1.
fn is_write(b: &CircuitBuilder, tag: Wire) -> Wire {
    b.bor(b.bor(is_push(b, tag), is_load(b, tag)),
          b.bor(b.bor(is_eqz(b, tag), is_alu(b, tag)), is_tag(b, tag, T_SELECT)))
}

// ---- barrel shifts (bits as MSB-bools) ----

fn bits_msb(b: &CircuitBuilder, x: Wire, n_bits: u32) -> Vec<Wire> {
    (0..n_bits)
        .map(|k| b.icmp_ne(b.band(x, b.add_constant_64(1u64 << k)), b.add_constant_64(0)))
        .collect()
}

fn barrel_shl(b: &CircuitBuilder, v: Wire, bits: &[Wire]) -> Wire {
    let mut x = v;
    for (i, &bit) in bits.iter().enumerate() {
        x = b.select(bit, b.shl(x, (1u64 << i) as u32), x);
    }
    x
}

fn barrel_shr(b: &CircuitBuilder, v: Wire, bits: &[Wire]) -> Wire {
    let mut x = v;
    for (i, &bit) in bits.iter().enumerate() {
        x = b.select(bit, b.shr(x, (1u64 << i) as u32), x);
    }
    x
}

/// Shift-add mul ladder (no IntMul channel in this pipeline).
fn mul_ladder(b: &CircuitBuilder, a: Wire, x: Wire, n_bits: u32) -> Wire {
    let zero = b.add_constant_64(0);
    let mut acc = zero;
    for k in 0..n_bits {
        let bit = b.icmp_ne(b.band(x, b.add_constant_64(1u64 << k)), zero);
        acc = b.iadd(acc, b.select(bit, b.shl(a, k), zero)).0;
    }
    acc
}

/// The shared ALU candidate chain: all 42 binop results, selected by tag.
fn alu_chain(b: &CircuitBuilder, a: Wire, x: Wire, tag: Wire) -> Wire {
    let zero = b.add_constant_64(0);
    let m32 = b.add_constant_64(0xFFFF_FFFF);
    let a32 = b.band(a, m32);
    let x32 = b.band(x, m32);
    let flip32 = b.add_constant_64(0x8000_0000);
    let flip64 = b.add_constant_64(0x8000_0000_0000_0000);
    // signed compare via xor-flip: lt_s(u,v)=ult(u^f,v^f); ge_s(u,v)=uge(u^f,v^f)
    let slt = |u: Wire, v: Wire, f: Wire| b.icmp_ult(b.bxor(u, f), b.bxor(v, f));
    let sge = |u: Wire, v: Wire, f: Wire| b.icmp_uge(b.bxor(u, f), b.bxor(v, f));
    let k32 = b.band(x32, b.add_constant_64(31));
    let k64 = b.band(x, b.add_constant_64(63));
    let bits32 = bits_msb(b, k32, 5);
    let bits64 = bits_msb(b, k64, 6);
    let notbits32: Vec<Wire> = bits32.iter().map(|&w| b.bnot(w)).collect();
    let notbits64: Vec<Wire> = bits64.iter().map(|&w| b.bnot(w)).collect();
    // i32 shr_s: sign-extend a32 then logical-shift
    let a32_sext = b.bor(a32, b.select(b.icmp_uge(a32, flip32),
                                       b.add_constant_64(0xFFFF_FFFF_0000_0000), zero));
    // i64 shr_s: logical shift OR sign-fill (high k bits when bit63 set)
    let shr_s64 = {
        let sh = barrel_shr(b, a, &bits64);
        let ones = b.add_constant_64(u64::MAX);
        let fill = b.bnot(barrel_shr(b, ones, &bits64));
        b.select(b.icmp_uge(a, flip64), b.bor(sh, fill), sh)
    };
    // rotates: (v<<k) | (v>>(w-k)); NOT-bits give w-1-k, >>1 -> w-k; k=0 -> 0
    let rotl32 = b.band(b.bor(barrel_shl(b, a32, &bits32),
                              b.shr(barrel_shr(b, a32, &notbits32), 1)), m32);
    let rotr32 = b.band(b.bor(barrel_shr(b, a32, &bits32),
                             b.shl(barrel_shl(b, a32, &notbits32), 1)), m32);
    let rotl64 = b.bor(barrel_shl(b, a, &bits64),
                       b.shr(barrel_shr(b, a, &notbits64), 1));
    let rotr64 = b.bor(barrel_shr(b, a, &bits64),
                       b.shl(barrel_shl(b, a, &notbits64), 1));
    let mut r = zero;
    // OP_TAGS order per family: eq,ne,lt_s,lt_u,gt_s,gt_u,le_s,le_u,ge_s,
    // ge_u,add,sub,mul,and,or,xor,shl,shr_s,shr_u,rotl,rotr (21 ops)
    for (i32k, i64k) in ((T_I32_FIRST + 1)..T_I64_FIRST).zip((T_I64_FIRST + 1)..T_MISC_FIRST) {
        let (c32, c64) = match i32k - T_I32_FIRST {
            1 => (bool01(b, b.icmp_eq(a32, x32)), bool01(b, b.icmp_eq(a, x))),
            2 => (bool01(b, b.icmp_ne(a32, x32)), bool01(b, b.icmp_ne(a, x))),
            3 => (bool01(b, slt(a32, x32, flip32)), bool01(b, slt(a, x, flip64))),
            4 => (bool01(b, b.icmp_ult(a32, x32)), bool01(b, b.icmp_ult(a, x))),
            5 => (bool01(b, slt(x32, a32, flip32)), bool01(b, slt(x, a, flip64))),
            6 => (bool01(b, b.icmp_ult(x32, a32)), bool01(b, b.icmp_ult(x, a))),
            7 => (bool01(b, sge(x32, a32, flip32)), bool01(b, sge(x, a, flip64))),  // le_s
            8 => (bool01(b, b.icmp_ule(a32, x32)), bool01(b, b.icmp_ule(a, x))),
            9 => (bool01(b, sge(a32, x32, flip32)), bool01(b, sge(a, x, flip64))), // ge_s
            10 => (bool01(b, b.icmp_ule(x32, a32)), bool01(b, b.icmp_ule(x, a))),
            11 => (b.band(b.iadd(a32, x32).0, m32), b.iadd(a, x).0),
            12 => (b.band(b.isub_bin_bout(a32, x32, zero).0, m32), b.isub_bin_bout(a, x, zero).0),
            13 => (b.band(mul_ladder(b, a32, x32, 32), m32), mul_ladder(b, a, x, 64)),
            14 => (b.band(b.band(a32, x32), m32), b.band(a, x)),
            15 => (b.band(b.bor(a32, x32), m32), b.bor(a, x)),
            16 => (b.band(b.bxor(a32, x32), m32), b.bxor(a, x)),
            17 => (b.band(barrel_shl(b, a32, &bits32), m32), barrel_shl(b, a, &bits64)),
            18 => (b.band(barrel_shr(b, a32_sext, &bits32), m32), shr_s64),
            19 => (b.band(barrel_shr(b, a32, &bits32), m32), barrel_shr(b, a, &bits64)),
            20 => (rotl32, rotl64),
            _ => (rotr32, rotr64),
        };
        r = b.select(is_tag(b, tag, i32k), c32, r);
        r = b.select(is_tag(b, tag, i64k), c64, r);
    }
    r
}

// ---- construction ----

pub fn build(b: &CircuitBuilder, max_steps: usize) -> ExecTable {
    let n_steps = b.add_inout();
    let gas_total = b.add_inout();
    let result = b.add_inout();
    let code_len = b.add_inout();
    let code_digest: [Wire; 4] = core::array::from_fn(|_| b.add_inout());
    let init_digest: [Wire; 4] = core::array::from_fn(|_| b.add_inout());
    let mut steps = Vec::with_capacity(max_steps);
    for k in 0..max_steps {
        let s = b.subcircuit(format!("step-{k}"));
        let stack: Vec<Wire> = (0..N_STACK).map(|_| s.add_witness()).collect();
        let locals: Vec<Wire> = (0..N_LOCALS).map(|_| s.add_witness()).collect();
        steps.push(StepRow {
            pc: s.add_witness(), tag: s.add_witness(), a: s.add_witness(),
            b: s.add_witness(), out: s.add_witness(), c: s.add_witness(),
            height: s.add_witness(), br_taken: s.add_witness(),
            br_h: s.add_witness(), br_ar: s.add_witness(),
            mem_addr: s.add_witness(), mem_word: s.add_witness(),
            stack, locals,
        });
    }
    let section = |name: &str, n: usize| -> Vec<Wire> {
        let s = b.subcircuit(name);
        (0..n).map(|_| s.add_witness()).collect()
    };
    let init_stack = section("init-stack", N_STACK);
    let init_locals = section("init-locals", N_LOCALS);
    let init_globals = section("init-globals", N_GLOBALS);
    let init_mem = section("init-mem", MEM_WORDS);
    let fin_stack = section("fin-stack", N_STACK);
    let fin_locals = section("fin-locals", N_LOCALS);
    let fin_globals = section("fin-globals", N_GLOBALS);
    let code_words = section("code-words", CODE_WORDS);
    ExecTable { n_steps, gas_total, result, code_len, code_digest, init_digest,
                steps, init_stack, init_locals, init_globals, init_mem,
                fin_stack, fin_locals, fin_globals, code_words }
}

// ---- fixture parsing (host reading only; semantics is the circuit's job) ----

pub struct StepData {
    pub pc: u64, pub tag: u64, pub a: u64, pub b: u64, pub out: u64, pub c: u64,
    pub height: u64, pub br_taken: u64, pub br_h: u64, pub br_ar: u64,
    pub mem_addr: u64, pub mem_word: u64,
    pub stack: Vec<u64>, pub locals: Vec<u64>,
}

pub struct Fixture {
    pub n_steps: usize,
    pub gas_total: u64,
    pub result: u64,
    pub code: Vec<u8>,
    pub code_digest: [u64; 4],
    pub init_digest: [u64; 4],
    pub init_stack: Vec<u64>,
    pub init_locals: Vec<u64>,
    pub init_globals: Vec<u64>,
    pub init_mem: Vec<u64>,
    pub steps: Vec<StepData>,
    pub fin_stack: Vec<u64>,
    pub fin_locals: Vec<u64>,
    pub fin_globals: Vec<u64>,
}

pub fn parse_fixture(raw: &[u8]) -> Fixture {
    assert_eq!(&raw[..9], b"NPMWASM02", "fixture magic");
    let rd64 = |o: usize| u64::from_le_bytes(raw[o..o + 8].try_into().unwrap());
    let rd32 = |o: usize| u32::from_le_bytes(raw[o..o + 4].try_into().unwrap()) as usize;
    let be64 = |o: usize| u64::from_be_bytes(raw[o..o + 8].try_into().unwrap());
    assert_eq!(rd32(9), 2, "version");
    let n_steps = rd32(13);
    assert_eq!(rd32(17), N_STACK, "stack profile");
    assert_eq!(rd32(21), N_LOCALS, "locals profile");
    assert_eq!(rd32(25), N_GLOBALS, "globals profile");
    assert_eq!(rd32(29), MEM_WORDS, "memory profile");
    let code_len = rd32(33);
    assert!(code_len <= CODE_WORDS * 8, "code budget");
    let code = raw[37..37 + code_len].to_vec();
    let mut pos = 37 + code_len;
    let gas_total = rd64(pos);
    pos += 8;
    let code_digest = [be64(pos), be64(pos + 8), be64(pos + 16), be64(pos + 24)];
    pos += 32;
    let init_digest = [be64(pos), be64(pos + 8), be64(pos + 16), be64(pos + 24)];
    pos += 32;
    let mut words = |pos: &mut usize, n: usize| -> Vec<u64> {
        let v: Vec<u64> = (0..n).map(|i| rd64(*pos + 8 * i)).collect();
        *pos += 8 * n;
        v
    };
    let init_stack = words(&mut pos, N_STACK);
    let init_locals = words(&mut pos, N_LOCALS);
    let init_globals = words(&mut pos, N_GLOBALS);
    let init_mem = words(&mut pos, MEM_WORDS);
    let mut steps = Vec::with_capacity(n_steps);
    for _ in 0..n_steps {
        let pc = rd32(pos) as u64;
        let tag = rd32(pos + 4) as u64;
        let a = rd64(pos + 8);
        let b = rd64(pos + 16);
        let out = rd64(pos + 24);
        let c = rd64(pos + 32);
        let height = rd32(pos + 40) as u64;
        let _code_off = rd32(pos + 44);
        pos += 52; // 40 header + height(4) + code_off(4) + pad(4)
        let br_taken = rd64(pos);
        let br_h = rd64(pos + 8);
        let br_ar = rd64(pos + 16);
        let mem_addr = rd64(pos + 24);
        let mem_word = rd64(pos + 32);
        pos += 40;
        let stack = words(&mut pos, N_STACK);
        let locals = words(&mut pos, N_LOCALS);
        steps.push(StepData { pc, tag, a, b, out, c, height, br_taken, br_h,
                             br_ar, mem_addr, mem_word, stack, locals });
    }
    let fin_stack = words(&mut pos, N_STACK);
    let fin_locals = words(&mut pos, N_LOCALS);
    let fin_globals = words(&mut pos, N_GLOBALS);
    let result = rd64(pos);
    pos += 8;
    let _kind = rd32(pos);
    pos += 4;
    let _fixture_digest = &raw[pos..pos + 32];
    pos += 32;
    assert_eq!(pos, raw.len(), "fixture consumed");
    Fixture { n_steps, gas_total, result, code, code_digest, init_digest,
              init_stack, init_locals, init_globals, init_mem, steps,
              fin_stack, fin_locals, fin_globals }
}

pub fn fill(w: &mut binius_frontend::WitnessFiller, t: &ExecTable, f: &Fixture) {
    use binius_core::word::Word;
    w[t.n_steps] = Word(f.n_steps as u64);
    w[t.gas_total] = Word(f.gas_total);
    w[t.result] = Word(f.result);
    w[t.code_len] = Word(f.code.len() as u64);
    for (x, v) in t.code_digest.iter().zip(f.code_digest) { w[*x] = Word(v); }
    for (x, v) in t.init_digest.iter().zip(f.init_digest) { w[*x] = Word(v); }
    let mut code_words = vec![0u64; CODE_WORDS];
    for (i, &byte) in f.code.iter().enumerate() {
        code_words[i / 8] |= (byte as u64) << (8 * (i % 8));
    }
    for (x, v) in t.code_words.iter().zip(code_words) { w[*x] = Word(v); }
    for (x, v) in t.init_stack.iter().zip(&f.init_stack) { w[*x] = Word(*v); }
    for (x, v) in t.init_locals.iter().zip(&f.init_locals) { w[*x] = Word(*v); }
    for (x, v) in t.init_globals.iter().zip(&f.init_globals) { w[*x] = Word(*v); }
    for (x, v) in t.init_mem.iter().zip(&f.init_mem) { w[*x] = Word(*v); }
    for (x, v) in t.fin_stack.iter().zip(&f.fin_stack) { w[*x] = Word(*v); }
    for (x, v) in t.fin_locals.iter().zip(&f.fin_locals) { w[*x] = Word(*v); }
    for (x, v) in t.fin_globals.iter().zip(&f.fin_globals) { w[*x] = Word(*v); }
    for (i, s) in t.steps.iter().enumerate() {
        match f.steps.get(i) {
            Some(d) => {
                w[s.pc] = Word(d.pc); w[s.tag] = Word(d.tag);
                w[s.a] = Word(d.a); w[s.b] = Word(d.b); w[s.out] = Word(d.out);
                w[s.c] = Word(d.c); w[s.height] = Word(d.height);
                w[s.br_taken] = Word(d.br_taken); w[s.br_h] = Word(d.br_h);
                w[s.br_ar] = Word(d.br_ar);
                w[s.mem_addr] = Word(d.mem_addr); w[s.mem_word] = Word(d.mem_word);
                for (x, v) in s.stack.iter().zip(&d.stack) { w[*x] = Word(*v); }
                for (x, v) in s.locals.iter().zip(&d.locals) { w[*x] = Word(*v); }
            }
            None => {
                w[s.pc] = Word(0); w[s.tag] = Word(0);
                w[s.a] = Word(0); w[s.b] = Word(0); w[s.out] = Word(0);
                w[s.c] = Word(0); w[s.height] = Word(0);
                w[s.br_taken] = Word(0); w[s.br_h] = Word(0); w[s.br_ar] = Word(0);
                w[s.mem_addr] = Word(0); w[s.mem_word] = Word(0);
                for x in s.stack.iter() { w[*x] = Word(0); }
                for x in s.locals.iter() { w[*x] = Word(0); }
            }
        }
    }
}

// ---- the constraint set ----

pub fn constrain(b: &CircuitBuilder, t: &ExecTable) {
    let zero = b.add_constant_64(0);
    let one = b.add_constant_64(1);
    let two = b.add_constant_64(2);
    let m32 = b.add_constant_64(0xFFFF_FFFF);
    let m1 = b.add_constant_64(u64::MAX);      // -1 mod 2^64
    let m2 = b.add_constant_64(u64::MAX - 1);  // -2 mod 2^64
    let hmax = b.add_constant_64(63);
    let mem_max = b.add_constant_64((MEM_WORDS * 8 - 1) as u64);
    let n_reg = b.add_constant_64((N_LOCALS - 1) as u64);
    let g_reg = b.add_constant_64((N_GLOBALS - 1) as u64);

    // ---- public digest bindings ----
    b.assert_false("code-len-cap", b.icmp_ugt(t.code_len, b.add_constant_64((CODE_WORDS * 8) as u64)));
    let code_vec = ByteVec::new_with_len_range(t.code_words.clone(), t.code_len, 0..=CODE_WORDS * 8);
    let cd = tight_sha::sha256_tight(&b.subcircuit("code-digest"), &code_vec, CODE_WORDS * 8);
    for i in 0..4 { b.assert_eq(format!("code-digest-{i}"), cd[i], t.code_digest[i]); }
    let mut init_words = Vec::with_capacity(N_STACK + N_LOCALS + N_GLOBALS + MEM_WORDS);
    init_words.extend(t.init_stack.iter().copied());
    init_words.extend(t.init_locals.iter().copied());
    init_words.extend(t.init_globals.iter().copied());
    init_words.extend(t.init_mem.iter().copied());
    let init_len = init_words.len() * 8;
    let init_vec = ByteVec::new_with_len_range(init_words, b.add_constant_64(init_len as u64), init_len..=init_len);
    let id = tight_sha::sha256_tight(&b.subcircuit("init-digest"), &init_vec, init_len);
    for i in 0..4 { b.assert_eq(format!("init-digest-{i}"), id[i], t.init_digest[i]); }

    // ---- bounds ----
    b.assert_false("n-steps-cap", b.icmp_ugt(t.n_steps, b.add_constant_64(t.steps.len() as u64)));

    // ---- threaded state ----
    let mut mem_bank: Vec<Wire> = t.init_mem.clone();
    let mut glob_bank: Vec<Wire> = t.init_globals.clone();
    let mut gas = zero;
    let mut fin_stack_reg: Vec<Wire> = vec![zero; N_STACK];
    let mut fin_locals_reg: Vec<Wire> = vec![zero; N_LOCALS];
    let mut fin_globals_reg: Vec<Wire> = vec![zero; N_GLOBALS];
    let mut last_h = zero;

    for (k, s) in t.steps.iter().enumerate() {
        let k_const = b.add_constant_64(k as u64);
        let active = b.icmp_ult(k_const, t.n_steps);
        let is_last = b.band(active, b.icmp_eq(k_const, b.isub_bin_bout(t.n_steps, one, zero).0));
        let tag = s.tag;
        let alu = is_alu(b, tag);
        let eqz = is_eqz(b, tag);
        let load = is_load(b, tag);
        let store = is_store(b, tag);
        let push = is_push(b, tag);
        let pop1 = is_pop1(b, tag);
        let pop2 = is_pop2(b, tag);
        let write = is_write(b, tag);
        let sel_op = is_tag(b, tag, T_SELECT);
        let br_op = is_tag(b, tag, T_BR);
        let br_if_op = is_tag(b, tag, T_BR_IF);
        let localset = b.bor(is_tag(b, tag, T_LOCAL_SET), is_tag(b, tag, T_LOCAL_TEE));
        let localget = is_tag(b, tag, T_LOCAL_GET);
        let globset = is_tag(b, tag, T_GLOBAL_SET);
        let globget = is_tag(b, tag, T_GLOBAL_GET);
        let is_const = b.bor(is_tag(b, tag, T_I32_CONST), is_tag(b, tag, T_I64_CONST));

        let prev_stack: Vec<Wire> = if k == 0 { t.init_stack.clone() } else { t.steps[k - 1].stack.clone() };
        let prev_locals: Vec<Wire> = if k == 0 { t.init_locals.clone() } else { t.steps[k - 1].locals.clone() };
        let prev_h = if k == 0 { zero } else { t.steps[k - 1].height };

        // ---- branch metadata ----
        let br_bool = b.icmp_ne(s.br_taken, zero);
        b.assert_eq_cond(format!("br-always-{k}"), s.br_taken, one, b.band(active, br_op));
        b.assert_eq_cond(format!("brif-taken-{k}"), s.br_taken, bool01(b, b.icmp_ne(s.a, zero)),
                         b.band(active, br_if_op));
        let not_br = b.bnot(b.bor(br_op, br_if_op));
        b.assert_eq_cond(format!("br-never-{k}"), s.br_taken, zero, b.band(active, not_br));
        b.assert_false(format!("br-ar-bound-{k}"), b.band(b.band(active, br_bool), b.icmp_ugt(s.br_ar, one)));
        b.assert_false(format!("br-h-bound-{k}"), b.band(b.band(active, br_bool), b.icmp_ugt(s.br_h, hmax)));

        // ---- height rule ----
        let dh = b.select(push, one,
                  b.select(pop1, m1,
                  b.select(alu, m1,
                  b.select(pop2, m2, zero))));
        let h_next = b.iadd(prev_h, dh).0;
        let h_br = b.iadd(s.br_h, s.br_ar).0;
        b.assert_eq_cond(format!("height-{k}"), s.height, b.select(br_bool, h_br, h_next), active);
        b.assert_false(format!("h-bound-{k}"), b.band(active, b.icmp_ugt(s.height, hmax)));

        // ---- operand binding (muxes over the PREVIOUS stack) ----
        let hm1 = b.isub_bin_bout(prev_h, one, zero).0;
        let hm2 = b.isub_bin_bout(prev_h, two, zero).0;
        let hm3 = b.isub_bin_bout(prev_h, b.add_constant_64(3), zero).0;
        let top = single_wire_multiplex(b, &prev_stack, hm1);
        let second = single_wire_multiplex(b, &prev_stack, hm2);
        let third = single_wire_multiplex(b, &prev_stack, hm3);
        let g_alu = b.band(b.band(active, alu), b.bnot(br_bool));
        b.assert_eq_cond(format!("alu-a-{k}"), s.a, second, g_alu);
        b.assert_eq_cond(format!("alu-b-{k}"), s.b, top, g_alu);
        let g_eqz = b.band(b.band(active, eqz), b.bnot(br_bool));
        b.assert_eq_cond(format!("eqz-a-{k}"), s.a, top, g_eqz);
        b.assert_eq_cond(format!("drop-out-{k}"), s.out, top,
                        b.band(b.band(active, is_tag(b, tag, T_DROP)), b.bnot(br_bool)));
        let g_sel = b.band(b.band(active, sel_op), b.bnot(br_bool));
        b.assert_eq_cond(format!("sel-c-{k}"), s.c, top, g_sel);
        b.assert_eq_cond(format!("sel-b-{k}"), s.b, second, g_sel);
        b.assert_eq_cond(format!("sel-a-{k}"), s.a, third, g_sel);
        let g_brif = b.band(b.band(active, br_if_op), b.bnot(br_bool));
        b.assert_eq_cond(format!("brif-a-{k}"), s.a, top, g_brif);
        let g_set = b.band(b.band(active, b.bor(localset, globset)), b.bnot(br_bool));
        b.assert_eq_cond(format!("set-out-{k}"), s.out, top, g_set);
        // NOTE: tee's stack is UNCHANGED (h same, top already equals out via
        // the constraint above; the snapshot chain carries prev[j] forward).
        let g_store = b.band(b.band(active, store), b.bnot(br_bool));
        b.assert_eq_cond(format!("store-b-{k}"), s.b, top, g_store);
        b.assert_eq_cond(format!("store-a-{k}"), s.a, second, g_store);
        let g_load = b.band(b.band(active, load), b.bnot(br_bool));
        b.assert_eq_cond(format!("load-a-{k}"), s.a, top, g_load);
        b.assert_eq_cond(format!("const-out-{k}"), s.out, s.a,
                         b.band(b.band(active, is_const), b.bnot(br_bool)));

        // ---- results ----
        let chain = alu_chain(b, s.a, s.b, tag);
        b.assert_eq_cond(format!("alu-out-{k}"), s.out, chain, g_alu);
        let ez = b.select(is_tag(b, tag, T_EQZ_I64), bool01(b, b.icmp_eq(s.a, zero)),
                          bool01(b, b.icmp_eq(b.band(s.a, m32), zero)));
        b.assert_eq_cond(format!("eqz-out-{k}"), s.out, ez, g_eqz);
        b.assert_eq_cond(format!("sel-out-{k}"), s.out,
                        b.select(b.icmp_ne(s.c, zero), s.a, s.b), g_sel);

        // ---- locals ----
        // localset only (tee is handled at the stack layer: it writes the
        // local AND keeps the value on the stack).
        let g_localset = b.band(b.band(active, localset), b.bnot(br_bool));
        for j in 0..N_LOCALS {
            let hit = b.band(g_localset, b.icmp_eq(s.a, b.add_constant_64(j as u64)));
            let want = b.select(hit, s.out, prev_locals[j]);
            b.assert_eq_cond(format!("locals-{k}-{j}"), s.locals[j], want, active);
        }
        b.assert_false(format!("localset-idx-{k}"), b.band(g_localset, b.icmp_ugt(s.a, n_reg)));
        let lg = single_wire_multiplex(b, &s.locals, s.a);
        b.assert_eq_cond(format!("localget-out-{k}"), s.out, lg,
                         b.band(b.band(active, localget), b.bnot(br_bool)));
        b.assert_false(format!("localget-idx-{k}"),
                      b.band(b.band(active, localget), b.icmp_ugt(s.a, n_reg)));

        // ---- globals (running bank; globset only) ----
        let g_gs = b.band(b.band(active, globset), b.bnot(br_bool));
        for j in 0..N_GLOBALS {
            let hit = b.band(g_gs, b.icmp_eq(s.a, b.add_constant_64(j as u64)));
            glob_bank[j] = b.select(hit, s.out, glob_bank[j]);
        }
        b.assert_false(format!("globset-idx-{k}"), b.band(g_gs, b.icmp_ugt(s.a, g_reg)));
        let gg = single_wire_multiplex(b, &glob_bank, s.a);
        b.assert_eq_cond(format!("globget-out-{k}"), s.out, gg,
                         b.band(b.band(active, globget), b.bnot(br_bool)));
        b.assert_false(format!("globget-idx-{k}"),
                      b.band(b.band(active, globget), b.icmp_ugt(s.a, g_reg)));

        // ---- memory (running bank; byte-position-aware) ----
        let is_mem = b.bor(load, store);
        let g_mem = b.band(b.band(active, is_mem), b.bnot(br_bool));
        b.assert_false(format!("mem-addr-bound-{k}"), b.band(g_mem, b.icmp_ugt(s.mem_addr, mem_max)));
        // alignment per width: i64 ops %8; 4-byte ops %4; byte ops any
        let g_al8 = b.band(g_mem, b.bor(is_tag(b, tag, T_I64_LOAD), is_tag(b, tag, T_I64_STORE)));
        b.assert_false(format!("mem-align8-{k}"), b.band(g_al8, b.icmp_ne(b.band(s.mem_addr, b.add_constant_64(7)), zero)));
        let g_al4 = b.band(g_mem, b.bor(b.bor(is_tag(b, tag, T_I32_LOAD), is_tag(b, tag, T_I64_LOAD32U)),
                                        b.bor(is_tag(b, tag, T_I32_STORE), is_tag(b, tag, T_I64_STORE32))));
        b.assert_false(format!("mem-align4-{k}"), b.band(g_al4, b.icmp_ne(b.band(s.mem_addr, b.add_constant_64(3)), zero)));
        let word_idx = b.shr(s.mem_addr, 3);
        let cur_word = single_wire_multiplex(b, &mem_bank, word_idx);
        // byte position bits (addr & 7): p2 = bit2 (which half), p0..p2 for bytes
        let p0 = b.icmp_ne(b.band(s.mem_addr, b.add_constant_64(1)), zero);
        let p1 = b.icmp_ne(b.band(s.mem_addr, b.add_constant_64(2)), zero);
        let p2 = b.icmp_ne(b.band(s.mem_addr, b.add_constant_64(4)), zero);
        // loads: mem_word == the bank word (fresh by construction)
        b.assert_eq_cond(format!("load-word-{k}"), s.mem_word, cur_word,
                         b.band(b.band(active, load), b.bnot(br_bool)));
        // load results by width, at the byte position
        let shr_by_pos8 = b.select(p2, b.shr(s.mem_word, 32), b.select(p1, b.shr(s.mem_word, 16), b.select(p0, b.shr(s.mem_word, 8), s.mem_word)));
        b.assert_eq_cond(format!("load-i32-{k}"), s.out, b.band(shr_by_pos8, m32),
                         b.band(g_load, is_tag(b, tag, T_I32_LOAD)));
        b.assert_eq_cond(format!("load-i64-{k}"), s.out, s.mem_word,
                         b.band(g_load, is_tag(b, tag, T_I64_LOAD)));
        b.assert_eq_cond(format!("load-u8-{k}"), s.out, b.band(shr_by_pos8, b.add_constant_64(0xFF)),
                         b.band(g_load, is_tag(b, tag, T_I32_LOAD8U)));
        b.assert_eq_cond(format!("load-u32-{k}"), s.out, b.band(shr_by_pos8, m32),
                         b.band(g_load, is_tag(b, tag, T_I64_LOAD32U)));
        // stores: mem_word = bank word with bytes [pos, pos+w) from b
        let g_st64 = b.band(g_store, is_tag(b, tag, T_I64_STORE));
        b.assert_eq_cond(format!("store-word-{k}"), s.mem_word, s.b, g_st64);
        // width 4 at pos in {0,4}
        let g_st4 = b.bor(b.band(g_store, is_tag(b, tag, T_I32_STORE)),
                          b.band(g_store, is_tag(b, tag, T_I64_STORE32)));
        let b32 = b.band(s.b, m32);
        let cur_lo = b.band(cur_word, m32);
        let cur_hi = b.band(cur_word, b.add_constant_64(0xFFFF_FFFF_0000_0000));
        let w4 = b.select(p2, b.bor(b.shl(b32, 32), cur_lo), b.bor(cur_hi, b32));
        b.assert_eq_cond(format!("store-w4-{k}"), s.mem_word, w4, g_st4);
        // width 1 at pos in 0..7
        let g_st8 = b.band(g_store, is_tag(b, tag, T_I32_STORE8));
        let byte = b.band(s.b, b.add_constant_64(0xFF));
        let mut shifted = byte;
        shifted = b.select(p0, b.shl(shifted, 1), shifted);
        shifted = b.select(p1, b.shl(shifted, 2), shifted);
        shifted = b.select(p2, b.shl(shifted, 3), shifted);
        let mut affected = b.add_constant_64(0xFF);
        affected = b.select(p0, b.shl(affected, 1), affected);
        affected = b.select(p1, b.shl(affected, 2), affected);
        affected = b.select(p2, b.shl(affected, 3), affected);
        let w8 = b.bor(b.band(cur_word, b.bnot(affected)), b.band(shifted, affected));
        b.assert_eq_cond(format!("store-w8-{k}"), s.mem_word, w8, g_st8);
        // bank update
        for j in 0..MEM_WORDS {
            let hit = b.band(g_store, b.icmp_eq(word_idx, b.add_constant_64(j as u64)));
            mem_bank[j] = b.select(hit, s.mem_word, mem_bank[j]);
        }

        // ---- stack snapshot rule ----
        // branch value: the interpreter pops the condition FIRST, then moves
        // the remaining top to br_h — so the value sits at prev_h - 2.
        let hm2v = b.isub_bin_bout(prev_h, two, zero).0;
        let branch_val = single_wire_multiplex(b, &prev_stack, hm2v);
        for j in 0..N_STACK {
            let jc = b.add_constant_64(j as u64);
            let j_lt_h = b.icmp_ult(jc, s.height);
            let is_top = b.band(write, b.icmp_eq(jc, b.isub_bin_bout(s.height, one, zero).0));
            let normal = b.select(j_lt_h, b.select(is_top, s.out, prev_stack[j]), zero);
            let keep = b.icmp_ult(jc, s.br_h);
            let at_h = b.band(bnot_k(b, keep), b.band(b.icmp_eq(jc, s.br_h), b.icmp_eq(s.br_ar, one)));
            let branch = b.select(keep, prev_stack[j], b.select(at_h, branch_val, zero));
            b.assert_eq_cond(format!("stack-{k}-{j}"), s.stack[j], b.select(br_bool, branch, normal), active);
        }

        // ---- unused-field zero-guards (fabrication surface closure) ----
        // Every witness field not consumed by the step's op class is
        // asserted zero (on active rows) — mutants in unused fields then
        // hit a NAMED constraint instead of passing silently.
        let g_zero = b.band(active, b.bnot(br_bool));
        // c: only select uses it
        b.assert_eq_cond(format!("c-zero-{k}"), s.c, zero, b.band(g_zero, b.bnot(sel_op)));
        // mem_addr/mem_word: only load/store
        b.assert_eq_cond(format!("memaddr-zero-{k}"), s.mem_addr, zero, b.band(g_zero, b.bnot(is_mem)));
        b.assert_eq_cond(format!("memword-zero-{k}"), s.mem_word, zero, b.band(g_zero, b.bnot(is_mem)));
        // br_h/br_ar: only taken branches
        b.assert_eq_cond(format!("brh-zero-{k}"), s.br_h, zero, b.band(g_zero, bnot_k(b, br_bool)));
        b.assert_eq_cond(format!("brar-zero-{k}"), s.br_ar, zero, b.band(g_zero, bnot_k(b, br_bool)));

        // ---- pc chaining (label walk is the stated follow-up) ----
        if k + 1 < t.steps.len() {
            let next_active = b.icmp_ult(b.add_constant_64((k + 1) as u64), t.n_steps);
            let chain_ok = b.band(b.band(active, b.bnot(br_bool)), next_active);
            b.assert_eq_cond(format!("pc-chain-{k}"), t.steps[k + 1].pc, b.iadd(s.pc, one).0, chain_ok);
        }

        // ---- gas + final-state threading ----
        gas = b.iadd(gas, b.select(active, one, zero)).0;
        for j in 0..N_STACK { fin_stack_reg[j] = b.select(is_last, s.stack[j], fin_stack_reg[j]); }
        for j in 0..N_LOCALS { fin_locals_reg[j] = b.select(is_last, s.locals[j], fin_locals_reg[j]); }
        for j in 0..N_GLOBALS { fin_globals_reg[j] = b.select(is_last, glob_bank[j], fin_globals_reg[j]); }
        last_h = b.select(is_last, s.height, last_h);
    }

    // ---- final bindings ----
    for j in 0..N_STACK { b.assert_eq(format!("fin-stack-{j}"), t.fin_stack[j], fin_stack_reg[j]); }
    for j in 0..N_LOCALS { b.assert_eq(format!("fin-locals-{j}"), t.fin_locals[j], fin_locals_reg[j]); }
    for j in 0..N_GLOBALS { b.assert_eq(format!("fin-globals-{j}"), t.fin_globals[j], fin_globals_reg[j]); }
    b.assert_eq("gas-total", gas, t.gas_total);
    let res_idx = b.isub_bin_bout(last_h, one, zero).0;
    let res = single_wire_multiplex(b, &t.fin_stack, res_idx);
    b.assert_eq("result-top", t.result, res);
}

/// bnot wrapper (keeps call sites readable in expressions).
#[inline]
fn bnot_k(b: &CircuitBuilder, x: Wire) -> Wire {
    b.bnot(x)
}
