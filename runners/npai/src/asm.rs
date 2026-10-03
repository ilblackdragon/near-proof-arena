//! `npai-asm`: a tiny text assembler/disassembler for NPAI v1 images.
//!
//! NOT part of the TCB: the arena only ever runs the image bytes (whose
//! SHA-256 is pinned by the certificate); how they were produced is
//! irrelevant. Syntax (one statement per line, `;` or `#` starts a comment):
//!
//! ```text
//! .mem 4096              ; memSize (default: data length)
//! .equ N 10              ; named constant
//! .dlabel buf            ; name := current data length (an address in memory)
//! .data 00ff10           ; append hex bytes to the data segment
//! .ascii "hello"         ; append ASCII bytes (no escapes except \" and \\)
//! .zero 32               ; append 32 zero bytes
//! loop:                  ; code label := index of the next instruction
//!     const r1, N
//!     addi r1, r1, 0xffffffff
//!     jnz r1, loop
//!     tlen r2, claim     ; tapes: pub | claim | proof (or 0/1/2)
//!     out 0, r3, r4      ; out k, addr, len
//!     halt r1
//! ```
//!
//! Mnemonics: halt a | const a,imm | mov a,b | add/sub/mul/and/or/xor/shl/
//! shr/eq/ltu a,b,c | addi a,b,imm | jmp t | jz a,t | jnz a,t | tlen a,tape |
//! tload a,b,tape | tcopy a,b,c,tape | ld8 a,b | st8 a,b | sha256 a,b,c |
//! rohash a,b,c | memeq a,b,c,d | out k,a,b. Immediates are u32: decimal,
//! `0x` hex, a label or an `.equ` name. Registers are `r0`..`r15`.

use crate::interp::{encode, BinOp, Instr, Program, Tape, MAX_CODE_LEN, MAX_MEM_SIZE};
use std::collections::BTreeMap;

#[derive(Debug)]
pub struct AsmError {
    pub line: usize,
    pub msg: String,
}

impl std::fmt::Display for AsmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}: {}", self.line, self.msg)
    }
}

fn err<T>(line: usize, msg: impl Into<String>) -> Result<T, AsmError> {
    Err(AsmError {
        line,
        msg: msg.into(),
    })
}

fn strip_comment(l: &str) -> &str {
    // Comments may not start inside an .ascii string.
    let mut in_str = false;
    let mut esc = false;
    for (i, ch) in l.char_indices() {
        if in_str {
            if esc {
                esc = false;
            } else if ch == '\\' {
                esc = true;
            } else if ch == '"' {
                in_str = false;
            }
        } else if ch == '"' {
            in_str = true;
        } else if ch == ';' || ch == '#' {
            return &l[..i];
        }
    }
    l
}

fn parse_hex(s: &str) -> Option<Vec<u8>> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    if !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

fn parse_num(s: &str) -> Option<u64> {
    if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u64::from_str_radix(&h.replace('_', ""), 16).ok()
    } else {
        s.replace('_', "").parse().ok()
    }
}

struct Ctx<'a> {
    syms: &'a BTreeMap<String, u64>,
    line: usize,
}

impl Ctx<'_> {
    fn reg(&self, s: &str) -> Result<usize, AsmError> {
        match s
            .strip_prefix('r')
            .or_else(|| s.strip_prefix('R'))
            .and_then(|n| n.parse::<usize>().ok())
        {
            Some(n) if n < 16 => Ok(n),
            _ => err(self.line, format!("bad register {s:?} (expected r0..r15)")),
        }
    }
    fn imm(&self, s: &str) -> Result<u32, AsmError> {
        let v = match parse_num(s) {
            Some(v) => v,
            None => match self.syms.get(s) {
                Some(v) => *v,
                None => return err(self.line, format!("unknown symbol or bad number {s:?}")),
            },
        };
        u32::try_from(v).or_else(|_| err(self.line, format!("immediate {s} does not fit in u32")))
    }
    fn tape(&self, s: &str) -> Result<Tape, AsmError> {
        match s {
            "pub" | "public" => Ok(Tape::Pub),
            "claim" => Ok(Tape::Claim),
            "proof" => Ok(Tape::Proof),
            _ => match parse_num(s)
                .and_then(|v| u32::try_from(v).ok())
                .and_then(Tape::from_imm)
            {
                Some(t) => Ok(t),
                None => err(self.line, format!("bad tape {s:?} (pub|claim|proof)")),
            },
        }
    }
}

fn instr(cx: &Ctx<'_>, mn: &str, ops: &[&str]) -> Result<Instr, AsmError> {
    let want = |n: usize| -> Result<(), AsmError> {
        if ops.len() == n {
            Ok(())
        } else {
            err(
                cx.line,
                format!("{mn} takes {n} operand(s), got {}", ops.len()),
            )
        }
    };
    let bin = |op: BinOp| -> Result<Instr, AsmError> {
        want(3)?;
        Ok(Instr::Bin(
            op,
            cx.reg(ops[0])?,
            cx.reg(ops[1])?,
            cx.reg(ops[2])?,
        ))
    };
    Ok(match mn {
        "halt" => {
            want(1)?;
            Instr::Halt(cx.reg(ops[0])?)
        }
        "const" => {
            want(2)?;
            Instr::Const(cx.reg(ops[0])?, cx.imm(ops[1])?)
        }
        "mov" => {
            want(2)?;
            Instr::Mov(cx.reg(ops[0])?, cx.reg(ops[1])?)
        }
        "add" => bin(BinOp::Add)?,
        "sub" => bin(BinOp::Sub)?,
        "mul" => bin(BinOp::Mul)?,
        "and" => bin(BinOp::And)?,
        "or" => bin(BinOp::Or)?,
        "xor" => bin(BinOp::Xor)?,
        "shl" => bin(BinOp::Shl)?,
        "shr" => bin(BinOp::Shr)?,
        "eq" => bin(BinOp::Eq)?,
        "ltu" => bin(BinOp::Ltu)?,
        "addi" => {
            want(3)?;
            Instr::Addi(cx.reg(ops[0])?, cx.reg(ops[1])?, cx.imm(ops[2])?)
        }
        "jmp" => {
            want(1)?;
            Instr::Jmp(cx.imm(ops[0])?)
        }
        "jz" => {
            want(2)?;
            Instr::Jz(cx.reg(ops[0])?, cx.imm(ops[1])?)
        }
        "jnz" => {
            want(2)?;
            Instr::Jnz(cx.reg(ops[0])?, cx.imm(ops[1])?)
        }
        "tlen" => {
            want(2)?;
            Instr::Tlen(cx.reg(ops[0])?, cx.tape(ops[1])?)
        }
        "tload" => {
            want(3)?;
            Instr::Tload(cx.reg(ops[0])?, cx.reg(ops[1])?, cx.tape(ops[2])?)
        }
        "tcopy" => {
            want(4)?;
            Instr::Tcopy(
                cx.reg(ops[0])?,
                cx.reg(ops[1])?,
                cx.reg(ops[2])?,
                cx.tape(ops[3])?,
            )
        }
        "ld8" => {
            want(2)?;
            Instr::Ld8(cx.reg(ops[0])?, cx.reg(ops[1])?)
        }
        "st8" => {
            want(2)?;
            Instr::St8(cx.reg(ops[0])?, cx.reg(ops[1])?)
        }
        "sha256" => {
            want(3)?;
            Instr::Sha256(cx.reg(ops[0])?, cx.reg(ops[1])?, cx.reg(ops[2])?)
        }
        "rohash" => {
            want(3)?;
            Instr::RoHash(cx.reg(ops[0])?, cx.reg(ops[1])?, cx.reg(ops[2])?)
        }
        "memeq" => {
            want(4)?;
            Instr::MemEq(
                cx.reg(ops[0])?,
                cx.reg(ops[1])?,
                cx.reg(ops[2])?,
                cx.reg(ops[3])?,
            )
        }
        "out" => {
            want(3)?;
            let k = cx.imm(ops[0])?;
            if k > 1 {
                return err(cx.line, "out buffer must be 0 or 1");
            }
            Instr::Out(k as u8, cx.reg(ops[1])?, cx.reg(ops[2])?)
        }
        _ => return err(cx.line, format!("unknown mnemonic {mn:?}")),
    })
}

fn parse_ascii(line: usize, s: &str) -> Result<Vec<u8>, AsmError> {
    let s = s.trim();
    let inner = match s.strip_prefix('"').and_then(|t| t.strip_suffix('"')) {
        Some(i) => i,
        None => return err(line, ".ascii expects a double-quoted string"),
    };
    let mut out = vec![];
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        let c = if c == '\\' {
            match chars.next() {
                Some(e @ ('"' | '\\')) => e,
                _ => return err(line, "only \\\" and \\\\ escapes are supported"),
            }
        } else {
            c
        };
        if !c.is_ascii() {
            return err(line, ".ascii accepts ASCII only");
        }
        out.push(c as u8);
    }
    Ok(out)
}

/// Assemble source text into a `Program` (two passes: symbols, then code).
pub fn assemble(src: &str) -> Result<Program, AsmError> {
    // Pass 1: labels, .equ, data segment.
    let mut syms: BTreeMap<String, u64> = BTreeMap::new();
    let mut data: Vec<u8> = vec![];
    let mut mem: Option<u64> = None;
    let mut ninstr: u64 = 0;
    let mut stmts: Vec<(usize, String, Vec<String>)> = vec![];
    let define = |syms: &mut BTreeMap<String, u64>,
                  line: usize,
                  name: &str,
                  v: u64|
     -> Result<(), AsmError> {
        if name.is_empty()
            || !name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
            || name.starts_with(|c: char| c.is_ascii_digit())
        {
            return err(line, format!("bad symbol name {name:?}"));
        }
        if syms.insert(name.to_string(), v).is_some() {
            return err(line, format!("duplicate symbol {name:?}"));
        }
        Ok(())
    };
    for (i, raw) in src.lines().enumerate() {
        let line = i + 1;
        let mut l = strip_comment(raw).trim();
        while let Some(pos) = l.find(':') {
            let (lab, rest) = l.split_at(pos);
            if lab.contains(char::is_whitespace) || lab.contains('"') {
                break;
            }
            define(&mut syms, line, lab, ninstr)?;
            l = rest[1..].trim();
        }
        if l.is_empty() {
            continue;
        }
        let (head, rest) = match l.find(char::is_whitespace) {
            Some(p) => (&l[..p], l[p..].trim()),
            None => (l, ""),
        };
        let head = head.to_ascii_lowercase();
        match head.as_str() {
            ".mem" => match parse_num(rest) {
                Some(v) => mem = Some(v),
                None => return err(line, ".mem expects a number"),
            },
            ".equ" => {
                let mut it = rest.split_whitespace();
                let (Some(n), Some(v), None) = (it.next(), it.next(), it.next()) else {
                    return err(line, ".equ NAME VALUE");
                };
                let Some(v) = parse_num(v) else {
                    return err(line, "bad .equ value");
                };
                define(&mut syms, line, n, v)?;
            }
            ".dlabel" => define(&mut syms, line, rest, data.len() as u64)?,
            ".data" => match parse_hex(rest) {
                Some(b) => data.extend(b),
                None => return err(line, ".data expects hex bytes"),
            },
            ".ascii" => data.extend(parse_ascii(line, rest)?),
            ".zero" => match parse_num(rest) {
                Some(n) if n <= MAX_MEM_SIZE => data.extend(std::iter::repeat_n(0u8, n as usize)),
                _ => return err(line, ".zero expects a size <= 2^24"),
            },
            h if h.starts_with('.') => return err(line, format!("unknown directive {h}")),
            _ => {
                let ops: Vec<String> = if rest.is_empty() {
                    vec![]
                } else {
                    rest.split(',').map(|s| s.trim().to_string()).collect()
                };
                stmts.push((line, head, ops));
                ninstr += 1;
            }
        }
    }
    // Pass 2: instructions.
    let mut code = Vec::with_capacity(stmts.len());
    for (line, mn, ops) in &stmts {
        let cx = Ctx {
            syms: &syms,
            line: *line,
        };
        let ops: Vec<&str> = ops.iter().map(|s| s.as_str()).collect();
        code.push(instr(&cx, mn, &ops)?);
    }
    let mem_size = mem.unwrap_or(data.len() as u64);
    if mem_size > MAX_MEM_SIZE {
        return err(0, format!("memSize {mem_size} exceeds 2^24"));
    }
    if (data.len() as u64) > mem_size {
        return err(
            0,
            format!("data ({} bytes) larger than .mem {mem_size}", data.len()),
        );
    }
    if code.len() as u64 > MAX_CODE_LEN {
        return err(0, format!("{} instructions exceed 2^16", code.len()));
    }
    Ok(Program {
        mem_size: mem_size as u32,
        data,
        code,
    })
}

/// Assemble straight to image bytes.
pub fn assemble_image(src: &str) -> Result<Vec<u8>, AsmError> {
    assemble(src).map(|p| encode(&p))
}

/// Render one instruction in assembler syntax.
pub fn disasm_instr(i: &Instr) -> String {
    let t = |t: &Tape| match t {
        Tape::Pub => "pub",
        Tape::Claim => "claim",
        Tape::Proof => "proof",
    };
    match i {
        Instr::Halt(a) => format!("halt r{a}"),
        Instr::Const(a, imm) => format!("const r{a}, {imm}"),
        Instr::Mov(a, b) => format!("mov r{a}, r{b}"),
        Instr::Bin(op, a, b, c) => {
            let m = match op {
                BinOp::Add => "add",
                BinOp::Sub => "sub",
                BinOp::Mul => "mul",
                BinOp::And => "and",
                BinOp::Or => "or",
                BinOp::Xor => "xor",
                BinOp::Shl => "shl",
                BinOp::Shr => "shr",
                BinOp::Eq => "eq",
                BinOp::Ltu => "ltu",
            };
            format!("{m} r{a}, r{b}, r{c}")
        }
        Instr::Addi(a, b, imm) => format!("addi r{a}, r{b}, {imm:#x}"),
        Instr::Jmp(x) => format!("jmp {x}"),
        Instr::Jz(a, x) => format!("jz r{a}, {x}"),
        Instr::Jnz(a, x) => format!("jnz r{a}, {x}"),
        Instr::Tlen(a, tp) => format!("tlen r{a}, {}", t(tp)),
        Instr::Tload(a, b, tp) => format!("tload r{a}, r{b}, {}", t(tp)),
        Instr::Tcopy(a, b, c, tp) => format!("tcopy r{a}, r{b}, r{c}, {}", t(tp)),
        Instr::Ld8(a, b) => format!("ld8 r{a}, r{b}"),
        Instr::St8(a, b) => format!("st8 r{a}, r{b}"),
        Instr::Sha256(a, b, c) => format!("sha256 r{a}, r{b}, r{c}"),
        Instr::RoHash(a, b, c) => format!("rohash r{a}, r{b}, r{c}"),
        Instr::MemEq(a, b, c, d) => format!("memeq r{a}, r{b}, r{c}, r{d}"),
        Instr::Out(k, a, b) => format!("out {k}, r{a}, r{b}"),
    }
}

/// Disassemble a program into source that `assemble` maps back to the same
/// image (jump targets are emitted as numbers).
pub fn disassemble(p: &Program) -> String {
    let mut s = format!(".mem {}\n", p.mem_size);
    for chunk in p.data.chunks(32) {
        s.push_str(".data ");
        for b in chunk {
            s.push_str(&format!("{b:02x}"));
        }
        s.push('\n');
    }
    for (pc, i) in p.code.iter().enumerate() {
        s.push_str(&format!("    {:<28} ; {pc}\n", disasm_instr(i)));
    }
    s
}
