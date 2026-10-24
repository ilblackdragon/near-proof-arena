//! Trace generation for `wasm-base-v1`: executes the code records (the verifier-side output of
//! `wasmbase-tool prep`) and fills every chip row by column name.  It is an independent
//! implementation of family F1 over the records; its results are compared with the Lean spec run
//! (`prep.json`) and with the Python reference interpreter.
use crate::air::{AirSpec, TableSpec};
use crate::sha;
use crate::sha::NCOLS;
use p3_baby_bear::BabyBear as F;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use serde_json::Value;
use std::collections::HashMap;

pub const OP_NEXT: u64 = 0x101;
pub const OP_JUMP: u64 = 0x102;
pub const OP_JIF: u64 = 0x103;
pub const OP_HALT: u64 = 0x104;
pub const OP_HIF: u64 = 0x105;
/// `Chips.IfC.opIf`: the `if` row (falls through on non-zero, jumps on zero).
pub const OP_IF: u64 = 0x106;

/// The HOST argument window (`Chips.Host.nArgs`): every D3α host function has `np ≤ 9`.
pub const HOST_NARGS: u64 = 9;
/// The HOSTQ message length (`Chips.Host.qMsg.length = 4 + 2·nArgs`, mirrored in `Chips.HostO.qLen`).
pub const HOST_QLEN: usize = 4 + 2 * HOST_NARGS as usize;

#[derive(Clone, Debug)]
pub struct Prep {
    pub records: Vec<[u64; 8]>,
    pub local_tags: Vec<u64>,
    pub arity: u64,
    pub res_tag: u64,
    pub g0: u128,
    pub g_final: u128,
    pub regular: u128,
    pub steps: u64,
    pub status: String,
    pub stack: Vec<(u64, [u64; 4])>,
    pub max_fee: u64,
    /// memory size in bytes (constant), end of the data image, and the image bytes
    pub mem: u64,
    pub data_end: u64,
    pub data: Vec<u64>,
    /// initial globals `(tag, limbs)` (numeric only: tag 0 = i32, 1 = i64); globals are channel space 2
    pub globals: Vec<(u64, [u64; 4])>,
    /// the spec's stack budget `stackRem` after `enter` (channel space 5; `< 2^30`)
    pub stack_rem: u64,
    /// the module's function table (bus FUNC): `[entry, np + 128 nl, charge, prologue, m0..m3]`
    pub funcs: Vec<[u64; 8]>,
    /// the fixed host call table `[id, np, ar, 0, 0, 0, 0, 0]` (cached HOSTT rows)
    pub host_tab: Vec<[u64; 8]>,
    /// the observed host responses, in call order
    pub hosts: Vec<HostEv>,
}

/// One host call observed by the spec: signature, request arguments, outcome and `g_after`.
#[derive(Clone, Debug)]
pub struct HostEv {
    pub hid: u64,
    pub np: u64,
    pub ar: u64,
    pub args: Vec<u64>,
    pub st: u64,
    pub word: u64,
    pub g_after: u64,
    /// the register file the call left behind `(id, bytes)`, i.e. what it filled
    pub regs: Vec<(u64, Vec<u64>)>,
}

impl Prep {
    pub fn parse(text: &str) -> Prep {
        let v: Value = serde_json::from_str(text).expect("prep json");
        assert!(v["eligible"].as_bool().unwrap(), "program not eligible: {text}");
        let nums = |x: &Value| -> Vec<u64> { x.as_array().unwrap().iter().map(|n| n.as_u64().unwrap()).collect() };
        Prep {
            records: v["records"]
                .as_array()
                .unwrap()
                .iter()
                .map(|r| nums(r).try_into().unwrap())
                .collect(),
            local_tags: nums(&v["localTags"]),
            arity: v["arity"].as_u64().unwrap(),
            res_tag: v["resTag"].as_u64().unwrap(),
            g0: v["g0"].as_u64().unwrap() as u128,
            g_final: v["gFinal"].as_u64().unwrap() as u128,
            regular: v["regularOpCost"].as_u64().unwrap() as u128,
            steps: v["steps"].as_u64().unwrap(),
            status: v["status"].as_str().unwrap().to_string(),
            stack: v["stack"]
                .as_array()
                .unwrap()
                .iter()
                .map(|e| {
                    let tag = e["tag"].as_u64().unwrap();
                    // The Lean exporter tags floats and references 2. The D1 checker rejects every
                    // float instruction and every reference type, so an eligible program never
                    // produces one; if this fires the exporter's domain check and the checker have
                    // diverged. Same rule as the globals above (GlobOK).
                    assert!(tag <= 1, "non-integer stack entry is outside the domain (D1)");
                    (tag, nums(&e["limbs"]).try_into().unwrap())
                })
                .collect(),
            max_fee: v["maxFee"].as_u64().unwrap(),
            mem: v["mem"].as_u64().unwrap_or(0),
            data_end: v["dataEnd"].as_u64().unwrap_or(0),
            data: v.get("data").map(|d| nums(d)).unwrap_or_default(),
            globals: v
                .get("globals")
                .and_then(|g| g.as_array())
                .map(|g| {
                    g.iter()
                        .map(|e| {
                            let tag = e["tag"].as_u64().unwrap();
                            assert!(tag <= 1, "reference-typed globals are outside the domain (GlobOK)");
                            (tag, nums(&e["limbs"]).try_into().unwrap())
                        })
                        .collect()
                })
                .unwrap_or_default(),
            stack_rem: v.get("stackRem").and_then(|x| x.as_u64()).unwrap_or(0),
            funcs: v
                .get("funcs")
                .and_then(|g| g.as_array())
                .map(|g| g.iter().map(|r| nums(r).try_into().unwrap()).collect())
                .unwrap_or_default(),
            host_tab: v
                .get("hostTab")
                .and_then(|g| g.as_array())
                .map(|g| g.iter().map(|r| nums(r).try_into().unwrap()).collect())
                .unwrap_or_default(),
            hosts: v
                .get("hosts")
                .and_then(|g| g.as_array())
                .map(|g| {
                    g.iter()
                        .map(|e| HostEv {
                            hid: e["hid"].as_u64().unwrap(),
                            np: e["np"].as_u64().unwrap(),
                            ar: e["ar"].as_u64().unwrap(),
                            args: nums(&e["args"]),
                            st: e["st"].as_u64().unwrap(),
                            word: e["word"].as_u64().unwrap(),
                            g_after: e["gAfter"].as_u64().unwrap(),
                            regs: e
                                .get("regs")
                                .and_then(|r| r.as_array())
                                .map(|r| {
                                    r.iter()
                                        .map(|p| (p[0].as_u64().unwrap(), nums(&p[1])))
                                        .collect()
                                })
                                .unwrap_or_default(),
                        })
                        .collect()
                })
                .unwrap_or_default(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Ent {
    tag: u64,
    val: u64,
    tp: u64,
}

/// An activation: its stack base `sb`, id `cid` (= the CALL row's time; 0 for the entry frame), its
/// locals (channel space `16 + cid`), and its call record's return pc and charge.
struct Frame {
    sb: u64,
    cid: u64,
    retpc: u64,
    charge: u64,
    locals: Vec<Ent>,
}

pub fn limbs(x: u64) -> [u64; 4] {
    [x & 0xffff, (x >> 16) & 0xffff, (x >> 32) & 0xffff, x >> 48]
}
pub fn bytes(x: u64) -> [u64; 8] {
    std::array::from_fn(|i| (x >> (8 * i)) & 0xff)
}
fn from_limbs(l: &[u64; 4]) -> u64 {
    l[0] | (l[1] << 16) | (l[2] << 32) | (l[3] << 48)
}
fn fe(x: u64) -> F {
    F::from_u64(x)
}
fn fi(x: i64) -> F {
    if x >= 0 { F::from_u64(x as u64) } else { -F::from_u64((-x) as u64) }
}
fn sg(v: u64, w: u32) -> i128 {
    let v = v as i128;
    if (v >> (w - 1)) & 1 == 1 { v - (1i128 << w) } else { v }
}

struct Tab<'a> {
    spec: &'a TableSpec,
    idx: HashMap<String, usize>,
    rows: Vec<Vec<F>>,
}
impl<'a> Tab<'a> {
    fn new(spec: &'a TableSpec) -> Self {
        let idx = spec.cols.iter().enumerate().map(|(i, c)| (c.clone(), i)).collect();
        Tab { spec, idx, rows: vec![] }
    }
    fn row(&mut self) -> Row<'_, 'a> {
        self.rows.push(vec![F::ZERO; self.spec.cols.len()]);
        Row { t: self }
    }
}
struct Row<'b, 'a> {
    t: &'b mut Tab<'a>,
}
impl Row<'_, '_> {
    fn s(&mut self, name: &str, v: F) -> &mut Self {
        let i = *self.t.idx.get(name).unwrap_or_else(|| panic!("{}: no col {name}", self.t.spec.name));
        *self.t.rows.last_mut().unwrap().get_mut(i).unwrap() = v;
        self
    }
    fn u(&mut self, name: &str, v: u64) -> &mut Self {
        self.s(name, fe(v))
    }
    fn limbs(&mut self, p: &str, l: [u64; 4]) -> &mut Self {
        for (i, x) in l.iter().enumerate() {
            self.u(&format!("{p}{i}"), *x);
        }
        self
    }
    fn bytes(&mut self, p: &str, b: [u64; 8]) -> &mut Self {
        for (i, x) in b.iter().enumerate() {
            self.u(&format!("{p}{i}"), *x);
        }
        self
    }
}

pub struct Gen {
    pub mats: Vec<RowMajorMatrix<F>>,
    pub pubs: Vec<F>,
    pub rows_per_table: Vec<(String, usize)>,
    pub result: Option<(u64, u64)>,
    pub steps: u64,
    pub s_units: u64,
}

struct St {
    r16: Vec<u32>,
    byte: Vec<Vec<u32>>,
}
impl St {
    fn r16(&mut self, v: u64) {
        assert!(v < 65536, "range check out of range: {v}");
        self.r16[v as usize] += 1;
    }
    fn byte(&mut self, kind: usize, x: u64, y: u64) -> u64 {
        assert!(x < 256 && y < 256);
        self.byte[kind][(x + 256 * y) as usize] += 1;
        match kind {
            0 => 0,
            1 => x & y,
            2 => x | y,
            _ => x ^ y,
        }
    }
    /// `tp < ts`: returns `hi` and records the two lookups.
    fn tchk(&mut self, ts: u64, tp: u64) -> u64 {
        assert!(tp < ts, "channel time order violated: tp {tp} ts {ts}");
        let d = ts - tp - 1;
        let hi = d >> 16;
        assert!(hi < (1 << 14));
        self.r16(d & 0xffff);
        self.r16(4 * hi);
        hi
    }
}

/// LOAD ops in flag order: `(opcode, width, signed, is64)` (= `Chips.Load.ops`).
pub const LOAD_OPS: [(u64, u64, bool, bool); 12] = [
    (0x28, 4, false, false), (0x29, 8, false, true), (0x2C, 1, true, false), (0x2D, 1, false, false),
    (0x2E, 2, true, false), (0x2F, 2, false, false), (0x30, 1, true, true), (0x31, 1, false, true),
    (0x32, 2, true, true), (0x33, 2, false, true), (0x34, 4, true, true), (0x35, 4, false, true)];
/// STORE ops in flag order: `(opcode, width, is64)` (= `Chips.Store.ops`).
pub const STORE_OPS: [(u64, u64, bool); 7] =
    [(0x36, 4, false), (0x37, 8, true), (0x3A, 1, false), (0x3B, 2, false), (0x3C, 1, true), (0x3D, 2, true),
     (0x3E, 4, true)];

/// Memory: the current `(byte, producer time)` of every touched address, and its initial byte.
struct Mem<'p> {
    prep: &'p Prep,
    cur: std::collections::BTreeMap<u64, (u64, u64)>,
    init: std::collections::BTreeMap<u64, u64>,
}
impl Mem<'_> {
    fn get(&mut self, a: u64) -> (u64, u64) {
        assert!(a < self.prep.mem, "memory access out of bounds at {a}: the trap is not provable");
        if let Some(&e) = self.cur.get(&a) {
            return e;
        }
        let b = if a < self.prep.data_end { self.prep.data[a as usize] } else { 0 };
        self.init.insert(a, b);
        self.cur.insert(a, (b, 0));
        (b, 0)
    }
}

/// The bytes a `sha256(len, ptr, reg)` call hashes: `memOrRegH ptr len` reads register `ptr` when
/// `len = u64::MAX` (the register branch of `Host.lean:111`) and `[ptr, ptr+len)` from memory
/// otherwise.  Registers come from the spec's own post-call file (`ev.regs`), so the trace is
/// exactly what the spec did.
fn hash_input(mem: &mut Mem, len: u64, ptr: u64, ev: &HostEv) -> Vec<u8> {
    if len == u64::MAX {
        let bs = ev
            .regs
            .iter()
            .find(|(id, _)| *id == ptr)
            .map(|(_, bs)| bs.clone())
            .unwrap_or_default();
        bs.into_iter().map(|b| (b & 0xff) as u8).collect()
    } else {
        (0..len).map(|i| mem.get(ptr + i).0 as u8).collect()
    }
}

fn binop(op: u64, a: u64, b: u64) -> u64 {
    let w: u32 = if (0x7C..=0x8A).contains(&op) { 64 } else { 32 };
    let m: u64 = if w == 64 { u64::MAX } else { 0xffff_ffff };
    let base = if w == 64 { 0x7C } else { 0x6A };
    let k = (b % w as u64) as u32;
    match op - base {
        0 => a.wrapping_add(b) & m,
        1 => a.wrapping_sub(b) & m,
        2 => a.wrapping_mul(b) & m,
        7 => a & b,
        8 => a | b,
        9 => a ^ b,
        10 => (a << k) & m,
        11 => ((sg(a, w) >> k) as u64) & m,
        12 => a >> k,
        13 => if k == 0 { a } else { ((a << k) | (a >> (w - k))) & m },
        14 => if k == 0 { a } else { ((a >> k) | (a << (w - k))) & m },
        _ => panic!("binop {op:#x}"),
    }
}

/// div/rem with the spec's traps (b = 0; div_s MIN / -1).
fn divop(op: u64, a: u64, b: u64) -> Option<u64> {
    let w: u32 = if op >= 0x7F { 64 } else { 32 };
    let m: u128 = (1u128 << w) - 1;
    let kind = op - if w == 64 { 0x7F } else { 0x6D };
    if b == 0 {
        return None;
    }
    let (sa, sb) = (sg(a, w) as i128, sg(b, w) as i128);
    match kind {
        0 => {
            if sa == -(1i128 << (w - 1)) && sb == -1 {
                return None;
            }
            Some(((sa / sb) as u128 & m) as u64)
        }
        1 => Some(a / b),
        2 => Some(((sa % sb) as u128 & m) as u64),
        _ => Some(a % b),
    }
}

fn relop(op: u64, a: u64, b: u64) -> u64 {
    let w: u32 = if op >= 0x50 { 64 } else { 32 };
    let k = op - if w == 64 { 0x51 } else { 0x46 };
    (match k {
        0 => a == b,
        1 => a != b,
        2 => sg(a, w) < sg(b, w),
        3 => a < b,
        4 => sg(a, w) > sg(b, w),
        5 => a > b,
        6 => sg(a, w) <= sg(b, w),
        7 => a <= b,
        8 => sg(a, w) >= sg(b, w),
        _ => a >= b,
    }) as u64
}

const CMP_FLAGS: [&str; 11] = [
    "f_eqz", "f_eq", "f_ne", "f_lts", "f_ltu", "f_gts", "f_gtu", "f_les", "f_leu", "f_ges", "f_geu",
];

pub fn generate(air: &AirSpec, prep: &Prep) -> Gen {
    let t = |n: &str| &air.tables[air.index(n)];
    let mut add = Tab::new(t("ADD"));
    let mut bit = Tab::new(t("BIT"));
    let mut mul = Tab::new(t("MUL"));
    let mut shift = Tab::new(t("SHIFT"));
    let mut cmp = Tab::new(t("CMP"));
    let mut cnst = Tab::new(t("CONST"));
    let mut stk = Tab::new(t("STACK"));
    let mut ctrl = Tab::new(t("CTRL"));
    // `IF` is only in the `if` AIRs (`wasmBaseIfAir` / `wasmBaseIfHostAir`), so the base and host
    // paths are byte-identical to before.
    let has_if = air.tables.iter().any(|x| x.name == "IF");
    let mut ift = if has_if { Some(Tab::new(&air.tables[air.index("IF")])) } else { None };
    let mut loc = Tab::new(t("LOCAL"));
    let mut div = Tab::new(t("DIV"));
    let mut ld = Tab::new(t("LOAD"));
    let mut sto = Tab::new(t("STORE"));
    let mut call = Tab::new(t("CALL"));
    let mut ret = Tab::new(t("RET"));
    let has_host = air.tables.iter().any(|x| x.name == "HOST");
    let mut host = if has_host { Some(Tab::new(&air.tables[air.index("HOST")])) } else { None };
    let mut hosto = if has_host { Some(Tab::new(&air.tables[air.index("HOSTO")])) } else { None };
    // `wasmBaseHashAir` extends the oracle with the `sha` flag and the hash-call summary
    let has_sha = air.tables.iter().any(|x| x.name == "SHA256");
    // SHA-256 rows, one `ShaRows` per hash call (in call order)
    let mut sha_calls: Vec<sha::ShaRows> = vec![];
    let mut hostt = if has_host { Some(Tab::new(&air.tables[air.index("HOSTT")])) } else { None };
    let mut hostb = if has_host { Some(Tab::new(&air.tables[air.index("HOSTB")])) } else { None };
    // The register wire (channel space 6): present only in `wasmBaseRegAir` (table index 26).
    let has_reg = air.tables.iter().any(|x| x.name == "REG");
    let mut reg = if has_reg { Some(Tab::new(&air.tables[air.index("REG")])) } else { None };
    let shat = if has_sha { Some(Tab::new(&air.tables[air.index("SHA256")])) } else { None };
    // indexed by **host id**: the table's ids are not contiguous (`abort`/`write_register`
    // reserve 11/14), so the vector must reach the largest id, not the row count
    let mut host_calls: Vec<u64> =
        vec![0; prep.host_tab.iter().map(|r| r[0] as usize + 1).max().unwrap_or(0)];
    let mut host_ix = 0usize;
    // HOSTB rows `(ts, dir, pos, byte, len, hid, gap, act, f, reg, ptrLo, ptrHi, mtp, hp)`,
    // grouped by `(ts, dir)`: the request (`dir = 0`) and the response (`dir = 1`) of a host call.
    // A request byte is a **memory read**: it consumes the live space-3 message of `ptr + pos` at
    // its producer time `mtp` and re-produces it at `ts` (`Chips.HostB.memCnt`, `timeChk ts mtp hp`),
    // so the row carries the real memory byte and the trace's `mem.cur` is re-timed to `ts`.
    let mut hostb_rows: Vec<[u64; 14]> = vec![];
    let mut hostb_done = false;
    // The register file as the trace sees it (`space 6`): content, fill time, and whether the
    // register's message is still live (filled and not yet read).  `filled_seen` makes the fill
    // rows fire exactly once per register (the KAT keeps one fill per register).
    let mut regs: HashMap<u64, Vec<u64>> = HashMap::new();
    // the most recent producer time of the register's space-6 **byte** and **length** messages
    // (every access re-produces its own kind; a `register_len` does not touch the bytes)
    let mut reg_bts: HashMap<u64, u64> = HashMap::new();
    let mut reg_lts: HashMap<u64, u64> = HashMap::new();
    let mut reg_rows: Vec<[u64; 16]> = vec![];
    let mut func_calls: Vec<u64> = vec![0; prep.funcs.len()];
    // dead callee locals `(space, slot, entry)`, left over in the channel after their frame returned
    let mut dead: Vec<(u64, u64, Ent)> = vec![];
    let mut mem = Mem { prep, cur: Default::default(), init: Default::default() };
    let mut trapped = false;
    let mut st = St { r16: vec![0; 65536], byte: vec![vec![0; 65536]; 4] };
    let mut fetch = vec![0u64; prep.records.len()];

    let mut stack: Vec<Ent> = vec![];
    let mut frames = vec![Frame {
        sb: 0,
        cid: 0,
        retpc: 0,
        charge: 0,
        locals: prep.local_tags.iter().map(|&tag| Ent { tag, val: 0, tp: 0 }).collect(),
    }];
    // the stack-budget register (space 5), produced by BOUNDARY at time 0
    assert!(prep.stack_rem < 1 << 30, "stackRem >= 2^30 is outside the domain (BudOK)");
    let mut budget = Ent { tag: 0, val: prep.stack_rem, tp: 0 };
    let mut globals: Vec<Ent> = prep
        .globals
        .iter()
        .map(|&(tag, l)| Ent { tag, val: l[0] | (l[1] << 16) | (l[2] << 32) | (l[3] << 48), tp: 0 })
        .collect();
    let (mut pc, mut ts, mut s) = (0u64, 1u64, 0u64);
    let halt_pc;
    loop {
        let rec = prep.records[pc as usize];
        assert_eq!(rec[0], pc);
        let (op, h, fee) = (rec[1], rec[2], rec[3]);
        let (sb, cid) = (frames.last().unwrap().sb, frames.last().unwrap().cid);
        assert_eq!(h + sb, stack.len() as u64, "static height mismatch at pc {pc}");
        fetch[pc as usize] += 1;
        let hdr = |r: &mut Row| {
            r.u("pc", pc).u("ts", ts).u("S", s).u("h", h).u("fee", fee).u("fr_sb", sb).u("fr_cid", cid);
        };
        let mut next = pc + 1;
        let mut halted = false;
        let mut extra = 0u64;
        match op {
            0x1FF if has_host => {
                // HOST: `call` of a declared import; the response comes from the spec-observed table
                let (hid, np, ar) = (rec[4], rec[5], rec[6]);
                let ev = prep.hosts.get(host_ix).expect("host event").clone();
                assert_eq!((ev.hid, ev.np, ev.ar), (hid, np, ar));
                host_ix += 1;
                if (hid as usize) < host_calls.len() {
                    host_calls[hid as usize] += 1;
                }
                assert!(np <= HOST_NARGS, "host arity {np} exceeds the HOST window {HOST_NARGS}");
                let sb2 = sb + h - np;
                let mut args = vec![0u64; HOST_NARGS as usize];
                // the producer time of each argument, from the stack entry itself (a host call may
                // consume several arguments pushed at different times)
                let mut argTp = vec![0u64; HOST_NARGS as usize];
                // `args[0]` is the *lowest* stack slot (the spec's `popArgs` reverses the pops), so
                // pop `np` entries top-first and then reverse.
                let mut popped = Vec::new();
                for _ in 0..np {                    let a = stack.pop().unwrap();
                    assert_eq!(a.tag, 1, "host arguments are i64");
                    popped.push(a);
                }
                popped.reverse();
                for (j, a) in popped.iter().enumerate() {
                    args[j] = a.val;
                    argTp[j] = a.tp;                }
                assert_eq!(stack.len() as u64, sb2, "host call stack height");
                let ga = ev.g_after;
                let gl = limbs(ga);
                let rl = limbs(ev.word);
                let mut r = host.as_mut().unwrap().row();
                hdr(&mut r);
                r.u("act", 1).u("hid", hid).u("np", np).u("ar", ar).u("st", ev.st).u("nres", ev.ar * (1 - ev.st));
                r.limbs("ga", gl);
                r.limbs("r", rl);
                for j in 0..HOST_NARGS {
                    let pl = limbs(args[j as usize]);
                    let present = (j < np) as u64;
                    let tag = present; // i64
                    r.u(&format!("pf{j}"), present).u(&format!("tagP{j}"), tag);
                    r.limbs(&format!("P{j}_"), pl);
                    r.u(&format!("tP{j}"), 0).u(&format!("hP{j}"), 0);
                    if present == 1 {
                        // producer time: the clock of the row that pushed this stack entry
                        let tp = argTp[j as usize];                        let hp = st.tchk(ts, tp);
                        r.u(&format!("tP{j}"), tp).u(&format!("hP{j}"), hp);
                    }
                }
                for i in 0..4 {
                    st.r16(gl[i]);
                    st.r16(rl[i]);
                }
                for j in 0..HOST_NARGS {
                    for i in 0..4 {
                        st.r16(limbs(args[j as usize])[i]);
                    }
                }
                // HOSTO row: request `[ts, hid, S, np, (aLo j, aHi j) …]` + response
                let mut o = hosto.as_mut().unwrap().row();
                let req: Vec<u64> = vec![ts, hid, s, np]
                    .into_iter()
                    .chain(args.iter().flat_map(|&a| {
                        let l = limbs(a);
                        [l[0] | (l[1] << 16), l[2] | (l[3] << 16)]
                    }))
                    .collect();
                assert_eq!(req.len(), HOST_QLEN);
                for (i, v) in req.iter().enumerate() {
                    o.u(&format!("q{i}"), *v);                }
                o.u("st", ev.st).limbs("r", rl).limbs("g", gl).u("ar", ar).u("mult", 1);
                if has_sha {
                    // `sha` is 1 exactly on the four hash ids: the oracle states what the call did
                    let is_hash = [53u64, 54, 55, 56].contains(&hid);
                    o.u("sha", is_hash as u64);
                    if hid == 53 && ev.st == 0 {
                        // `sha256(len, ptr, reg)`: hash the spec's input bytes
                        let (len, ptr, reg) = (args[0], args[1], args[2]);
                        let input = hash_input(&mut mem, len, ptr, &ev);
                        sha_calls.push(sha::rows(
                            &[sha::Msg { id: reg, bytes: input, dmult: true }],
                            ts, 0, hid, ptr, len,
                        ));
                    }
                }
                // The register wire.  `input` (host id 48) fills register 0 with the spec's
                // `ctx.input`; `read_register` (49) reads one; `register_len` (6) reads only a
                // length.  The bytes come from the spec's own post-call register file (`ev.regs`),
                // so the trace is exactly what the spec did.
                // The ids are `Chips.Host.hostLogFns`/`hostFnsBase`, NOT the pre-canonical 12/13:
                // those arms never fired, so every REG row in every KAT was padding.
                if has_reg && ev.st == 0 {
                    match hid {
                        48 => {
                            // the register the call filled (the only one present in `ev.regs`)
                            if let Some((rid, bs)) = ev.regs.first() {
                                let rid = *rid;
                                let blen = bs.len() as u64;
                                regs.insert(rid, bs.clone());
                                // fill rows: one per byte, plus one length row
                                for (pos, &b) in bs.iter().enumerate() {
                                    // [act, kind, rd, rid, pos, len, byte, hid, ts, dir, gap,
                                    //  fresh, tp, hp, ptr, f]; f marks the group's first row
                                    reg_rows.push([1, 0, 0, rid, pos as u64, blen, b, hid, ts, 1,
                                        blen - pos as u64 - 1, 0, 0, 0, 0, (pos == 0) as u64]);
                                    // the HOSTB byte of a fill is the state-side half, `reg = 1`:
                                    // `memCnt = act*(1-dir)*(1-reg) = 0`, so this row has no space-3
                                    // message and its byteQ/r16 queries all have count 0; only the
                                    // bus-210 send `act*reg` remains (REG receives it).  The memory
                                    // columns are therefore inert and stay zero.
                                    hostb_rows.push([ts, 1, pos as u64, b, blen, hid,
                                        blen - pos as u64 - 1, 1, (pos == 0) as u64, 1, 0, 0, 0, 0]);
                                    st.byte(0, b, 0);
                                    // HOSTB's `gap` query (`reg = 1` makes its count 0, so this
                                    // answer is consumed by REG, which queries gap too)
                                    st.r16(blen - pos as u64 - 1);
                                    st.r16(blen);
                                    st.r16(rid);
                                    st.r16(pos as u64);
                                }
                                reg_rows.push([1, 1, 0, rid, 0, blen, 0, hid, ts, 0, 0, 0, 0, 0, 0, 0]);
                                st.r16(blen);
                                st.r16(rid);
                                st.r16(0);
                                // the fill re-produces both messages at `ts`
                                reg_bts.insert(rid, ts);
                                reg_lts.insert(rid, ts);
                            }
                        }
                        49 => {
                            // `read_register(id, ptr)`: consumes byte `i` of register `id`
                            if let Some(bs) = regs.get(&args[0]).cloned() {
                                let rid = args[0];
                                let blen = bs.len() as u64;
                                let ft = *reg_bts.get(&rid).unwrap();
                                let ptr = args[1];
                                for (pos, &b) in bs.iter().enumerate() {
                                    let h = st.tchk(ts, ft);
                                    // the memory write at `ptr + pos` is the deferred MEMIO link;
                                    // this slice only records the address
                                    reg_rows.push([1, 0, 1, rid, pos as u64, blen, b, hid, ts, 0,
                                        blen - pos as u64 - 1, 1, ft, h, ptr, (pos == 0) as u64]);
                                    st.byte(0, b, 0);
                                    // HOSTB's `gap` query (`reg = 1` makes its count 0, so this
                                    // answer is consumed by REG, which queries gap too)
                                    st.r16(blen - pos as u64 - 1);
                                    st.r16(blen);
                                    st.r16(rid);
                                    st.r16(pos as u64);
                                }
                                let lt = *reg_lts.get(&rid).unwrap();
                                let hl = st.tchk(ts, lt);
                                reg_rows.push([1, 1, 1, rid, 0, blen, 0, hid, ts, 0, 0, 1, lt, hl, ptr, 0]);
                                st.r16(blen);
                                st.r16(rid);
                                st.r16(0);
                                // the read re-produces both messages at `ts`
                                reg_bts.insert(rid, ts);
                                reg_lts.insert(rid, ts);
                                let _ = ft;
                            }
                        }
                        6 => {
                            // `register_len(id)`: consumes only the length message
                            if let Some(bs) = regs.get(&args[0]).cloned() {
                                let rid = args[0];
                                let blen = bs.len() as u64;
                                let lt = *reg_lts.get(&rid).unwrap();
                                let h = st.tchk(ts, lt);
                                // a length-only access is a complete group: the row starts it
                                reg_rows.push([1, 1, 1, rid, 0, blen, 0, hid, ts, 0, 0, 1, lt, h, 0, 1]);
                                st.r16(blen);
                                st.r16(rid);
                                st.r16(0);
                                reg_lts.insert(rid, ts);
                            }
                        }
                        _ => {}
                    }
                }
                // The register length is consumed (not produced) by the register's own fill row,
                // so a fill register's `len` message never leaks; nothing else to do here.
                // HOSTB rows: a fixed 4-byte request stream (dir 0) and a fixed 4-byte response
                // stream (dir 1) for the first host call.  The bytes are the low four bytes of the
                // first argument and of the result word; a `(ptr, len)` memory range is not
                // modelled in this slice.
                // The byte payload of the log/return functions: a `dir = 0` request group
                // (Wasm -> state) carrying the memory bytes at `(len, ptr)`, taken from the trace's
                // own memory at the time of the call.  `(ts, hid)` is the host call's, so the group
                // cannot be spliced onto another call.  `len` is capped at 40 bytes (the KAT's
                // payloads).
                //
                // The ids are `Chips.hostByteIds` (`HostChip.lean`): `log_utf8 = 45`,
                // `log_utf16 = 46`, `panic_utf8 = 47`, `value_return = 50`.  This arm used to test
                // `[8, 9, 10, 15]`, which are `promise_create`/`promise_then`/`promise_and`/
                // `promise_batch_action_deploy_contract`, so it never fired for a real log call.
                //
                // The spec's signature is `log_utf8(len, ptr)` (`Host.lean`: `utf8H a[0] a[1]` then
                // `readMemH ptr len`), so `args[0]` is the **length** and `args[1]` the pointer.
                //
                // Each request byte is the MEMIO link of `Chips.HostB`: it consumes the live space-3
                // byte of `ptr + pos` at its producer time `mtp`, checks `mtp < ts` (`timeChk`) and
                // re-produces the same byte at `ts`, so the trace's `mem.cur` is re-timed exactly as
                // a LOAD row would re-time it.  The row therefore needs, per byte: `byteQ`, `r16`
                // gap/pos/len, `r16` ptrLo and `r16 (32*ptrHi)` (the AIR's five), plus the two
                // `timeChk` limbs.
                if has_host && [45u64, 46, 47, 50].contains(&hid) {
                    let (blen, ptr) = (args[0], args[1]);
                    let blen = blen.min(40);
                    if blen > 0 {
                        assert!(ptr < (1u64 << 27), "buffer base {ptr} beyond 2^27");
                        let (ptr_lo, ptr_hi) = (ptr & 0xffff, ptr >> 16);
                        assert!(ptr_hi < 2048, "buffer base {ptr} beyond 2^27");
                        for pos in 0..blen {
                            let (b, mtp) = mem.get(ptr + pos);
                            let hp = st.tchk(ts, mtp);
                            mem.cur.insert(ptr + pos, (b, ts));
                            hostb_rows.push([ts, 0, pos, b, blen, hid, blen - pos - 1, 1,
                                (pos == 0) as u64, 0, ptr_lo, ptr_hi, mtp, hp]);
                            st.byte(0, b, 0);
                            st.r16(blen - pos - 1);
                            st.r16(pos);
                            st.r16(blen);
                            st.r16(ptr_lo);
                            st.r16(32 * ptr_hi);
                        }
                    }
                }
                // The placeholder byte stream belongs to the minimum slice.  With the REG table the
                // byte payload is driven by the register wire instead (`hid = 12/13/6`), so the
                // placeholder must not add unrelated bytes; and a log/return call has its own
                // payload group above.
                //
                // A request byte (`dir = 0`) is a real memory read at the buffer base 0, so it needs
                // the same MEMIO link as the payload arm: consume the live byte at `mtp`, `timeChk`,
                // re-produce at `ts`.  A program without memory (or with fewer than four bytes) has
                // no in-bounds buffer, so only the response half (`dir = 1`, state-side data that
                // never touches memory) is emitted there.
                if !hostb_done && !has_reg && ![45u64, 46, 47, 50].contains(&hid) {
                    hostb_done = true;
                    let sb_ = bytes(ev.word);
                    let blen = 4u64;
                    if prep.mem >= blen {
                        for pos in 0..blen {
                            let (b, mtp) = mem.get(pos);
                            let hp = st.tchk(ts, mtp);
                            mem.cur.insert(pos, (b, ts));
                            // [ts, dir, pos, byte, len, hid, gap, act, f, reg, ptrLo, ptrHi, mtp, hp]
                            hostb_rows.push([ts, 0, pos, b, blen, hid, blen - pos - 1, 1,
                                (pos == 0) as u64, 0, 0, 0, mtp, hp]);
                            st.byte(0, b, 0);
                            st.r16(blen - pos - 1);
                            st.r16(pos);
                            st.r16(blen);
                            st.r16(0);
                            st.r16(0);
                        }
                    }
                    for pos in 0..blen {
                        let b = sb_[pos as usize];
                        // A `dir = 1` byte that fills a register (`input`) has `reg = 1`: HOSTB
                        // then carries only the state-side half and REG the Wasm side.  Here the
                        // byte is a plain payload byte (`reg = 0`), so HOSTB carries both halves
                        // and queries byteQ, gap, pos, len, ptrLo and 32*ptrHi itself.  It never
                        // touches memory (`memCnt = act*(1-dir)*(1-reg) = 0`).
                        hostb_rows.push([ts, 1, pos, b, blen, hid, blen - pos - 1, 1,
                            (pos == 0) as u64, 0, 0, 0, 0, 0]);
                        st.byte(0, b, 0);
                        st.r16(blen - pos - 1);
                        st.r16(pos);
                        st.r16(blen);
                        st.r16(0);
                        st.r16(0);
                    }
                }
                if ev.st == 0 && ar == 1 {
                    stack.push(Ent { tag: 1, val: ev.word, tp: ts });
                } else {
                    assert!(ar == 0 || ev.st == 1);
                    if ev.st == 1 {
                        trapped = true;
                    }
                }
                extra = 0;
            }
            0x10 => {
                // call: params -> callee locals (space 16 + ts), declared locals zeroed, call record
                // (space 4, slot ts), budget decremented by the callee's charge
                let entry = rec[4];
                let k = prep.funcs.iter().position(|f| f[0] == entry).expect("callee in the function table");
                func_calls[k] += 1;
                let fr = prep.funcs[k];
                let (shape, charge, pro) = (fr[1], fr[2], fr[3]);
                let (np, nl) = (shape % 128, shape / 128);
                assert!(np <= 8 && np <= nl && nl <= 64);
                let mask = fr[4] | (fr[5] << 16) | (fr[6] << 32) | (fr[7] << 48);
                let sbn = sb + h - np;
                let params = stack.split_off(sbn as usize);
                assert!(budget.val >= charge, "stack budget exhausted: the trap is not provable");
                let n = budget.val - charge;
                let hb = st.tchk(ts, budget.tp);
                for x in [n & 0xffff, n >> 16, 4 * (n >> 16), sbn & 0xffff, sbn >> 16, 16 * (sbn >> 16), ts & 0xffff,
                    ts >> 16, 16 * (ts >> 16)] {
                    st.r16(x);
                }
                let mut r = call.row();
                hdr(&mut r);
                r.u("act", 1).u("entry", entry).u("shape", shape).u("charge", charge).u("pro", pro);
                for q in 0..4 {
                    r.u(&format!("m{q}"), fr[4 + q]);
                }
                for j in 0..8u64 {
                    r.u(&format!("pf{j}"), (j < np) as u64);
                }
                for j in 0..64u64 {
                    r.u(&format!("af{j}"), (j < nl) as u64).u(&format!("tg{j}"), (mask >> j) & 1);
                }
                let mut locs = vec![];
                for (j, p) in params.iter().enumerate() {
                    assert_eq!(p.tag, (mask >> j) & 1, "param type");
                    let hp = st.tchk(ts, p.tp);
                    r.u(&format!("tagP{j}"), p.tag).limbs(&format!("P{j}_"), limbs(p.val)).u(&format!("tP{j}"), p.tp)
                        .u(&format!("hP{j}"), hp);
                    locs.push(Ent { tag: p.tag, val: p.val, tp: ts });
                }
                for j in np..nl {
                    locs.push(Ent { tag: (mask >> j) & 1, val: 0, tp: ts });
                }
                r.u("r0", budget.val & 0xffff).u("r1", budget.val >> 16).u("tpb", budget.tp).u("hb", hb);
                r.u("n0", n & 0xffff).u("n1", n >> 16).u("sbn0", sbn & 0xffff).u("sbn1", sbn >> 16);
                r.u("ts0", ts & 0xffff).u("ts1", ts >> 16);
                frames.push(Frame { sb: sbn, cid: ts, retpc: pc + 1, charge, locals: locs });
                budget = Ent { tag: 0, val: n, tp: ts };
                next = entry;
                extra = pro;
            }
            OP_HALT | OP_HIF if cid != 0 => {
                // end / return / br(_if) to the function label in a callee: RET
                let mut r = ret.row();
                hdr(&mut r);
                r.u(if op == OP_HALT { "f_ret" } else { "f_rif" }, 1).s("invc", fe(cid).inverse());
                let mut taken = true;
                if op == OP_HIF {
                    let c = stack.pop().unwrap();
                    assert_eq!(c.tag, 0);
                    let hc = st.tchk(ts, c.tp);
                    let cl = limbs(c.val);
                    let cz = cl[0] + cl[1];
                    r.u("c0", cl[0]).u("c1", cl[1]).u("tc", c.tp).u("hc", hc);
                    r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
                    taken = c.val != 0;
                }
                if taken {
                    let f = frames.pop().unwrap();
                    let caller = frames.last().unwrap();
                    let hr = st.tchk(ts, f.cid);
                    let hb = st.tchk(ts, budget.tp);
                    let n = budget.val + f.charge;
                    st.r16(n & 0xffff);
                    st.r16(n >> 16);
                    st.r16(4 * (n >> 16));
                    r.u("retpc", f.retpc).u("sbc", caller.sb).u("cidc", caller.cid).u("charge", f.charge);
                    r.u("tpr", f.cid).u("hr", hr);
                    r.u("r0", budget.val & 0xffff).u("r1", budget.val >> 16).u("tpb", budget.tp).u("hb", hb);
                    r.u("n0", n & 0xffff).u("n1", n >> 16);
                    budget = Ent { tag: 0, val: n, tp: ts };
                    for (j, e) in f.locals.into_iter().enumerate() {
                        dead.push((16 + f.cid, j as u64, e));
                    }
                    next = f.retpc;
                }
            }
            0x41 | 0x42 => {
                let is64 = op - 0x41;
                let v = from_limbs(&[rec[4], rec[5], rec[6], rec[7]]);
                let mut r = cnst.row();
                hdr(&mut r);
                r.u("act", 1).u("is64", is64).limbs("imm", limbs(v));
                stack.push(Ent { tag: is64, val: v, tp: ts });
            }
            0x6A | 0x6B | 0x7C | 0x7D => {
                let is64 = (op >= 0x7C) as u64;
                let sub = (op & 1 == 1) as u64; // 0x6B, 0x7D
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let (x, z) = if sub == 1 { (rv, a.val) } else { (a.val, rv) };
                let (xl, bl, zl) = (limbs(x), limbs(b.val), limbs(z));
                let nl = if is64 == 1 { 4 } else { 2 };
                let mut c = [0u64; 4];
                let mut carry = 0;
                for i in 0..nl {
                    let tot = xl[i] + bl[i] + carry;
                    assert_eq!(tot & 0xffff, zl[i]);
                    carry = tot >> 16;
                    c[i] = carry;
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                for l in limbs(rv) {
                    st.r16(l);
                }
                let mut r = add.row();
                hdr(&mut r);
                r.u("f_add", 1 - sub).u("f_sub", sub).u("is64", is64);
                r.limbs("a", limbs(a.val)).u("ta", a.tp).u("ha", ha);
                r.limbs("b", limbs(b.val)).u("tb", b.tp).u("hb", hb);
                r.limbs("r", limbs(rv)).limbs("c", c);
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x71..=0x73 | 0x83..=0x85 => {
                let is64 = (op >= 0x83) as u64;
                let k = op - if is64 == 1 { 0x83 } else { 0x71 };
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let (ab, bb, rb) = (bytes(a.val), bytes(b.val), bytes(rv));
                for j in 0..8 {
                    assert_eq!(st.byte(k as usize + 1, ab[j], bb[j]), rb[j]);
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                let mut r = bit.row();
                hdr(&mut r);
                r.u("f_and", (k == 0) as u64).u("f_or", (k == 1) as u64).u("f_xor", (k == 2) as u64);
                r.u("is64", is64).bytes("ab", ab).u("ta", a.tp).u("ha", ha);
                r.bytes("bb", bb).u("tb", b.tp).u("hb", hb).bytes("rb", rb);
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x6C | 0x7E => {
                let is64 = (op == 0x7E) as u64;
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let (ab, bb, rb) = (bytes(a.val), bytes(b.val), bytes(rv));
                let nb = if is64 == 1 { 8 } else { 4 };
                let mut cy = [0u64; 8];
                let mut carry = 0u64;
                for k in 0..nb {
                    let mut tot = carry;
                    for i in 0..=k {
                        tot += ab[i] * bb[k - i];
                    }
                    assert_eq!(tot & 0xff, rb[k]);
                    carry = tot >> 8;
                    cy[k] = carry;
                }
                for i in 0..4 {
                    st.byte(0, ab[2 * i], ab[2 * i + 1]);
                    st.byte(0, bb[2 * i], bb[2 * i + 1]);
                    st.byte(0, rb[2 * i], rb[2 * i + 1]);
                }
                for c in cy {
                    st.r16(c);
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                let mut r = mul.row();
                hdr(&mut r);
                r.u("act", 1).u("is64", is64).bytes("ab", ab).u("ta", a.tp).u("ha", ha);
                r.bytes("bb", bb).u("tb", b.tp).u("hb", hb).bytes("rb", rb).bytes("cy", cy);
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x74..=0x78 | 0x86..=0x8A => {
                let is64 = (op >= 0x86) as u64;
                let kind = op - if is64 == 1 { 0x86 } else { 0x74 }; // shl, shr_s, shr_u, rotl, rotr
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let rv = binop(op, a.val, b.val);
                let w: u64 = if is64 == 1 { 64 } else { 32 };
                let b0 = b.val & 0xffff;
                let k = b0 % w;
                let q = b0 / w;
                let left = kind == 0 || kind == 3;
                let e = if left { k } else { w - k };
                let (ebv, t) = (e % 8, e / 8);
                let pow = 1u64 << ebv;
                let ab = bytes(a.val);
                let top = if is64 == 1 { ab[7] } else { ab[3] };
                let sgn = top >> 7;
                let rest = top & 0x7f;
                let fill = if kind == 1 { 255 * sgn } else { 0 };
                let aext: Vec<u64> = (0..16)
                    .map(|i| {
                        if i < 4 { ab[i] }
                        else if i < 8 { if is64 == 1 { ab[i] } else { fill } }
                        else if is64 == 1 { fill } else { 0 }
                    })
                    .collect();
                let nb = if is64 == 1 { 16 } else { 8 };
                let (mut pb, mut cy) = ([0u64; 16], [0u64; 16]);
                let mut carry = 0u64;
                for j in 0..nb {
                    let m = if j as u64 >= t { aext[j - t as usize] } else { 0 };
                    let tot = pow * m + carry;
                    pb[j] = tot & 0xff;
                    carry = tot >> 8;
                    cy[j] = carry;
                }
                let flo = matches!(kind, 0 | 3 | 4) as u64;
                let fhi = matches!(kind, 1 | 2 | 3 | 4) as u64;
                let rbytes: Vec<u64> = (0..8)
                    .map(|j| {
                        if j < 4 {
                            flo * pb[j] + fhi * if is64 == 1 { pb[j + 8] } else { pb[j + 4] }
                        } else if is64 == 1 {
                            flo * pb[j] + fhi * pb[j + 8]
                        } else {
                            0
                        }
                    })
                    .collect();
                let rcalc: u64 = rbytes.iter().enumerate().map(|(j, &x)| x << (8 * j)).sum();
                assert_eq!(rcalc, rv, "shift construction op {op:#x} a {:#x} b {:#x}", a.val, b.val);
                st.r16(q);
                st.byte(0, 2 * rest, 0);
                for i in 0..4 {
                    st.byte(0, ab[2 * i], ab[2 * i + 1]);
                }
                for i in 0..8 {
                    st.byte(0, pb[2 * i], pb[2 * i + 1]);
                    st.byte(0, cy[2 * i], cy[2 * i + 1]);
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                let mut r = shift.row();
                hdr(&mut r);
                for (i, f) in ["f_shl", "f_shrs", "f_shru", "f_rotl", "f_rotr"].iter().enumerate() {
                    r.u(f, (kind == i as u64) as u64);
                }
                r.u("is64", is64).bytes("ab", ab).u("ta", a.tp).u("ha", ha);
                r.limbs("b", limbs(b.val)).u("tb", b.tp).u("hb", hb);
                for j in 0..6 {
                    r.u(&format!("kb{j}"), (k >> j) & 1);
                }
                r.u("q", q);
                for j in 0..3 {
                    r.u(&format!("eb{j}"), (ebv >> j) & 1);
                }
                for j in 0..9 {
                    r.u(&format!("el{j}"), (t == j) as u64);
                }
                r.u("sgn", sgn).u("rest", rest);
                for j in 0..16 {
                    r.u(&format!("P{j}"), pb[j]).u(&format!("cy{j}"), cy[j]);
                }
                stack.push(Ent { tag: is64, val: rv, tp: ts });
            }
            0x45..=0x5A => {
                let is64 = (op >= 0x50) as u64;
                let idx = (op - if is64 == 1 { 0x50 } else { 0x45 }) as usize;
                let eqz = idx == 0;
                let b = if eqz { Ent { tag: is64, val: 0, tp: 0 } } else { stack.pop().unwrap() };
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let res = if eqz { (a.val == 0) as u64 } else { relop(op, a.val, b.val) };
                let swap = matches!(idx, 5 | 6 | 7 | 8);
                let signed = matches!(idx, 3 | 5 | 7 | 9);
                let w: u32 = if is64 == 1 { 64 } else { 32 };
                let (x, y) = if swap { (b.val, a.val) } else { (a.val, b.val) };
                let flip = |v: u64| if signed { v ^ (1u64 << (w - 1)) } else { v };
                let (xl, yl) = (limbs(flip(x)), limbs(flip(y)));
                let nl = if is64 == 1 { 4 } else { 2 };
                let (mut d, mut br) = ([0u64; 4], [0u64; 4]);
                let mut borrow = 0i64;
                for i in 0..nl {
                    let v = xl[i] as i64 - yl[i] as i64 - borrow;
                    let (dv, bo) = if v < 0 { (v + 65536, 1) } else { (v, 0) };
                    d[i] = dv as u64;
                    br[i] = bo as u64;
                    borrow = bo;
                }
                let lt = borrow as u64;
                let zsum: u64 = d.iter().sum();
                let eqf = (zsum == 0) as u64;
                let calc = match idx {
                    0 | 1 => eqf,
                    2 => 1 - eqf,
                    3 | 4 | 5 | 6 => lt,
                    _ => 1 - lt,
                };
                assert_eq!(calc, res, "cmp construction op {op:#x}");
                let (al, bl) = (limbs(a.val), limbs(b.val));
                let (ta_, tb_) = (if is64 == 1 { al[3] } else { al[1] }, if is64 == 1 { bl[3] } else { bl[1] });
                let (sa, ra, sb, rb) = (ta_ >> 15, ta_ & 0x7fff, tb_ >> 15, tb_ & 0x7fff);
                for v in d {
                    st.r16(v);
                }
                st.r16(2 * ra);
                st.r16(2 * rb);
                let ha = st.tchk(ts, a.tp);
                let hb = if eqz { 0 } else { st.tchk(ts, b.tp) };
                let mut r = cmp.row();
                hdr(&mut r);
                for (i, f) in CMP_FLAGS.iter().enumerate() {
                    r.u(f, (i == idx) as u64);
                }
                r.u("is64", is64).limbs("a", al).u("ta", a.tp).u("ha", ha);
                r.limbs("b", bl).u("tb", b.tp).u("hb", hb);
                r.u("sa", sa).u("ra", ra).u("sb", sb).u("rb", rb).limbs("d", d).limbs("br", br);
                let inv = if zsum == 0 { F::ZERO } else { fe(zsum).inverse() };
                r.s("inv", inv);
                stack.push(Ent { tag: 0, val: res, tp: ts });
            }
            0x1A => {
                let a = stack.pop().unwrap();
                let ha = st.tchk(ts, a.tp);
                let al = limbs(a.val);
                let cz = al[0] + al[1];
                let mut r = stk.row();
                hdr(&mut r);
                r.u("f_drop", 1).u("tagA", a.tag).limbs("A", al).u("tA", a.tp).u("hA", ha);
                r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
            }
            0x1B => {
                let c = stack.pop().unwrap();
                let v2 = stack.pop().unwrap();
                let v1 = stack.pop().unwrap();
                assert!(c.tag == 0 && v1.tag == v2.tag);
                let (hc, h2, h1) = (st.tchk(ts, c.tp), st.tchk(ts, v2.tp), st.tchk(ts, v1.tp));
                let cl = limbs(c.val);
                let cz = cl[0] + cl[1];
                let out = if c.val != 0 { v1 } else { v2 };
                let mut r = stk.row();
                hdr(&mut r);
                r.u("f_sel", 1).u("tagA", 0).limbs("A", cl).u("tA", c.tp).u("hA", hc);
                r.u("tagV", v1.tag);
                let l2 = limbs(v2.val);
                let l1 = limbs(v1.val);
                for i in 0..4 {
                    r.u(&format!("V2_{i}"), l2[i]).u(&format!("V1_{i}"), l1[i]);
                }
                r.u("t2", v2.tp).u("h2", h2).u("t1", v1.tp).u("h1", h1);
                r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
                stack.push(Ent { tag: out.tag, val: out.val, tp: ts });
            }
            0x20..=0x24 => {
                // local.get/set/tee (0x20..0x22) and global.get/set (0x23, 0x24): one LOCAL row
                let x = rec[4] as usize;
                let is_g = op >= 0x23;
                let vars = if is_g { &mut globals } else { &mut frames.last_mut().unwrap().locals };
                let old = vars[x];
                let hl = st.tchk(ts, old.tp);
                let mut r = loc.row();
                hdr(&mut r);
                r.u("f_get", (op == 0x20) as u64).u("f_set", (op == 0x21) as u64).u("f_tee", (op == 0x22) as u64);
                r.u("f_gget", (op == 0x23) as u64).u("f_gset", (op == 0x24) as u64);
                r.u("idx", x as u64).u("tagL", old.tag).limbs("L", limbs(old.val)).u("tL", old.tp).u("hL", hl);
                // channel space: `16 + cid` for locals, 2 for globals
                r.s("inv_sp", fe(if is_g { 2 } else { 16 + cid }).inverse());
                if op == 0x20 || op == 0x23 {
                    vars[x] = Ent { tag: old.tag, val: old.val, tp: ts };
                    stack.push(Ent { tag: old.tag, val: old.val, tp: ts });
                } else {
                    let v = stack.pop().unwrap();
                    let hv = st.tchk(ts, v.tp);
                    r.u("tagV", v.tag).limbs("V", limbs(v.val)).u("tV", v.tp).u("hV", hv);
                    vars[x] = Ent { tag: v.tag, val: v.val, tp: ts };
                    if op == 0x22 {
                        stack.push(Ent { tag: v.tag, val: v.val, tp: ts });
                    }
                }
            }
            OP_IF if has_if => {
                // `if`: pop the condition, push the `end` label (the checker's business), and select
                // the successor.  `tgt` is `elseOf + 1` — which equals `endOf + 1` when there is no
                // `else`, so one column covers both shapes.
                let tgt = rec[4];
                let c = stack.pop().unwrap();
                assert_eq!(c.tag, 0, "`if` condition is i32");
                let mut r = ift.as_mut().unwrap().row();
                hdr(&mut r);
                let cl = limbs(c.val);
                let cz = cl[0] + cl[1];
                let hc = st.tchk(ts, c.tp);
                r.u("f_if", 1).u("tgt", tgt);
                r.u("c0", cl[0]).u("c1", cl[1]).u("tc", c.tp).u("hc", hc);
                r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
                // the polarity: non-zero falls through, zero jumps
                next = if c.val != 0 { pc + 1 } else { tgt };
            }
            OP_NEXT | OP_JUMP | OP_JIF | OP_HALT | OP_HIF => {
                let tgt = rec[4];
                let mut r = ctrl.row();
                hdr(&mut r);
                let names = ["f_next", "f_jump", "f_jif", "f_halt", "f_hif"];
                r.u(names[(op - OP_NEXT) as usize], 1).u("tgt", tgt);
                let mut taken = false;
                if op == OP_JIF || op == OP_HIF {
                    let c = stack.pop().unwrap();
                    assert_eq!(c.tag, 0);
                    let hc = st.tchk(ts, c.tp);
                    let cl = limbs(c.val);
                    let cz = cl[0] + cl[1];
                    r.u("c0", cl[0]).u("c1", cl[1]).u("tc", c.tp).u("hc", hc);
                    r.s("inv", if cz == 0 { F::ZERO } else { fe(cz).inverse() });
                    taken = c.val != 0;
                }
                match op {
                    OP_JUMP => next = tgt,
                    OP_JIF if taken => next = tgt,
                    OP_HALT => halted = true,
                    OP_HIF if taken => halted = true,
                    _ => {}
                }
            }
            0x6D..=0x70 | 0x7F..=0x82 => {
                let is64 = (op >= 0x7F) as u64;
                let w: u32 = if is64 == 1 { 64 } else { 32 };
                let kind = op - if is64 == 1 { 0x7F } else { 0x6D }; // 0 divS 1 divU 2 remS 3 remU
                let signed = kind == 0 || kind == 2;
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert!(a.tag == is64 && b.tag == is64);
                let nl = if is64 == 1 { 4 } else { 2 };
                let (al, bl) = (limbs(a.val), limbs(b.val));
                let (hb_a, ra) = (al[nl - 1] >> 15, al[nl - 1] & 0x7fff);
                let (hb_b, rb) = (bl[nl - 1] >> 15, bl[nl - 1] & 0x7fff);
                let wm: u128 = 1u128 << w;
                let neg = |x: u64| -> u64 { ((wm - x as u128) % wm) as u64 };
                let sa = signed && hb_a == 1;
                let sb = signed && hb_b == 1;
                let am = if sa { neg(a.val) } else { a.val };
                let bm = if sb { neg(b.val) } else { b.val };
                // negation-chain carries: s ? X + x = 2^16 c (limb-wise) : 0
                let chain = |on: bool, x: u64, xx: u64| -> [u64; 4] {
                    let mut c = [0u64; 4];
                    if on {
                        let (xl, xxl) = (limbs(x), limbs(xx));
                        let mut cin = 0u64;
                        for i in 0..nl {
                            let sm = xl[i] + xxl[i] + cin;
                            assert_eq!(sm & 0xffff, 0);
                            c[i] = sm >> 16;
                            cin = c[i];
                        }
                    }
                    c
                };
                let ca = chain(sa, am, a.val);
                let cb = chain(sb, bm, b.val);
                let tz = bm == 0;
                let (qm, rm) = if tz { (0, 0) } else { (am / bm, am % bm) };
                let (ab_, bb_, qb, rb_) = (bytes(am), bytes(bm), bytes(qm), bytes(rm));
                let nb = if is64 == 1 { 8 } else { 4 };
                let mut cy = [0u64; 8];
                let mut dd = [0u64; 4];
                let mut bw = [0u64; 4];
                if !tz {
                    let mut cin = 0u64;
                    for k in 0..nb {
                        let mut conv = 0u64;
                        for i in 0..=k {
                            conv += qb[i] * bb_[k - i];
                        }
                        let tot = conv + rb_[k] + cin;
                        assert!(tot >= ab_[k] && (tot - ab_[k]) % 256 == 0);
                        cy[k] = (tot - ab_[k]) / 256;
                        cin = cy[k];
                    }
                    assert_eq!(cy[nb - 1], 0);
                    let (bml, rml) = (limbs(bm), limbs(rm));
                    let mut bin = 0i64;
                    for i in 0..4 {
                        let mut d = bml[i] as i64 - rml[i] as i64 - (i == 0) as i64 - bin;
                        if d < 0 {
                            d += 65536;
                            bw[i] = 1;
                        }
                        dd[i] = d as u64;
                        bin = bw[i] as i64;
                    }
                    assert_eq!(bw[3], 0);
                }
                let ql = limbs(qm);
                let (hb_q, rq) = (ql[nl - 1] >> 15, ql[nl - 1] & 0x7fff);
                let tov = !tz && kind == 0 && hb_a == 1 && hb_b == 1 && hb_q == 1;
                let trap = tz || tov;
                let xv = if kind == 0 || kind == 1 { qm } else { rm };
                let sres = (kind == 0 && (hb_a ^ hb_b) == 1) || (kind == 2 && hb_a == 1);
                let resv = if sres { neg(xv) } else { xv };
                let cr = chain(sres, resv, xv);
                if !trap {
                    let rv = match divop(op, a.val, b.val) {
                        Some(v) => v,
                        None => panic!("div trap mismatch"),
                    };
                    assert_eq!(rv, resv, "div result op {op:#x} a {:#x} b {:#x}", a.val, b.val);
                } else {
                    assert!(divop(op, a.val, b.val).is_none(), "div should trap");
                }
                let ha = st.tchk(ts, a.tp);
                let hb = st.tchk(ts, b.tp);
                st.r16(2 * ra);
                st.r16(2 * rb);
                st.r16(2 * rq);
                for i in 0..4 {
                    st.byte(0, ab_[2 * i], ab_[2 * i + 1]);
                    st.byte(0, bb_[2 * i], bb_[2 * i + 1]);
                    st.byte(0, qb[2 * i], qb[2 * i + 1]);
                    st.byte(0, rb_[2 * i], rb_[2 * i + 1]);
                }
                for d in dd {
                    st.r16(d);
                }
                for l in limbs(resv) {
                    st.r16(l);
                }
                for c in cy {
                    st.r16(c);
                }
                let bsum: u64 = bb_.iter().sum();
                let mut r = div.row();
                hdr(&mut r);
                r.u("f_divs", (kind == 0) as u64).u("f_divu", (kind == 1) as u64).u("f_rems", (kind == 2) as u64)
                    .u("f_remu", (kind == 3) as u64).u("is64", is64);
                r.limbs("a", al).u("ta", a.tp).u("ha", ha).limbs("b", bl).u("tb", b.tp).u("hb", hb);
                r.u("hbA", hb_a).u("ra", ra).u("hbB", hb_b).u("rb", rb);
                r.bytes("A", ab_).bytes("B", bb_).bytes("Q", qb).bytes("R", rb_);
                r.limbs("ca", ca).limbs("cb", cb);
                for k in 0..8 {
                    r.u(&format!("cy{k}"), cy[k]);
                }
                r.limbs("d", dd).limbs("bw", bw);
                r.u("tz", tz as u64).s("invB", if bsum == 0 { F::ZERO } else { fe(bsum).inverse() });
                r.u("hbQ", hb_q).u("rq", rq).u("tov", tov as u64).limbs("res", limbs(resv)).limbs("cr", cr);
                if trap {
                    trapped = true;
                } else {
                    stack.push(Ent { tag: is64, val: resv, tp: ts });
                }
            }
            op if LOAD_OPS.iter().any(|o| o.0 == op) => {
                let k = LOAD_OPS.iter().position(|o| o.0 == op).unwrap();
                let (_, w, sgn, is64) = LOAD_OPS[k];
                let a = stack.pop().unwrap();
                assert_eq!(a.tag, 0);
                let off = rec[4] + 65536 * rec[5];
                let ea = a.val + off;
                let al = limbs(a.val);
                let (e0, cye) = ((al[0] + rec[4]) & 0xffff, (al[0] + rec[4]) >> 16);
                let e1 = al[1] + rec[5] + cye;
                assert_eq!(e0 + 65536 * e1, ea);
                assert!(e1 < 2048, "effective address beyond 2^27");
                let ha = st.tchk(ts, a.tp);
                st.r16(e0);
                st.r16(32 * e1);
                let mut bv = [0u64; 8];
                let mut tbv = [0u64; 8];
                let mut hbv = [0u64; 8];
                for i in 0..w as usize {
                    let (b, tp) = mem.get(ea + i as u64);
                    bv[i] = b;
                    tbv[i] = tp;
                    hbv[i] = st.tchk(ts, tp);
                    mem.cur.insert(ea + i as u64, (b, ts));
                }
                let v: u64 = (0..w as usize).map(|i| bv[i] << (8 * i)).sum();
                let top = bv[w as usize - 1];
                let (sbit, low7) = (top >> 7, top & 0x7f);
                st.r16(512 * low7);
                let rv = if sgn && sbit == 1 {
                    let ext = v | (u64::MAX << (8 * w));
                    if is64 { ext } else { ext & 0xffff_ffff }
                } else {
                    v
                };
                let mut r = ld.row();
                hdr(&mut r);
                r.u(&format!("f{k}"), 1);
                r.u("a0", al[0]).u("a1", al[1]).u("ta", a.tp).u("ha", ha);
                r.u("off0", rec[4]).u("off1", rec[5]).u("e0", e0).u("e1", e1).u("cyE", cye);
                r.bytes("b", bv).bytes("tb", tbv).bytes("hb", hbv).u("sbit", sbit).u("low7", low7);
                r.limbs("r", limbs(rv));
                stack.push(Ent { tag: is64 as u64, val: rv, tp: ts });
            }
            op if STORE_OPS.iter().any(|o| o.0 == op) => {
                let k = STORE_OPS.iter().position(|o| o.0 == op).unwrap();
                let (_, w, is64) = STORE_OPS[k];
                let v = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                assert_eq!(v.tag, is64 as u64);
                assert_eq!(a.tag, 0);
                let off = rec[4] + 65536 * rec[5];
                let ea = a.val + off;
                let al = limbs(a.val);
                let (e0, cye) = ((al[0] + rec[4]) & 0xffff, (al[0] + rec[4]) >> 16);
                let e1 = al[1] + rec[5] + cye;
                assert_eq!(e0 + 65536 * e1, ea);
                assert!(e1 < 2048, "effective address beyond 2^27");
                let hv = st.tchk(ts, v.tp);
                let ha = st.tchk(ts, a.tp);
                st.r16(e0);
                st.r16(32 * e1);
                let vb = bytes(v.val);
                for j in 0..4 {
                    st.byte(0, vb[2 * j], vb[2 * j + 1]);
                }
                let mut ob = [0u64; 8];
                let mut tob = [0u64; 8];
                let mut hob = [0u64; 8];
                for i in 0..w as usize {
                    let (b, tp) = mem.get(ea + i as u64);
                    ob[i] = b;
                    tob[i] = tp;
                    hob[i] = st.tchk(ts, tp);
                    mem.cur.insert(ea + i as u64, (vb[i], ts));
                }
                let mut r = sto.row();
                hdr(&mut r);
                r.u(&format!("f{k}"), 1).limbs("v", limbs(v.val)).u("tv", v.tp).u("hv", hv).bytes("vb", vb);
                r.u("a0", al[0]).u("a1", al[1]).u("ta", a.tp).u("ha", ha);
                r.u("off0", rec[4]).u("off1", rec[5]).u("e0", e0).u("e1", e1).u("cyE", cye);
                r.bytes("ob", ob).bytes("tob", tob).bytes("hob", hob);
            }
            _ => panic!("unknown op {op:#x}"),
        }
        s += fee + extra;
        ts += 1;
        if halted || trapped {
            halt_pc = if trapped { pc + 1 } else { pc };
            break;
        }
        pc = next;
    }
    let steps = ts - 1;
    let status: u64 = if trapped { 2 } else { 1 };
    if !trapped {
        assert_eq!(stack.len() as u64, prep.arity, "final stack size");
    }
    let result = if trapped { None } else { stack.last().map(|e| (e.tag, e.val)) };
    // after a trap the leftover operand stack goes to DRAIN rows
    let mut drn = Tab::new(t("DRAIN"));
    let (sbf, cidf) = (frames.last().unwrap().sb, frames.last().unwrap().cid);
    if trapped {
        for (i, e) in stack.iter().enumerate() {
            drn.row().u("act", 1).u("space", 0).u("slot", i as u64).u("tag", e.tag).limbs("v", limbs(e.val)).u("tp", e.tp);
        }
        // the frames still live at the trap: their call records (space 4) and locals (space 16 + cid)
        for k in 1..frames.len() {
            let (f, c) = (&frames[k], &frames[k - 1]);
            drn.row().u("act", 1).u("space", 4).u("slot", f.cid).u("tag", 0)
                .limbs("v", [f.retpc, c.sb, c.cid, f.charge]).u("tp", f.cid).s("inv", fe(4).inverse());
            for (j, e) in f.locals.iter().enumerate() {
                dead.push((16 + f.cid, j as u64, *e));
            }
        }
    } else {
        assert_eq!(frames.len(), 1, "halted outside the entry frame");
    }
    // dead callee locals
    for &(sp, j, e) in dead.iter() {
        drn.row().u("act", 1).u("space", sp).u("slot", j).u("tag", e.tag).limbs("v", limbs(e.val)).u("tp", e.tp)
            .s("inv", fe(sp).inverse());
    }
    // the stack-budget register is left over at the end (space 5)
    drn.row().u("act", 1).u("space", 5).u("slot", 0).u("tag", 0)
        .limbs("v", [budget.val & 0xffff, budget.val >> 16, 0, 0]).u("tp", budget.tp).s("inv", fe(5).inverse());
    // every global is left over at the end (space 2)
    for (g, e) in globals.iter().enumerate() {
        drn.row().u("act", 1).u("space", 2).u("slot", g as u64).u("tag", e.tag).limbs("v", limbs(e.val)).u("tp", e.tp)
            .s("inv", fe(2).inverse());
    }
    // every touched memory byte is left over at the end (space 3)
    for (&a, &(b, tp)) in mem.cur.iter() {
        drn.row().u("act", 1).u("space", 3).u("slot", a).u("tag", 0).limbs("v", [b, 0, 0, 0]).u("tp", tp)
            .s("inv", fe(3).inverse());
    }
    // the final register file is left over at the end (space 6): one length message and one byte
    // message per register, at the register's latest producer time.  This is exactly
    // `Register.view` -- the leftover space-6 messages are the register file.
    let mut rid_sorted: Vec<u64> = regs.keys().copied().collect();
    rid_sorted.sort_unstable();
    for &rid in rid_sorted.iter() {
        let bs = regs.get(&rid).unwrap();
        let btp = *reg_bts.get(&rid).unwrap();
        let ltp = *reg_lts.get(&rid).unwrap();
        let blen = bs.len() as u64;
        for (pos, &b) in bs.iter().enumerate() {
            drn.row().u("act", 1).u("space", 6).u("slot", rid * (1u64 << 24) + pos as u64 + 1)
                .u("tag", 0).limbs("v", [b, 0, 0, 0]).u("tp", btp).s("inv", fe(6).inverse());
        }
        drn.row().u("act", 1).u("space", 6).u("slot", rid * (1u64 << 24)).u("tag", 2)
            .limbs("v", [blen, 0, 0, 0]).u("tp", ltp).s("inv", fe(6).inverse());
    }
    // MEMINIT: one row per touched byte, sorted, with its initial byte; DATA multiplicities
    let mut mi = Tab::new(t("MEMINIT"));
    let mut data_mult = vec![0u64; (prep.data_end as usize).max(1)];
    let mut prev: Option<u64> = None;
    for (&a, &b) in mem.init.iter() {
        let zd = a >= prep.data_end;
        let gap = prev.map(|p| a - p - 1).unwrap_or(0);
        let mut r = mi.row();
        r.u("act", 1).u("ad", a).u("bv", b).u("zd", zd as u64);
        r.u("glo", gap & 0xffff).u("ghi", gap >> 16).u("alo", a & 0xffff).u("ahi", a >> 16);
        let m = prep.mem - 1 - a;
        r.u("mlo", m & 0xffff).u("mhi", m >> 16);
        st.r16(gap & 0xffff);
        st.r16(32 * (gap >> 16));
        st.r16(a & 0xffff);
        st.r16(32 * (a >> 16));
        st.r16(m & 0xffff);
        st.r16(32 * (m >> 16));
        if zd {
            let d = a - prep.data_end;
            r.u("dlo", d & 0xffff).u("dhi", d >> 16);
            st.r16(d & 0xffff);
            st.r16(32 * (d >> 16));
        } else {
            data_mult[a as usize] += 1;
        }
        prev = Some(a);
    }

    // BOUNDARY
    let bspec = t("BOUNDARY");
    let mut bnd = Tab::new(bspec);
    {
        let mut r = bnd.row();
        r.u("pcf", halt_pc).u("tpr", if trapped { 0 } else { stack.last().map(|e| e.tp).unwrap_or(0) });
        r.u("sbf", sbf).u("cidf", cidf);
        for (j, e) in frames[0].locals.iter().enumerate() {
            r.u(&format!("ftag{j}"), e.tag).limbs(&format!("fv{j}_"), limbs(e.val)).u(&format!("ftp{j}"), e.tp);
        }
    }
    // public values
    let mut pubs = vec![fe(ts), fe(s), fe(prep.arity)];
    let (rtag, rval) = result.unwrap_or((0, 0));
    pubs.push(fe(rtag));
    pubs.extend(limbs(rval).map(fe));
    pubs.push(fe(status));
    pubs.push(fe(prep.mem));
    pubs.push(fe(prep.data_end));
    pubs.extend(prep.local_tags.iter().map(|&x| fe(x)));
    for &(tag, l) in prep.globals.iter() {
        pubs.push(fe(tag));
        pubs.extend(l.map(fe));
    }
    pubs.push(fe(prep.stack_rem & 0xffff));
    pubs.push(fe(prep.stack_rem >> 16));
    assert_eq!(pubs.len(), air.num_pub);

    // RANGE16 / BYTE
    let mut rng = Tab::new(t("RANGE16"));
    for v in 0..65536u64 {
        rng.row().u("v", v).u("m", st.r16[v as usize] as u64);
    }
    let mut byt = Tab::new(t("BYTE"));
    for key in 0..65536u64 {
        let (x, y) = (key & 0xff, key >> 8);
        let mut r = byt.row();
        for i in 0..8 {
            r.u(&format!("x{i}"), (x >> i) & 1).u(&format!("y{i}"), (y >> i) & 1);
        }
        for k in 0..4 {
            r.u(&format!("m{k}"), st.byte[k][key as usize] as u64);
        }
    }

    // CODE: the canonical record matrix (cached) + multiplicities
    let mut code = Tab::new(t("CODE"));
    let crows = code_rows(&prep.records);
    for (j, rec) in crows.iter().enumerate() {
        let mut r = code.row();
        for (k, name) in ["pc", "op", "h", "fee", "x0", "x1", "x2", "x3"].iter().enumerate() {
            r.u(name, rec[k]);
        }
        r.u("mult", if j < fetch.len() { fetch[j] } else { 0 });
    }

    // DATA: the canonical image matrix (cached) + multiplicities
    let mut dat = Tab::new(t("DATA"));
    for (j, rec) in data_rows(prep).iter().enumerate() {
        dat.row().u("addr", rec[0]).u("byte", rec[1]).u("mult", if j < data_mult.len() && (j as u64) < prep.data_end { data_mult[j] } else { 0 });
    }

    // FUNC: the canonical function-table matrix (cached) + multiplicities (calls per function)
    let mut fun = Tab::new(t("FUNC"));
    for (j, rec) in func_rows(prep).iter().enumerate() {
        let mut r = fun.row();
        for (k, name) in ["entry", "shape", "charge", "pro", "m0", "m1", "m2", "m3"].iter().enumerate() {
            r.u(name, rec[k]);
        }
        r.u("mult", if j < func_calls.len() { func_calls[j] } else { 0 });
    }

    let mut tabs: HashMap<String, Tab> = HashMap::new();
    for tb in [bnd, add, bit, mul, shift, cmp, cnst, stk, ctrl, loc, div, ld, sto, call, ret, rng, byt, code, drn, mi,
        dat, fun] {
        tabs.insert(tb.spec.name.clone(), tb);
    }
    // `IF` only when the AIR has it; padded by inactive rows so `first`/`last` never land mid-row
    // and the selector constraint `f_if · (f_if − 1) = 0` holds on the padding.
    if let Some(mut ift) = ift {
        let hgt = (ift.rows.len() + 1).max(4).next_power_of_two();
        while ift.rows.len() < hgt {
            ift.row().u("f_if", 0);
        }
        tabs.insert("IF".into(), ift);
    }
    if let (Some(h), Some(o), Some(ht), Some(hb)) = (host, hosto, hostt, hostb) {
        // HOSTT: the fixed host table as a cached trace, multiplicities = calls per host id
        let rows = {
            let mut rows: Vec<[u64; 8]> = if prep.host_tab.is_empty() { vec![[0; 8]] } else { prep.host_tab.clone() };
            let hgt = rows.len().max(4).next_power_of_two();
            let last = *rows.last().unwrap();
            rows.resize(hgt, last);
            rows
        };
        let mut ht = ht;
        for (j, rec) in rows.iter().enumerate() {
            let mut r = ht.row();
            for (k, name) in ["id", "np", "ar", "z0", "z1", "z2", "z3", "z4"].iter().enumerate() {
                r.u(name, rec[k]);
            }
            // the multiplicity is the number of calls of **this row's** host id (the table's ids
            // are not contiguous: `abort`/`write_register` reserve 11/14), not of row `j`
            let id = rec[0] as usize;
            // padding rows repeat the last record: they carry no call
            let real = j < prep.host_tab.len();
            r.u("mult", if real && id < host_calls.len() { host_calls[id] } else { 0 });
        }
        tabs.insert("HOSTT".into(), ht);
        tabs.insert("HOST".into(), h);
        tabs.insert("HOSTO".into(), o);
        // HOSTB: the byte stream, padded by group-start rows (`f = 1`, `act = 0`), which keeps
        // `first`/`last` at a group break and never fires a continuation constraint.
        let mut hb = hb;
        for rec in hostb_rows.iter() {
            let mut r = hb.row();
            for (k, name) in ["ts", "dir", "pos", "byte", "len", "hid", "gap", "act", "f", "reg",
                              "ptrLo", "ptrHi", "mtp", "hp"].iter().enumerate() {
                r.u(name, rec[k]);
            }
        }
        let hgt = (hb.rows.len() + 1).max(4).next_power_of_two();
        while hb.rows.len() < hgt {
            hb.row().u("act", 0).u("f", 1).u("gap", 0);
        }
        tabs.insert("HOSTB".into(), hb);
        if let Some(st_) = shat {
            let mut st_ = st_;
            let names: Vec<String> = st_.spec.cols.clone();
            for sr in sha_calls.iter() {
                for row in sr.rows.iter() {
                    let col: Vec<(String, u64)> =
                        names.iter().take(NCOLS).enumerate().map(|(i, n)| (n.clone(), row[i])).collect();
                    let mut r = st_.row();
                    for (n, v) in col {
                        r.u(&n, v);
                    }
                }
            }
            // an empty table still needs `≥ 4` padding rows
            while st_.rows.len() < 4 {
                st_.row();
            }
            tabs.insert("SHA256".into(), st_);
        }
        if let Some(rg) = reg {
            let mut rg = rg;
            for rec in reg_rows.iter() {
                let mut r = rg.row();
                for (k, name) in ["act", "kind", "rd", "rid", "pos", "len", "byte", "hid", "ts",
                    "dir", "gap", "fresh", "tp", "hp", "ptr", "f"].iter().enumerate() {
                    r.u(name, rec[k]);
                }
            }
            // Padding: a closed empty group (`f = 1`, `kind = 1`, `pos = 0`, `len = 0`), which is
            // what `cLast`/`cLenEnds`/`cStartPos` accept.  `act = 0` keeps every interaction count 0.
            let hgt = (rg.rows.len() + 1).max(4).next_power_of_two();
            while rg.rows.len() < hgt {
                rg.row().u("act", 0).u("f", 1).u("kind", 1).u("pos", 0).u("len", 0).u("gap", 0);
            }
            tabs.insert("REG".into(), rg);
        }
    }
    let mut mats = vec![];
    let mut rows_per_table = vec![];
    for spec in &air.tables {
        let tb = tabs.remove(&spec.name).unwrap();
        let w = spec.cols.len();
        let n = tb.rows.len();
        let h = n.max(4).next_power_of_two();
        let mut data: Vec<F> = tb.rows.into_iter().flatten().collect();
        data.resize(h * w, F::ZERO);
        rows_per_table.push((spec.name.clone(), n));
        mats.push(RowMajorMatrix::new(data, w));
    }
    Gen { mats, pubs, rows_per_table, result, steps, s_units: s }
}

/// The canonical CODE rows: the records in pc order, padded to a power of two (≥ 4) by repeating the
/// last record.  `code_root` (a statement component, recomputed by V_d from the contract code) is the
/// commitment to exactly this matrix.
pub fn code_rows(records: &[[u64; 8]]) -> Vec<[u64; 8]> {
    let h = records.len().max(4).next_power_of_two();
    let mut rows = records.to_vec();
    let last = *records.last().expect("non-empty code");
    rows.resize(h, last);
    rows
}

/// The canonical FUNC rows: the module's function table in checked-function order, padded to a power
/// of two (≥ 4) by repeating the last row.  `func_root` (a statement component, recomputed by V_d from
/// the contract code) is the commitment to exactly this matrix.
pub fn func_rows(prep: &Prep) -> Vec<[u64; 8]> {
    let mut rows = prep.funcs.clone();
    if rows.is_empty() {
        rows.push([0; 8]);
    }
    let h = rows.len().max(4).next_power_of_two();
    let last = *rows.last().unwrap();
    rows.resize(h, last);
    rows
}

pub fn func_matrix(prep: &Prep) -> RowMajorMatrix<F> {
    let rows = func_rows(prep);
    RowMajorMatrix::new(rows.iter().flat_map(|r| r.iter().map(|&x| fe(x))).collect(), 8)
}

/// The canonical DATA rows: `(a, image[a])` for `a < dataEnd` in address order (`(0, 0)` if the image
/// is empty), padded to a power of two (≥ 4) by repeating the last row.  `data_root` (a statement
/// component, recomputed by V_d from the contract code) is the commitment to exactly this matrix.
pub fn data_rows(prep: &Prep) -> Vec<[u64; 2]> {
    let mut rows: Vec<[u64; 2]> = (0..prep.data_end).map(|a| [a, prep.data[a as usize]]).collect();
    if rows.is_empty() {
        rows.push([0, 0]);
    }
    let h = rows.len().max(4).next_power_of_two();
    let last = *rows.last().unwrap();
    rows.resize(h, last);
    rows
}

pub fn data_matrix(prep: &Prep) -> RowMajorMatrix<F> {
    let rows = data_rows(prep);
    RowMajorMatrix::new(rows.iter().flat_map(|r| r.iter().map(|&x| fe(x))).collect(), 2)
}

pub fn code_matrix(records: &[[u64; 8]]) -> RowMajorMatrix<F> {
    let rows = code_rows(records);
    RowMajorMatrix::new(rows.iter().flat_map(|r| r.iter().map(|&x| fe(x))).collect(), 8)
}

/// Check every constraint of every table on every row with the interpreter (cheap pre-check).
pub fn check_constraints(air: &AirSpec, g: &Gen) -> Result<(), String> {
    for (ti, spec) in air.tables.iter().enumerate() {
        let m = &g.mats[ti];
        let w = spec.cols.len();
        let h = m.values.len() / w;
        let pubs: &[F] = if crate::air::JsonAir::reads_pub(spec) { &g.pubs } else { &[] };
        for r in 0..h {
            let cur = &m.values[r * w..(r + 1) * w];
            let nr = (r + 1) % h;
            let nxt = &m.values[nr * w..(nr + 1) * w];
            let sel = [fe((r == 0) as u64), fe((r == h - 1) as u64), fe((r != h - 1) as u64)];
            for (ci, c) in spec.constraints.iter().enumerate() {
                let v = c.eval_f(cur, nxt, pubs, sel);
                if v != F::ZERO {
                    return Err(format!("{} row {r} constraint {ci} = {}", spec.name, v.as_canonical_u32()));
                }
            }
        }
    }
    Ok(())
}

/// Bus balance (exact multisets over the trace, all buses) with the interpreter.
pub fn check_buses(air: &AirSpec, g: &Gen) -> Result<(), String> {
    let mut bal: HashMap<(u16, Vec<u32>), i128> = HashMap::new();
    for (ti, spec) in air.tables.iter().enumerate() {
        let m = &g.mats[ti];
        let w = spec.cols.len();
        let h = m.values.len() / w;
        let pubs: &[F] = if crate::air::JsonAir::reads_pub(spec) { &g.pubs } else { &[] };
        for r in 0..h {
            let cur = &m.values[r * w..(r + 1) * w];
            let nr = (r + 1) % h;
            let nxt = &m.values[nr * w..(nr + 1) * w];
            let sel = [fe((r == 0) as u64), fe((r == h - 1) as u64), fe((r != h - 1) as u64)];
            for it in &spec.inters {
                let c = it.count.eval_f(cur, nxt, pubs, sel).as_canonical_u32();
                if c == 0 {
                    continue;
                }
                let msg: Vec<u32> = it.msg.iter().map(|e| e.eval_f(cur, nxt, pubs, sel).as_canonical_u32()).collect();
                let e = bal.entry((it.bus, msg)).or_insert(0);
                *e += if it.send { c as i128 } else { -(c as i128) };
            }
        }
    }
    if std::env::var("WASMBASE_BUS_DEBUG").is_ok() {
        let mut per: HashMap<(u16, Vec<u32>), i128> = HashMap::new();
        for (ti, spec) in air.tables.iter().enumerate() {
            let m = &g.mats[ti];
            let w = spec.cols.len();
            let h = m.values.len() / w;
            for r in 0..h {
                let cur = &m.values[r * w..(r + 1) * w];
                let nr = (r + 1) % h;
                let nxt = &m.values[nr * w..(nr + 1) * w];
                let sel = [fe((r == 0) as u64), fe((r == h - 1) as u64), fe((r != h - 1) as u64)];
                for it in &spec.inters {
                    let c = it.count.eval_f(cur, nxt, &g.pubs, sel).as_canonical_u32();
                    if c == 0 { continue; }
                    let msg: Vec<u32> = it.msg.iter().map(|e| e.eval_f(cur, nxt, &g.pubs, sel).as_canonical_u32()).collect();
                    if it.bus == 3 || (it.bus == 4 && msg[0] == 0) {
                        eprintln!("BUS {} send={} {:?} {}", spec.name, it.send, msg, c);
                        per.entry((it.bus, msg)).or_insert(0);
                    }
                }
            }
        }
        let _ = per;
    }
    let bad: Vec<_> = bal.iter().filter(|(_, v)| **v != 0).take(5).collect();
    if bad.is_empty() { Ok(()) } else { Err(format!("unbalanced: {bad:?}")) }
}

#[allow(dead_code)]
pub fn felt(x: i64) -> F {
    fi(x)
}
