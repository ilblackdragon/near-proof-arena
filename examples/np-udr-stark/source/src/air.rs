//! The AIR, mirroring `ZkFormal.Air` (DESIGN.md §5.1), its JSON import and a
//! compiled straight-line form ("tape") used by the prover and the reference
//! verifier.
//!
//! Selector semantics (exact 0/1 indicators on the trace domain
//! `H = ⟨ω_T⟩`, row `r` ↔ `ω_T^r`):
//! * `isFirst = L_1(x) = (x^T - 1) / (T·(x - 1))`
//! * `isLast  = L_h(x) = h·(x^T - 1) / (T·(x - h))`, `h = ω_T^{-1}`
//! * `isTransition = 1 - isLast`
//! Each counts as degree 1 in the constraint degree (it has degree `T - 1`).
//! `col c true` is column `c` on row `r + 1 mod T` (polynomially `f_c(ω_T x)`).

use std::collections::HashMap;

use p3_field::PrimeCharacteristicRing;
use serde_json::Value;

use crate::field::{F, P};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Const(u64),
    Col(usize, bool),
    Pub(usize),
    IsFirst,
    IsLast,
    IsTransition,
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
}

#[derive(Clone, Debug)]
pub struct Interaction {
    pub bus: usize,
    /// multiplicity bits, least significant first
    pub mult: Vec<Expr>,
    pub msg: Vec<Expr>,
    pub send: bool,
}

#[derive(Clone, Debug)]
pub struct Table {
    pub name: String,
    pub width: usize,
    pub constraints: Vec<Expr>,
    pub interactions: Vec<Interaction>,
    pub max_log: usize,
}

#[derive(Clone, Debug)]
pub struct Air {
    pub tables: Vec<Table>,
    pub num_buses: usize,
    pub num_pub: usize,
}

impl Expr {
    pub fn degree(&self) -> usize {
        match self {
            Expr::Const(_) | Expr::Pub(_) => 0,
            Expr::Col(..) | Expr::IsFirst | Expr::IsLast | Expr::IsTransition => 1,
            Expr::Add(a, b) => a.degree().max(b.degree()),
            Expr::Mul(a, b) => a.degree() + b.degree(),
            Expr::Neg(a) => a.degree(),
        }
    }

    // Convenience constructors for hand-written AIRs.
    pub fn c(v: u64) -> Expr {
        Expr::Const(v)
    }
    pub fn col(c: usize) -> Expr {
        Expr::Col(c, false)
    }
    pub fn nxt(c: usize) -> Expr {
        Expr::Col(c, true)
    }
    pub fn add(a: Expr, b: Expr) -> Expr {
        Expr::Add(Box::new(a), Box::new(b))
    }
    pub fn mul(a: Expr, b: Expr) -> Expr {
        Expr::Mul(Box::new(a), Box::new(b))
    }
    pub fn neg(a: Expr) -> Expr {
        Expr::Neg(Box::new(a))
    }
    pub fn sub(a: Expr, b: Expr) -> Expr {
        Expr::add(a, Expr::neg(b))
    }
}

impl Table {
    /// Maximal constraint degree (at least 1).
    pub fn degree(&self) -> usize {
        self.constraints.iter().map(|c| c.degree()).max().unwrap_or(0).max(1)
    }
    /// Number of quotient chunks `max(1, d - 1)`, each of degree `< T`.
    pub fn num_quot_chunks(&self) -> usize {
        (self.degree().max(2)) - 1
    }
    /// Number of `K`-valued aux columns (grand-product accumulators).
    pub fn aux_width(&self) -> usize {
        // Buses are not yet supported (pending the L4/L3 grand-product
        // layout); AIRs with interactions are rejected by `Air::validate`.
        0
    }
}

impl Air {
    pub fn validate(&self) -> Result<(), String> {
        if self.tables.is_empty() {
            return Err("AIR has no tables".into());
        }
        for (ti, t) in self.tables.iter().enumerate() {
            if !t.interactions.is_empty() {
                return Err(format!("table {ti}: interactions not supported yet"));
            }
            if t.degree() > 16 {
                return Err(format!("table {ti}: constraint degree {} > 16", t.degree()));
            }
            if t.max_log > 22 || t.max_log < 1 {
                return Err(format!("table {ti}: maxLog {} not in [1, 22]", t.max_log));
            }
            for c in &t.constraints {
                check_expr(c, t.width, self.num_pub).map_err(|e| format!("table {ti}: {e}"))?;
            }
        }
        Ok(())
    }

    pub fn from_json(s: &str) -> Result<Air, String> {
        let v: Value = serde_json::from_str(s).map_err(|e| e.to_string())?;
        parse_air(&v)
    }
}

fn check_expr(e: &Expr, width: usize, num_pub: usize) -> Result<(), String> {
    match e {
        Expr::Col(c, _) if *c >= width => Err(format!("column {c} out of range")),
        Expr::Pub(i) if *i >= num_pub => Err(format!("public {i} out of range")),
        Expr::Add(a, b) | Expr::Mul(a, b) => {
            check_expr(a, width, num_pub)?;
            check_expr(b, width, num_pub)
        }
        Expr::Neg(a) => check_expr(a, width, num_pub),
        _ => Ok(()),
    }
}

// ---------------------------------------------------------------------------
// JSON import: format `np-air-v1` (`ZkFormal.Air.exportJson`, lane L4).
//   const c ["c",c]   col c next ["v",c,0|1]   pub i ["p",i]
//   ["first"] ["last"] ["trans"]   ["+",a,b] ["*",a,b] ["-",a]
// Table `constraints` is `Table.allConstraints` (user constraints followed by
// the multiplicity-bit booleanity constraints), in α_c order.
// ---------------------------------------------------------------------------

fn get<'a>(v: &'a Value, k: &str) -> Result<&'a Value, String> {
    v.get(k).ok_or_else(|| format!("missing field {k}"))
}
fn nat(v: &Value) -> Result<u64, String> {
    v.as_u64().ok_or_else(|| format!("expected natural, got {v}"))
}
fn arr<'a>(v: &'a Value, what: &str) -> Result<&'a Vec<Value>, String> {
    v.as_array().ok_or_else(|| format!("{what}: expected array"))
}

pub fn parse_expr(v: &Value) -> Result<Expr, String> {
    let a = arr(v, "expr")?;
    let tag = a.first().and_then(|t| t.as_str()).ok_or("expr: missing tag")?;
    let want = |n: usize| -> Result<(), String> {
        if a.len() == n { Ok(()) } else { Err(format!("expr {tag}: arity")) }
    };
    Ok(match tag {
        "c" => {
            want(2)?;
            Expr::Const(nat(&a[1])?)
        }
        "v" => {
            want(3)?;
            let nx = nat(&a[2])?;
            if nx > 1 {
                return Err("expr v: next must be 0/1".into());
            }
            Expr::Col(nat(&a[1])? as usize, nx == 1)
        }
        "p" => {
            want(2)?;
            Expr::Pub(nat(&a[1])? as usize)
        }
        "first" => {
            want(1)?;
            Expr::IsFirst
        }
        "last" => {
            want(1)?;
            Expr::IsLast
        }
        "trans" => {
            want(1)?;
            Expr::IsTransition
        }
        "+" => {
            want(3)?;
            Expr::add(parse_expr(&a[1])?, parse_expr(&a[2])?)
        }
        "*" => {
            want(3)?;
            Expr::mul(parse_expr(&a[1])?, parse_expr(&a[2])?)
        }
        "-" => {
            want(2)?;
            Expr::neg(parse_expr(&a[1])?)
        }
        _ => return Err(format!("unknown expr tag {tag}")),
    })
}

fn parse_air(v: &Value) -> Result<Air, String> {
    if get(v, "format")?.as_str() != Some("np-air-v1") {
        return Err("format must be np-air-v1".into());
    }
    let mut tables = vec![];
    for (i, t) in arr(get(v, "tables")?, "tables")?.iter().enumerate() {
        let mut interactions = vec![];
        for it in arr(get(t, "interactions")?, "interactions")? {
            interactions.push(Interaction {
                bus: nat(get(it, "bus")?)? as usize,
                mult: arr(get(it, "mult")?, "mult")?.iter().map(parse_expr).collect::<Result<_, _>>()?,
                msg: arr(get(it, "msg")?, "msg")?.iter().map(parse_expr).collect::<Result<_, _>>()?,
                send: get(it, "send")?.as_bool().ok_or("send")?,
            });
        }
        tables.push(Table {
            name: format!("t{i}"),
            width: nat(get(t, "width")?)? as usize,
            constraints: arr(get(t, "constraints")?, "constraints")?
                .iter()
                .map(parse_expr)
                .collect::<Result<_, _>>()?,
            interactions,
            max_log: nat(get(t, "maxLog")?)? as usize,
        });
    }
    Ok(Air {
        tables,
        num_buses: nat(get(v, "numBuses")?)? as usize,
        num_pub: nat(get(v, "numPub")?)? as usize,
    })
}

/// Export in `np-air-v1` (inverse of `Air::from_json`; used for tests and
/// for hand-written Rust AIRs). `constraints` are written as stored, so a
/// table built in Rust must already contain its booleanity constraints.
impl Expr {
    pub fn to_json(&self) -> String {
        match self {
            Expr::Const(c) => format!("[\"c\",{c}]"),
            Expr::Col(c, n) => format!("[\"v\",{c},{}]", *n as u8),
            Expr::Pub(i) => format!("[\"p\",{i}]"),
            Expr::IsFirst => "[\"first\"]".into(),
            Expr::IsLast => "[\"last\"]".into(),
            Expr::IsTransition => "[\"trans\"]".into(),
            Expr::Add(a, b) => format!("[\"+\",{},{}]", a.to_json(), b.to_json()),
            Expr::Mul(a, b) => format!("[\"*\",{},{}]", a.to_json(), b.to_json()),
            Expr::Neg(a) => format!("[\"-\",{}]", a.to_json()),
        }
    }
}

fn json_list(xs: impl Iterator<Item = String>) -> String {
    format!("[{}]", xs.collect::<Vec<_>>().join(","))
}

impl Air {
    pub fn to_json(&self) -> String {
        let tables = json_list(self.tables.iter().map(|t| {
            let ints = json_list(t.interactions.iter().map(|i| {
                format!(
                    "{{\"bus\":{},\"send\":{},\"mult\":{},\"msg\":{}}}",
                    i.bus,
                    i.send,
                    json_list(i.mult.iter().map(|e| e.to_json())),
                    json_list(i.msg.iter().map(|e| e.to_json()))
                )
            }));
            format!(
                "{{\"width\":{},\"maxLog\":{},\"constraints\":{},\"interactions\":{}}}",
                t.width,
                t.max_log,
                json_list(t.constraints.iter().map(|e| e.to_json())),
                ints
            )
        }));
        format!(
            "{{\"format\":\"np-air-v1\",\"numBuses\":{},\"numPub\":{},\"tables\":{}}}",
            self.num_buses, self.num_pub, tables
        )
    }
}

// ---------------------------------------------------------------------------
// Compiled form: hash-consed straight-line program.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Const(u32),
    Col(u32, bool),
    Pub(u32),
    IsFirst,
    IsLast,
    IsTransition,
    Add(u32, u32),
    Mul(u32, u32),
    Neg(u32),
}

/// A straight-line program; `outputs[i]` is the register of constraint `i`.
#[derive(Clone, Debug)]
pub struct Tape {
    pub ops: Vec<Op>,
    pub outputs: Vec<u32>,
}

impl Tape {
    pub fn compile(constraints: &[Expr]) -> Tape {
        let mut ops = vec![];
        let mut memo: HashMap<Op, u32> = HashMap::new();
        fn go(e: &Expr, ops: &mut Vec<Op>, memo: &mut HashMap<Op, u32>) -> u32 {
            let op = match e {
                Expr::Const(c) => Op::Const((*c % P as u64) as u32),
                Expr::Col(c, n) => Op::Col(*c as u32, *n),
                Expr::Pub(i) => Op::Pub(*i as u32),
                Expr::IsFirst => Op::IsFirst,
                Expr::IsLast => Op::IsLast,
                Expr::IsTransition => Op::IsTransition,
                Expr::Add(a, b) => Op::Add(go(a, ops, memo), go(b, ops, memo)),
                Expr::Mul(a, b) => Op::Mul(go(a, ops, memo), go(b, ops, memo)),
                Expr::Neg(a) => Op::Neg(go(a, ops, memo)),
            };
            *memo.entry(op).or_insert_with(|| {
                ops.push(op);
                (ops.len() - 1) as u32
            })
        }
        let outputs = constraints.iter().map(|c| go(c, &mut ops, &mut memo)).collect();
        Tape { ops, outputs }
    }

    /// Evaluate over any ring `R` containing `F`. `col(c, next)` and the
    /// selectors are supplied by the caller.
    #[inline]
    pub fn eval<R: PrimeCharacteristicRing + Copy + From<F>>(
        &self,
        regs: &mut Vec<R>,
        col: impl Fn(usize, bool) -> R,
        pubs: &[F],
        sel: [R; 3],
    ) {
        regs.clear();
        for op in &self.ops {
            let v = match *op {
                Op::Const(c) => R::from(F::new(c)),
                Op::Col(c, n) => col(c as usize, n),
                Op::Pub(i) => R::from(pubs[i as usize]),
                Op::IsFirst => sel[0],
                Op::IsLast => sel[1],
                Op::IsTransition => sel[2],
                Op::Add(a, b) => regs[a as usize] + regs[b as usize],
                Op::Mul(a, b) => regs[a as usize] * regs[b as usize],
                Op::Neg(a) => -regs[a as usize],
            };
            regs.push(v);
        }
    }
}
