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
    pub mult: Expr,
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
            if t.max_log > 22 {
                return Err(format!("table {ti}: maxLog {} > 22", t.max_log));
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
// JSON (provisional; follows the Lean constructors one to one)
//   {"const":n} {"col":c,"next":b} {"pub":i} "isFirst" "isLast" "isTransition"
//   {"add":[a,b]} {"mul":[a,b]} {"neg":a}
// ---------------------------------------------------------------------------

fn get<'a>(v: &'a Value, k: &str) -> Result<&'a Value, String> {
    v.get(k).ok_or_else(|| format!("missing field {k}"))
}
fn nat(v: &Value) -> Result<u64, String> {
    v.as_u64().ok_or_else(|| format!("expected natural, got {v}"))
}

pub fn parse_expr(v: &Value) -> Result<Expr, String> {
    if let Some(s) = v.as_str() {
        return match s {
            "isFirst" => Ok(Expr::IsFirst),
            "isLast" => Ok(Expr::IsLast),
            "isTransition" => Ok(Expr::IsTransition),
            _ => Err(format!("unknown expr {s}")),
        };
    }
    let o = v.as_object().ok_or("expr must be object or string")?;
    if let Some(c) = o.get("const") {
        return Ok(Expr::Const(nat(c)?));
    }
    if let Some(c) = o.get("col") {
        let next = o.get("next").and_then(|b| b.as_bool()).unwrap_or(false);
        return Ok(Expr::Col(nat(c)? as usize, next));
    }
    if let Some(c) = o.get("pub") {
        return Ok(Expr::Pub(nat(c)? as usize));
    }
    for (k, ctor) in [("add", 0), ("mul", 1)] {
        if let Some(ab) = o.get(k) {
            let ab = ab.as_array().ok_or("binary op needs [a,b]")?;
            if ab.len() != 2 {
                return Err("binary op needs [a,b]".into());
            }
            let (a, b) = (parse_expr(&ab[0])?, parse_expr(&ab[1])?);
            return Ok(if ctor == 0 { Expr::add(a, b) } else { Expr::mul(a, b) });
        }
    }
    if let Some(a) = o.get("neg") {
        return Ok(Expr::neg(parse_expr(a)?));
    }
    Err(format!("unknown expr {v}"))
}

fn parse_air(v: &Value) -> Result<Air, String> {
    let mut tables = vec![];
    for (i, t) in get(v, "tables")?.as_array().ok_or("tables")?.iter().enumerate() {
        let mut interactions = vec![];
        if let Some(is) = t.get("interactions") {
            for it in is.as_array().ok_or("interactions")? {
                interactions.push(Interaction {
                    bus: nat(get(it, "bus")?)? as usize,
                    mult: parse_expr(get(it, "mult")?)?,
                    msg: get(it, "msg")?
                        .as_array()
                        .ok_or("msg")?
                        .iter()
                        .map(parse_expr)
                        .collect::<Result<_, _>>()?,
                    send: get(it, "send")?.as_bool().ok_or("send")?,
                });
            }
        }
        tables.push(Table {
            name: t.get("name").and_then(|n| n.as_str()).map(String::from).unwrap_or(format!("t{i}")),
            width: nat(get(t, "width")?)? as usize,
            constraints: get(t, "constraints")?
                .as_array()
                .ok_or("constraints")?
                .iter()
                .map(parse_expr)
                .collect::<Result<_, _>>()?,
            interactions,
            max_log: nat(get(t, "maxLog")?)? as usize,
        });
    }
    let air = Air {
        tables,
        num_buses: nat(get(v, "numBuses")?)? as usize,
        num_pub: nat(get(v, "numPub")?)? as usize,
    };
    Ok(air)
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
