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

/// A public segment (`ZkFormal.V2.PubSeg`, FORMATS.md §8.2): messages the
/// verifier reads from the public vector and puts on bus `bus`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PubSeg {
    pub bus: usize,
    pub send: bool,
    /// payload bytes per record
    pub width: usize,
    /// `pub` index of the little-endian u32 record count
    pub count_at: usize,
    /// static payload offset (used when `start_at` is `None`)
    pub start: usize,
    /// constant message prefix (field constants)
    pub prefix: Vec<u64>,
    /// implicit record index `index_base + j`, appended after the prefix
    pub index_base: Option<u64>,
    /// `pub` index of a little-endian u32 payload offset
    pub start_at: Option<usize>,
}

/// An AIR with its proof parameters: `ZkFormal.V2.AirP` (`tables`,
/// `numBuses`, `numPub`, `pubSegs`, `maxPub`) and `Params.auxGroup`.
/// With `v2 = false` (format `np-air-v1`), `pub_segs` is empty and
/// `aux_group = 1`, which is exactly `np-udr-stark-v1`.
#[derive(Clone, Debug)]
pub struct Air {
    pub tables: Vec<Table>,
    pub num_buses: usize,
    pub num_pub: usize,
    pub pub_segs: Vec<PubSeg>,
    pub max_pub: usize,
    pub aux_group: usize,
    pub v2: bool,
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
    /// Constraint degree (`Table.degree g`, including aux constraints, ≥ 2).
    pub fn degree(&self, g: usize) -> usize {
        crate::aux::table_degree(self, g)
    }
    /// Number of quotient chunks `degree - 1`, each of degree `< T`.
    pub fn num_quot_chunks(&self, g: usize) -> usize {
        self.degree(g) - 1
    }
    /// Number of `K`-valued aux columns (`Table.auxCount g`).
    pub fn aux_width(&self, g: usize) -> usize {
        crate::aux::AuxLayout::new(self, g).width()
    }
    /// Number of bus finals (send groups + receive groups).
    pub fn num_finals(&self, g: usize) -> usize {
        crate::aux::AuxLayout::new(self, g).num_finals()
    }
}

impl PubSeg {
    /// `PubSeg.messageWidth`: prefix, optional index, payload.
    pub fn message_width(&self) -> usize {
        self.prefix.len() + self.index_base.is_some() as usize + self.width
    }
}

impl Air {
    /// A v1 AIR (`np-air-v1`, no public segments, `auxGroup = 1`).
    pub fn v1(tables: Vec<Table>, num_buses: usize, num_pub: usize) -> Air {
        Air {
            tables,
            num_buses,
            num_pub,
            pub_segs: vec![],
            max_pub: 0,
            aux_group: 1,
            v2: false,
        }
    }

    /// The same AIR proved with `auxGroup = g` (`ZkFormal.V2.G.pg g`).
    pub fn with_aux_group(mut self, g: usize) -> Air {
        assert!((1..=3).contains(&g), "auxGroup must be in 1..=3");
        self.aux_group = g;
        self
    }

    /// `Air.wf 16` and `Table.degree ≤ 16` (`headerOk` without the header).
    pub fn validate(&self) -> Result<(), String> {
        if self.tables.is_empty() {
            return Err("AIR has no tables".into());
        }
        for (ti, t) in self.tables.iter().enumerate() {
            let chk = |e: &Expr| {
                check_expr(e, t.width, self.num_pub).map_err(|m| format!("table {ti}: {m}"))
            };
            for c in &t.constraints {
                chk(c)?;
                if c.degree() > 16 {
                    return Err(format!("table {ti}: constraint degree > 16"));
                }
            }
            for i in &t.interactions {
                if i.bus >= self.num_buses {
                    return Err(format!("table {ti}: bus {} out of range", i.bus));
                }
                if i.mult.len() > 25 {
                    return Err(format!("table {ti}: more than 25 multiplicity bits"));
                }
                for e in i.mult.iter().chain(&i.msg) {
                    chk(e)?;
                }
            }
            if t.degree(self.aux_group) > 16 {
                return Err(format!(
                    "table {ti}: degree {} > 16",
                    t.degree(self.aux_group)
                ));
            }
            if t.max_log > 22 || t.max_log < 1 {
                return Err(format!("table {ti}: maxLog {} not in [1, 22]", t.max_log));
            }
        }
        if !(1..=3).contains(&self.aux_group) || (!self.v2 && self.aux_group != 1) {
            return Err(format!("auxGroup {} not allowed", self.aux_group));
        }
        if !self.v2 && (!self.pub_segs.is_empty() || self.max_pub != 0) {
            return Err("np-air-v1 has no public segments".into());
        }
        for (si, sg) in self.pub_segs.iter().enumerate() {
            if sg.bus >= self.num_buses {
                return Err(format!("pubSeg {si}: bus {} out of range", sg.bus));
            }
            if sg.width == 0 {
                return Err(format!("pubSeg {si}: width 0"));
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
    v.as_u64()
        .ok_or_else(|| format!("expected natural, got {v}"))
}
fn arr<'a>(v: &'a Value, what: &str) -> Result<&'a Vec<Value>, String> {
    v.as_array()
        .ok_or_else(|| format!("{what}: expected array"))
}

pub fn parse_expr(v: &Value) -> Result<Expr, String> {
    let a = arr(v, "expr")?;
    let tag = a
        .first()
        .and_then(|t| t.as_str())
        .ok_or("expr: missing tag")?;
    let want = |n: usize| -> Result<(), String> {
        if a.len() == n {
            Ok(())
        } else {
            Err(format!("expr {tag}: arity"))
        }
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

fn opt_nat(v: &Value) -> Result<Option<u64>, String> {
    if v.is_null() {
        Ok(None)
    } else {
        nat(v).map(Some)
    }
}

fn parse_pub_seg(v: &Value) -> Result<PubSeg, String> {
    Ok(PubSeg {
        bus: nat(get(v, "bus")?)? as usize,
        send: get(v, "send")?.as_bool().ok_or("pubSeg send")?,
        width: nat(get(v, "width")?)? as usize,
        count_at: nat(get(v, "countAt")?)? as usize,
        start: nat(get(v, "start")?)? as usize,
        prefix: arr(get(v, "prefix")?, "prefix")?
            .iter()
            .map(nat)
            .collect::<Result<_, _>>()?,
        index_base: opt_nat(get(v, "indexBase")?)?,
        start_at: opt_nat(get(v, "startAt")?)?.map(|x| x as usize),
    })
}

fn parse_air(v: &Value) -> Result<Air, String> {
    let v2 = match get(v, "format")?.as_str() {
        Some("np-air-v1") => false,
        Some("np-air-v2") => true,
        _ => return Err("format must be np-air-v1 or np-air-v2".into()),
    };
    let mut tables = vec![];
    for (i, t) in arr(get(v, "tables")?, "tables")?.iter().enumerate() {
        let mut interactions = vec![];
        for it in arr(get(t, "interactions")?, "interactions")? {
            interactions.push(Interaction {
                bus: nat(get(it, "bus")?)? as usize,
                mult: arr(get(it, "mult")?, "mult")?
                    .iter()
                    .map(parse_expr)
                    .collect::<Result<_, _>>()?,
                msg: arr(get(it, "msg")?, "msg")?
                    .iter()
                    .map(parse_expr)
                    .collect::<Result<_, _>>()?,
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
    let (pub_segs, max_pub) = if v2 {
        (
            arr(get(v, "pubSegs")?, "pubSegs")?
                .iter()
                .map(parse_pub_seg)
                .collect::<Result<_, _>>()?,
            nat(get(v, "maxPub")?)? as usize,
        )
    } else {
        (vec![], 0)
    };
    Ok(Air {
        tables,
        num_buses: nat(get(v, "numBuses")?)? as usize,
        num_pub: nat(get(v, "numPub")?)? as usize,
        pub_segs,
        max_pub,
        aux_group: 1,
        v2,
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
        if !self.v2 {
            return format!(
                "{{\"format\":\"np-air-v1\",\"numBuses\":{},\"numPub\":{},\"tables\":{}}}",
                self.num_buses, self.num_pub, tables
            );
        }
        let opt = |o: Option<u64>| o.map_or("null".to_string(), |x| x.to_string());
        let segs = json_list(self.pub_segs.iter().map(|sg| {
            format!(
                "{{\"bus\":{},\"send\":{},\"width\":{},\"countAt\":{},\"start\":{},\"prefix\":{},\"indexBase\":{},\"startAt\":{}}}",
                sg.bus,
                sg.send,
                sg.width,
                sg.count_at,
                sg.start,
                json_list(sg.prefix.iter().map(|x| x.to_string())),
                opt(sg.index_base),
                opt(sg.start_at.map(|x| x as u64))
            )
        }));
        format!(
            "{{\"format\":\"np-air-v2\",\"numBuses\":{},\"numPub\":{},\"tables\":{},\"pubSegs\":{},\"maxPub\":{}}}",
            self.num_buses, self.num_pub, tables, segs, self.max_pub
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
        let outputs = constraints
            .iter()
            .map(|c| go(c, &mut ops, &mut memo))
            .collect();
        Tape { ops, outputs }
    }

    /// Evaluate over `K` with arbitrary (extension-valued) public inputs.
    pub fn eval_ext(
        &self,
        regs: &mut Vec<crate::field::EF>,
        col: impl Fn(usize, bool) -> crate::field::EF,
        pubv: impl Fn(usize) -> crate::field::EF,
        sel: [crate::field::EF; 3],
    ) {
        use crate::field::EF;
        regs.clear();
        for op in &self.ops {
            let v = match *op {
                Op::Const(c) => EF::from(F::new(c)),
                Op::Col(c, n) => col(c as usize, n),
                Op::Pub(i) => pubv(i as usize),
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
