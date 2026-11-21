//! Interpreter of the Lean-exported AIR (`wasmbase-tool air <nloc> <ncode>`).
//!
//! The Lean value `WasmBase.wasmBaseAir` is the single source of truth: every constraint and
//! interaction of every table is read from its JSON export and replayed here through the openvm
//! `AirBuilder` / `InteractionBuilder` interface, so the SWIRL keygen's symbolic DAG is built from
//! exactly the Lean expressions.  Nothing in this file is specific to the Wasm chips; the column
//! layout is only used by the trace generator, by name.
use openvm_stark_backend::{PartitionedBaseAir, air_builders::PartitionedAirBuilder, interaction::InteractionBuilder};
use p3_air::{Air, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use serde_json::Value;

#[derive(Clone, Debug)]
pub enum E {
    C(u64),
    V(usize),
    N(usize),
    P(usize),
    First,
    Last,
    Trans,
    Add(Box<E>, Box<E>),
    Sub(Box<E>, Box<E>),
    Mul(Box<E>, Box<E>),
}

impl E {
    pub fn parse(v: &Value) -> E {
        let a = v.as_array().expect("expr array");
        let tag = a[0].as_str().unwrap();
        let num = |i: usize| a[i].as_u64().unwrap();
        let sub = |i: usize| Box::new(E::parse(&a[i]));
        match tag {
            "c" => E::C(num(1)),
            "v" => E::V(num(1) as usize),
            "n" => E::N(num(1) as usize),
            "p" => E::P(num(1) as usize),
            "first" => E::First,
            "last" => E::Last,
            "trans" => E::Trans,
            "+" => E::Add(sub(1), sub(2)),
            "-" => E::Sub(sub(1), sub(2)),
            "*" => E::Mul(sub(1), sub(2)),
            t => panic!("bad expr tag {t}"),
        }
    }
    /// Evaluate over plain field values (trace generation self-checks, difftest).
    pub fn eval_f<F: PrimeCharacteristicRing + Copy>(
        &self,
        cur: &[F],
        nxt: &[F],
        pubs: &[F],
        sel: [F; 3],
    ) -> F {
        match self {
            E::C(n) => F::from_u64(*n),
            E::V(i) => cur[*i],
            E::N(i) => nxt[*i],
            E::P(i) => pubs.get(*i).copied().unwrap_or(F::ZERO),
            E::First => sel[0],
            E::Last => sel[1],
            E::Trans => sel[2],
            E::Add(a, b) => a.eval_f(cur, nxt, pubs, sel) + b.eval_f(cur, nxt, pubs, sel),
            E::Sub(a, b) => a.eval_f(cur, nxt, pubs, sel) - b.eval_f(cur, nxt, pubs, sel),
            E::Mul(a, b) => a.eval_f(cur, nxt, pubs, sel) * b.eval_f(cur, nxt, pubs, sel),
        }
    }
    pub fn uses_next(&self) -> bool {
        match self {
            E::N(_) => true,
            E::Add(a, b) | E::Sub(a, b) | E::Mul(a, b) => a.uses_next() || b.uses_next(),
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Inter {
    pub bus: u16,
    pub send: bool,
    pub count: E,
    pub msg: Vec<E>,
}

#[derive(Clone, Debug)]
pub struct TableSpec {
    pub name: String,
    /// Leading columns committed as a separate cached trace (CODE: the records); 0 otherwise.
    pub cached: usize,
    pub cols: Vec<String>,
    pub degree: usize,
    pub constraints: Vec<E>,
    pub inters: Vec<Inter>,
}

impl TableSpec {
    pub fn col(&self, name: &str) -> usize {
        self.cols
            .iter()
            .position(|c| c == name)
            .unwrap_or_else(|| panic!("{}: no column {name}", self.name))
    }
}

#[derive(Clone)]
pub struct AirSpec {
    pub num_pub: usize,
    pub tables: Vec<TableSpec>,
}

impl AirSpec {
    pub fn parse(text: &str) -> AirSpec {
        let v: Value = serde_json::from_str(text).expect("air json");
        let tables = v["tables"]
            .as_array()
            .unwrap()
            .iter()
            .map(|t| TableSpec {
                name: t["name"].as_str().unwrap().to_string(),
                cached: t["cached"].as_u64().unwrap_or(0) as usize,
                cols: t["cols"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|c| c.as_str().unwrap().to_string())
                    .collect(),
                degree: t["degree"].as_u64().unwrap() as usize,
                constraints: t["constraints"].as_array().unwrap().iter().map(E::parse).collect(),
                inters: t["inters"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|i| Inter {
                        bus: i["bus"].as_u64().unwrap() as u16,
                        send: i["send"].as_bool().unwrap(),
                        count: E::parse(&i["count"]),
                        msg: i["msg"].as_array().unwrap().iter().map(E::parse).collect(),
                    })
                    .collect(),
            })
            .collect();
        AirSpec {
            num_pub: v["numPub"].as_u64().unwrap() as usize,
            tables,
        }
    }
    pub fn index(&self, name: &str) -> usize {
        self.tables.iter().position(|t| t.name == name).unwrap()
    }
}

/// One table of the AIR set, as an openvm AIR.  Only BOUNDARY reads public values.
pub struct JsonAir {
    pub spec: TableSpec,
    pub num_pub: usize,
}

impl JsonAir {
    pub fn reads_pub(spec: &TableSpec) -> bool {
        fn has_p(e: &E) -> bool {
            match e {
                E::P(_) => true,
                E::Add(a, b) | E::Sub(a, b) | E::Mul(a, b) => has_p(a) || has_p(b),
                _ => false,
            }
        }
        spec.constraints.iter().any(has_p)
            || spec.inters.iter().any(|i| has_p(&i.count) || i.msg.iter().any(has_p))
    }
}

impl<F> BaseAir<F> for JsonAir {
    fn width(&self) -> usize {
        self.spec.cols.len()
    }
}
impl<F> PartitionedBaseAir<F> for JsonAir {
    fn cached_main_widths(&self) -> Vec<usize> {
        if self.spec.cached > 0 { vec![self.spec.cached] } else { vec![] }
    }
    fn common_main_width(&self) -> usize {
        self.spec.cols.len() - self.spec.cached
    }
}
impl<F> BaseAirWithPublicValues<F> for JsonAir {
    fn num_public_values(&self) -> usize {
        self.num_pub
    }
}

fn build<AB: AirBuilderWithPublicValues>(
    b: &AB,
    e: &E,
    l: &[AB::Expr],
    n: &[AB::Expr],
    p: &[AB::Expr],
) -> AB::Expr {
    match e {
        E::C(c) => AB::Expr::from_u64(*c),
        E::V(i) => l[*i].clone(),
        E::N(i) => n[*i].clone(),
        E::P(i) => p[*i].clone(),
        E::First => b.is_first_row(),
        E::Last => b.is_last_row(),
        E::Trans => b.is_transition(),
        E::Add(x, y) => build(b, x, l, n, p) + build(b, y, l, n, p),
        E::Sub(x, y) => build(b, x, l, n, p) - build(b, y, l, n, p),
        E::Mul(x, y) => build(b, x, l, n, p) * build(b, y, l, n, p),
    }
}

impl<AB: AirBuilderWithPublicValues + InteractionBuilder + PartitionedAirBuilder> Air<AB> for JsonAir {
    fn eval(&self, b: &mut AB) {
        // column space = cached columns (if any) followed by the common main
        let mut l: Vec<AB::Expr> = vec![];
        let mut n: Vec<AB::Expr> = vec![];
        if self.spec.cached > 0 {
            l.extend(b.cached_mains()[0].row_slice(0).unwrap().iter().map(|&v| v.into()));
            n.extend(b.cached_mains()[0].row_slice(1).unwrap().iter().map(|&v| v.into()));
            l.extend(b.common_main().row_slice(0).unwrap().iter().map(|&v| v.into()));
            n.extend(b.common_main().row_slice(1).unwrap().iter().map(|&v| v.into()));
        } else {
            let main = b.main();
            l.extend(main.row_slice(0).unwrap().iter().map(|&v| v.into()));
            n.extend(main.row_slice(1).unwrap().iter().map(|&v| v.into()));
        }
        let p: Vec<AB::Expr> = b.public_values().iter().map(|&v| v.into()).collect();
        for c in &self.spec.constraints {
            let e = build(b, c, &l, &n, &p);
            b.assert_zero(e);
        }
        for i in &self.spec.inters {
            let msg: Vec<AB::Expr> = i.msg.iter().map(|m| build(b, m, &l, &n, &p)).collect();
            let cnt = build(b, &i.count, &l, &n, &p);
            let cnt = if i.send { cnt } else { -cnt };
            b.push_interaction(i.bus, msg, cnt, 1);
        }
    }
}
