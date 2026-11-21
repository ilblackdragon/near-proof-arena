//! The classical NEAR AIR (`ZkFormal.Air.Air` / `ZkFormal.V2.AirP`, exported by Lean as
//! `np-air-v2`, `docs/zk-formal/FORMATS.md` §1) interpreted as openvm/SWIRL AIRs, **unchanged**:
//! every constraint of `Table.allConstraints` (user constraints + the multiplicity-bit booleanity
//! constraints the export appends) is asserted as is; every interaction becomes one LogUp
//! interaction on the same bus with the same message and the count `Σ_k 2^k · b_k` (sends `+`,
//! receives `−`).  The classical `col c true` (row `r+1 mod 2^log`, cyclic) is SWIRL's next-row
//! rotation (also cyclic), and `isFirst / isLast / isTransition` are SWIRL's selectors.
//!
//! Two synthetic tables are added by `main.rs` (not part of the classical AIR):
//! * `TAPE`: the public-segment messages of `AirP.pubSegs` (verifier-computed in the classical
//!   protocol), as a cached trace whose commitment V_d recomputes from the claim;
//! * `EXT`: the net messages of the classical tables left out of the demo (stand-in only).
use openvm_stark_backend::{
    PartitionedBaseAir, air_builders::PartitionedAirBuilder, interaction::InteractionBuilder,
};
use p3_air::{Air, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use serde_json::Value;

#[derive(Clone, Debug)]
pub enum E {
    C(u64),
    Col(usize, bool),
    P(usize),
    First,
    Last,
    Trans,
    Add(Box<E>, Box<E>),
    Mul(Box<E>, Box<E>),
    Neg(Box<E>),
}

impl E {
    /// `Expr.toJson` (zk-formal/ZkFormal/Air/Export.lean) inverse.
    pub fn parse(v: &Value) -> E {
        let a = v.as_array().expect("expr array");
        let sub = |i: usize| Box::new(E::parse(&a[i]));
        match a[0].as_str().unwrap() {
            "c" => E::C(a[1].as_u64().unwrap()),
            "v" => E::Col(a[1].as_u64().unwrap() as usize, a[2].as_u64().unwrap() == 1),
            "p" => E::P(a[1].as_u64().unwrap() as usize),
            "first" => E::First,
            "last" => E::Last,
            "trans" => E::Trans,
            "+" => E::Add(sub(1), sub(2)),
            "*" => E::Mul(sub(1), sub(2)),
            "-" => E::Neg(sub(1)),
            t => panic!("bad expr tag {t}"),
        }
    }
    pub fn eval_f<F: PrimeCharacteristicRing + Copy>(
        &self,
        cur: &[F],
        nxt: &[F],
        pubs: &[F],
        sel: [F; 3],
    ) -> F {
        match self {
            // `const c` is `c mod p` (Lean `Nat.cast`)
            E::C(n) => F::from_u64(*n),
            E::Col(i, false) => cur[*i],
            E::Col(i, true) => nxt[*i],
            E::P(i) => pubs.get(*i).copied().unwrap_or(F::ZERO),
            E::First => sel[0],
            E::Last => sel[1],
            E::Trans => sel[2],
            E::Add(a, b) => a.eval_f(cur, nxt, pubs, sel) + b.eval_f(cur, nxt, pubs, sel),
            E::Mul(a, b) => a.eval_f(cur, nxt, pubs, sel) * b.eval_f(cur, nxt, pubs, sel),
            E::Neg(a) => -a.eval_f(cur, nxt, pubs, sel),
        }
    }
    pub fn pub_bound(&self) -> usize {
        match self {
            E::P(i) => i + 1,
            E::Add(a, b) | E::Mul(a, b) => a.pub_bound().max(b.pub_bound()),
            E::Neg(a) => a.pub_bound(),
            _ => 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Inter {
    pub bus: u16,
    pub send: bool,
    /// multiplicity bits, least significant first (`Interaction.mult`)
    pub mult: Vec<E>,
    pub msg: Vec<E>,
}

/// One table.  For the synthetic harness tables `harness` holds the per-key interaction
/// selectors instead (see `main.rs`).
#[derive(Clone, Debug)]
pub struct TableSpec {
    pub name: String,
    pub width: usize,
    pub max_log: usize,
    pub constraints: Vec<E>,
    pub inters: Vec<Inter>,
    /// harness: (bus, message length) per selector column; columns = msg[0..W), cnt, sel[..]
    pub harness: Option<(usize, Vec<(u16, usize)>)>,
    /// whole trace committed as a cached trace (TAPE)
    pub cached: bool,
    /// number of public values this AIR reads (`max pub index + 1`)
    pub num_pub: usize,
}

pub struct ClassicalAir {
    #[allow(dead_code)]
    pub num_buses: usize,
    #[allow(dead_code)]
    pub num_pub: usize,
    pub tables: Vec<TableSpec>,
}

impl ClassicalAir {
    pub fn parse(text: &str, names: &[&str]) -> ClassicalAir {
        let v: Value = serde_json::from_str(text).expect("air json");
        let tables: Vec<TableSpec> = v["tables"]
            .as_array()
            .unwrap()
            .iter()
            .enumerate()
            .map(|(i, t)| {
                let constraints: Vec<E> = t["constraints"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(E::parse)
                    .collect();
                let inters: Vec<Inter> = t["interactions"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|i| Inter {
                        bus: i["bus"].as_u64().unwrap() as u16,
                        send: i["send"].as_bool().unwrap(),
                        mult: i["mult"].as_array().unwrap().iter().map(E::parse).collect(),
                        msg: i["msg"].as_array().unwrap().iter().map(E::parse).collect(),
                    })
                    .collect();
                let num_pub = constraints
                    .iter()
                    .chain(
                        inters
                            .iter()
                            .flat_map(|i| i.mult.iter().chain(i.msg.iter())),
                    )
                    .map(|e| e.pub_bound())
                    .max()
                    .unwrap_or(0);
                TableSpec {
                    name: names[i].to_string(),
                    width: t["width"].as_u64().unwrap() as usize,
                    max_log: t["maxLog"].as_u64().unwrap() as usize,
                    constraints,
                    inters,
                    harness: None,
                    cached: false,
                    num_pub,
                }
            })
            .collect();
        ClassicalAir {
            num_buses: v["numBuses"].as_u64().unwrap() as usize,
            num_pub: v["numPub"].as_u64().unwrap() as usize,
            tables,
        }
    }
}

pub struct JsonAir {
    pub spec: TableSpec,
}

impl<F> BaseAir<F> for JsonAir {
    fn width(&self) -> usize {
        self.spec.width
    }
}
impl<F> PartitionedBaseAir<F> for JsonAir {
    fn cached_main_widths(&self) -> Vec<usize> {
        if self.spec.cached {
            vec![self.spec.width]
        } else {
            vec![]
        }
    }
    fn common_main_width(&self) -> usize {
        // SWIRL needs a non-empty common main: a cached AIR carries one unused zero column
        if self.spec.cached { 1 } else { self.spec.width }
    }
    /// The per-table cap from the Lean export (`maxLog`).  `HoldsP` accepts any
    /// `1 <= log <= maxLog`, and the soundness lemmas (capacity, the A7 bound) are proved at
    /// `maxLog`, so the cap travels into the vk and is enforced by the native verifier, the NV
    /// program generator and V_d.
    fn max_log_trace_height(&self) -> Option<usize> {
        Some(self.spec.max_log)
    }
}
impl<F> BaseAirWithPublicValues<F> for JsonAir {
    fn num_public_values(&self) -> usize {
        self.spec.num_pub
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
        E::Col(i, false) => l[*i].clone(),
        E::Col(i, true) => n[*i].clone(),
        E::P(i) => p.get(*i).cloned().unwrap_or(AB::Expr::ZERO),
        E::First => b.is_first_row(),
        E::Last => b.is_last_row(),
        E::Trans => b.is_transition(),
        E::Add(x, y) => build(b, x, l, n, p) + build(b, y, l, n, p),
        E::Mul(x, y) => build(b, x, l, n, p) * build(b, y, l, n, p),
        E::Neg(x) => -build(b, x, l, n, p),
    }
}

impl<AB: AirBuilderWithPublicValues + InteractionBuilder + PartitionedAirBuilder> Air<AB>
    for JsonAir
{
    fn eval(&self, b: &mut AB) {
        let mut l: Vec<AB::Expr> = vec![];
        let mut n: Vec<AB::Expr> = vec![];
        if self.spec.cached {
            l.extend(
                b.cached_mains()[0]
                    .row_slice(0)
                    .unwrap()
                    .iter()
                    .map(|&v| v.into()),
            );
            n.extend(
                b.cached_mains()[0]
                    .row_slice(1)
                    .unwrap()
                    .iter()
                    .map(|&v| v.into()),
            );
        } else {
            let main = b.main();
            l.extend(main.row_slice(0).unwrap().iter().map(|&v| v.into()));
            n.extend(main.row_slice(1).unwrap().iter().map(|&v| v.into()));
        }
        let p: Vec<AB::Expr> = b.public_values().iter().map(|&v| v.into()).collect();
        if let Some((w, keys)) = &self.spec.harness {
            // columns msg[0..w), cnt, sel[k]: interaction k sends msg[..len_k] with count cnt·sel_k
            for (k, (bus, len)) in keys.iter().enumerate() {
                let msg: Vec<AB::Expr> = l[..*len].to_vec();
                let cnt = l[*w].clone() * l[*w + 1 + k].clone();
                b.push_interaction(*bus, msg, cnt, 1);
            }
            return;
        }
        for c in &self.spec.constraints {
            let e = build(b, c, &l, &n, &p);
            b.assert_zero(e);
        }
        for i in &self.spec.inters {
            if i.mult.is_empty() {
                continue; // multiplicity zero: contributes nothing in either protocol
            }
            let msg: Vec<AB::Expr> = i.msg.iter().map(|m| build(b, m, &l, &n, &p)).collect();
            let mut cnt = AB::Expr::ZERO;
            for (k, bit) in i.mult.iter().enumerate() {
                cnt += build(b, bit, &l, &n, &p) * AB::Expr::from_u64(1u64 << k);
            }
            let cnt = if i.send { cnt } else { -cnt };
            b.push_interaction(i.bus, msg, cnt, 1);
        }
    }
}
