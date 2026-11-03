//! The public-input view of an AIR: what a verifier needs to recompute the public statement
//! (`numPub`, `pubSegs`, `maxPub`, the table count and each table's public-input bound), read in
//! one streaming pass over the AIR JSON without building the constraint trees.
//!
//! Intended for an AIR whose bytes the caller has already pinned (e.g. by a trusted hash): the
//! expression trees are scanned for `["p", i]` nodes only and are not otherwise validated.
//! [`AirPublic::of`] derives the same view from a fully parsed, validated [`Air`].
use std::fmt;

use serde::de::{self, Deserialize, Deserializer, IgnoredAny, SeqAccess, Visitor};
use serde_json::Value;

use crate::air::{Air, Expr, parse_pub_seg};

#[derive(Clone, Debug)]
pub struct AirPublic {
    /// `numBuses`, `numPub`, `pubSegs`, `maxPub` and the format flag of the AIR; `tables` is
    /// left empty (use `num_tables` / `table_num_pub`).
    pub air: Air,
    pub num_tables: usize,
    /// per table: max `pub` index read by a constraint or interaction (mult/msg), plus one
    pub table_num_pub: Vec<usize>,
}

impl AirPublic {
    /// The view of a fully parsed AIR.
    pub fn of(air: &Air) -> AirPublic {
        let table_num_pub = air
            .tables
            .iter()
            .map(|t| {
                t.constraints
                    .iter()
                    .chain(t.interactions.iter().flat_map(|i| i.mult.iter().chain(i.msg.iter())))
                    .map(pub_bound)
                    .max()
                    .unwrap_or(0)
            })
            .collect();
        AirPublic {
            air: Air { tables: vec![], ..air.clone() },
            num_tables: air.tables.len(),
            table_num_pub,
        }
    }

    /// One streaming pass over the AIR JSON (`np-air-v1` / `np-air-v2`).
    pub fn from_json_slice(bytes: &[u8]) -> Result<AirPublic, String> {
        let top: Top = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        let v2 = match top.format.as_str() {
            "np-air-v1" => false,
            "np-air-v2" => true,
            _ => return Err("format must be np-air-v1 or np-air-v2".into()),
        };
        let (pub_segs, max_pub) = if v2 {
            let segs = top.pub_segs.ok_or("missing field pubSegs")?;
            (
                segs.as_array()
                    .ok_or("pubSegs: expected array")?
                    .iter()
                    .map(parse_pub_seg)
                    .collect::<Result<_, _>>()?,
                top.max_pub.ok_or("missing field maxPub")? as usize,
            )
        } else {
            (vec![], 0)
        };
        Ok(AirPublic {
            air: Air {
                tables: vec![],
                num_buses: top.num_buses as usize,
                num_pub: top.num_pub as usize,
                pub_segs,
                max_pub,
                aux_group: 1,
                v2,
            },
            num_tables: top.tables.len(),
            table_num_pub: top
                .tables
                .iter()
                .map(|t| {
                    t.constraints
                        .iter()
                        .chain(t.interactions.iter().flat_map(|i| i.mult.iter().chain(i.msg.iter())))
                        .map(|b| b.0)
                        .max()
                        .unwrap_or(0)
                })
                .collect(),
        })
    }
}

fn pub_bound(e: &Expr) -> usize {
    match e {
        Expr::Pub(i) => i + 1,
        Expr::Add(a, b) | Expr::Mul(a, b) => pub_bound(a).max(pub_bound(b)),
        Expr::Neg(a) => pub_bound(a),
        _ => 0,
    }
}

#[derive(serde::Deserialize)]
struct Top {
    format: String,
    #[serde(rename = "numBuses")]
    num_buses: u64,
    #[serde(rename = "numPub")]
    num_pub: u64,
    tables: Vec<TableP>,
    #[serde(rename = "pubSegs", default)]
    pub_segs: Option<Value>,
    #[serde(rename = "maxPub", default)]
    max_pub: Option<u64>,
}

#[derive(serde::Deserialize)]
struct TableP {
    constraints: Vec<PubBound>,
    interactions: Vec<InterP>,
}

#[derive(serde::Deserialize)]
struct InterP {
    mult: Vec<PubBound>,
    msg: Vec<PubBound>,
}

/// The `pub` bound of one expression (`max i + 1` over its `["p", i]` nodes, 0 if none).
struct PubBound(usize);

impl<'de> Deserialize<'de> for PubBound {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_seq(ExprVisitor)
    }
}

struct ExprVisitor;

impl<'de> Visitor<'de> for ExprVisitor {
    type Value = PubBound;
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("an expression array")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut s: A) -> Result<PubBound, A::Error> {
        let tag: &'de str = s
            .next_element()?
            .ok_or_else(|| de::Error::custom("expr: missing tag"))?;
        let mut bound = 0;
        match tag {
            "p" => {
                let i: u64 = s
                    .next_element()?
                    .ok_or_else(|| de::Error::custom("expr p: arity"))?;
                bound = i as usize + 1;
            }
            "+" | "*" | "-" => {
                while let Some(PubBound(b)) = s.next_element()? {
                    bound = bound.max(b);
                }
            }
            _ => {}
        }
        while s.next_element::<IgnoredAny>()?.is_some() {}
        Ok(PubBound(bound))
    }
}
