//! [lane E, M11e] Export the pinned NvAir constraint DAG and interactions as Lean data.
//!
//! Installed as `crates/recursion/src/nv/nv_export.rs` by `nv-export/setup.sh` into a private
//! e2e-tree deps tree (`setup_e2e_verify_deps.sh` with `E2E_ZK=1 E2E_TREE=1`; shared trees are
//! never modified).  Run:
//!
//!   NV_EXPORT_OUT=<file.lean> cargo test --release -p openvm-recursion-circuit --lib nv::nv_export -- --nocapture
//!
//! What is exported is exactly the object the verifier consumes: `vk.inner.per_air[0]
//! .symbolic_constraints` (the `SymbolicConstraintsDag` after the backend's DAG builder, i.e. after
//! its structural dedup and algebraic simplifications), from keygen of `NvCircuit::new(3, 17, 1)`
//! (one compression instance: AIRs NvAir, Sha512Air4, TableAir4, ByteAir).
//!
//! Two NvAir variants exist (nv/uair.rs `NvAir::program_part`):
//! * `program_part = false` (the wrap / FINAL layer): P0..P3 in common main, one main part. This
//!   is the exported DAG; column `c` is the full NvAir row index (0..NV_WIDTH).
//! * `program_part = true` (tree leaves / nodes, D0a L1..L4): P0..P3 a cached main part. Its DAG
//!   is re-keyed to the same full-row column indices (common part: c < U_P -> c, c >= U_P ->
//!   c + N_PROG; cached part: c -> U_P + c) and its canonical hash compared with the exported one;
//!   the test asserts they are equal, so the Lean data covers both variants.
//! Constraints and interactions do not depend on `log_rows` / `k` (they size traces and the
//! program only).
//!
//! Lean format (self-contained, `ZkFormal.PQ.NvAirExport.DagNode`): `v c nx` (main column `c`,
//! next row iff `nx`), `p i` (public value `i`), `k n` (constant, canonical), `add/sub/mul a b`,
//! `neg a`, `first`, `last`, `trans`; children are earlier node indices.  Interactions are
//! `(bus, count, msg)` with node indices; the count is the signed field multiplicity of the
//! backend's LogUp (`send`/`lookup_key`: +enabled; `receive`/`add_key_with_lookups`: -count);
//! `nvCountWeights` lists their `count_weight`s in the same order.
//! The SHA-256 is over the canonical text `nodes|constraints|interactions` printed below
//! (count weights not included, as in the draft).
use std::collections::BTreeMap;

use openvm_stark_backend::{
    air_builders::symbolic::{symbolic_variable::Entry, SymbolicConstraintsDag, SymbolicExpressionNode},
    StarkEngine,
};
use p3_field::PrimeField32;
use sha2::{Digest as _, Sha256};

use super::{
    circuit::NvCircuit,
    uair::{NV_WIDTH, N_PROG, U_P},
};
use crate::sha384::config::*;

/// Map (part_index, offset) to the full NvAir row column.  `program_part`: cached mains are
/// part 0 (the program, width N_PROG), common main part 1 (backend order: cached first).
fn full_col(program_part: bool, part_index: usize, idx: usize) -> usize {
    if !program_part {
        assert_eq!(part_index, 0, "unpartitioned NvAir expected");
        return idx;
    }
    match part_index {
        0 => {
            assert!(idx < N_PROG);
            U_P + idx
        }
        1 => {
            if idx < U_P {
                idx
            } else {
                idx + N_PROG
            }
        }
        _ => panic!("unexpected part {part_index}"),
    }
}

fn node_text(n: &SymbolicExpressionNode<F>, program_part: bool) -> String {
    match n {
        SymbolicExpressionNode::Variable(var) => match var.entry {
            Entry::Main { part_index, offset } => {
                let c = full_col(program_part, part_index, var.index);
                assert!(c < NV_WIDTH);
                format!("v {} {}", c, if offset == 0 { "false" } else { "true" })
            }
            Entry::Public => format!("p {}", var.index),
            e => panic!("unsupported entry {e:?}"),
        },
        SymbolicExpressionNode::Constant(c) => format!("k {}", c.as_canonical_u32()),
        SymbolicExpressionNode::Add { left_idx, right_idx, .. } => format!("add {left_idx} {right_idx}"),
        SymbolicExpressionNode::Sub { left_idx, right_idx, .. } => format!("sub {left_idx} {right_idx}"),
        SymbolicExpressionNode::Mul { left_idx, right_idx, .. } => format!("mul {left_idx} {right_idx}"),
        SymbolicExpressionNode::Neg { idx, .. } => format!("neg {idx}"),
        SymbolicExpressionNode::IsFirstRow => "first".into(),
        SymbolicExpressionNode::IsLastRow => "last".into(),
        SymbolicExpressionNode::IsTransition => "trans".into(),
    }
}

/// degree of every node (variables 1, selectors 1, constants / publics 0)
fn degrees(sc: &SymbolicConstraintsDag<F>) -> Vec<usize> {
    let mut d = vec![0usize; sc.constraints.nodes.len()];
    for (i, n) in sc.constraints.nodes.iter().enumerate() {
        d[i] = match n {
            SymbolicExpressionNode::Variable(v) => match v.entry {
                Entry::Public | Entry::Challenge => 0,
                _ => 1,
            },
            SymbolicExpressionNode::Constant(_) => 0,
            SymbolicExpressionNode::IsFirstRow | SymbolicExpressionNode::IsLastRow | SymbolicExpressionNode::IsTransition => 1,
            SymbolicExpressionNode::Add { left_idx, right_idx, .. } | SymbolicExpressionNode::Sub { left_idx, right_idx, .. } => {
                d[*left_idx].max(d[*right_idx])
            }
            SymbolicExpressionNode::Mul { left_idx, right_idx, .. } => d[*left_idx] + d[*right_idx],
            SymbolicExpressionNode::Neg { idx, .. } => d[*idx],
        };
    }
    d
}

struct Canon {
    nodes: Vec<String>,
    int_txt: Vec<String>,
    hex: String,
}

fn canon(sc: &SymbolicConstraintsDag<F>, program_part: bool) -> Canon {
    let dag = &sc.constraints;
    let nodes: Vec<String> = dag.nodes.iter().map(|n| node_text(n, program_part)).collect();
    let mut c = String::new();
    for n in &nodes {
        c.push_str(n);
        c.push('\n');
    }
    c.push('|');
    for i in &dag.constraint_idx {
        c.push_str(&format!("{i}\n"));
    }
    c.push('|');
    let mut int_txt = vec![];
    for i in &sc.interactions {
        let m: Vec<String> = i.message.iter().map(|x| x.to_string()).collect();
        let t = format!("({}, {}, [{}])", i.bus_index, i.count, m.join(", "));
        c.push_str(&t);
        c.push('\n');
        int_txt.push(t);
    }
    let h = Sha256::digest(c.as_bytes());
    Canon { nodes, int_txt, hex: h.iter().map(|b| format!("{b:02x}")).collect() }
}

fn bus_names(c: &NvCircuit) -> BTreeMap<u16, String> {
    let b = c.buses;
    let mut m = BTreeMap::new();
    let mut put = |i: u16, s: &str| {
        m.entry(i).and_modify(|e: &mut String| e.push_str(&format!("/{s}"))).or_insert_with(|| s.to_string());
    };
    put(b.alu.slot, "slot");
    put(b.alu.job, "job");
    put(b.alu.digest, "digest");
    put(b.alu.mem, "mem");
    put(b.alu.bind, "bind");
    put(b.alu.acc, "acc");
    put(b.h.ctl, "sha_ctl");
    put(b.h.k, "sha_k");
    put(b.h.lb, "sha_lb");
    put(b.h.iface, "sha_iface");
    put(b.h.word, "h_word");
    put(b.h.byte, "byte");
    put(b.tr.sample, "tr_sample");
    put(b.tr.word, "tr_word");
    put(b.tr.chain, "tr_chain");
    put(b.tr.chain_start, "chain_start");
    for (i, &x) in b.lb_extra.iter().enumerate() {
        put(x, &format!("sha_lb{}", i + 1));
    }
    m
}

#[test]
fn nv_export() {
    let mut p = crate::sha384::e2e_tests::parent_params_debug();
    p.max_constraint_degree = NvCircuit::new(3, 16, 1).layout().degree().max(6);
    let engine = Sha384CpuEngine::new(p);
    let circ = NvCircuit::new(3, 17, 1);
    let names = bus_names(&circ);
    let airs = circ.airs::<Sha384Config>();
    let (_, vk) = engine.keygen(&airs);
    // the tree variant (program part cached)
    let mut circ_t = circ.clone();
    circ_t.program_part = true;
    let airs_t = circ_t.airs::<Sha384Config>();
    let (_, vk_t) = engine.keygen(&airs_t);

    // per-AIR summary and per-bus interaction counts (which AIRs balance each NvAir bus)
    let mut bus_lines = vec![];
    let mut per_bus: BTreeMap<u16, Vec<(String, usize, Vec<usize>)>> = BTreeMap::new();
    for (a, avk) in airs.iter().zip(&vk.inner.per_air) {
        let mut cnt: BTreeMap<u16, (usize, Vec<usize>)> = BTreeMap::new();
        for i in &avk.symbolic_constraints.interactions {
            let e = cnt.entry(i.bus_index).or_default();
            e.0 += 1;
            if !e.1.contains(&i.message.len()) {
                e.1.push(i.message.len());
            }
        }
        for (bus, (n, lens)) in &cnt {
            per_bus.entry(*bus).or_default().push((a.name(), *n, lens.clone()));
        }
        let w = &avk.params.width;
        let line = format!(
            "{} common_main={} cached_mains={:?} preprocessed={:?} nodes={} constraints={} interactions={} max_deg={} pvs={} buses={:?}",
            a.name(),
            w.common_main,
            w.cached_mains,
            w.preprocessed,
            avk.symbolic_constraints.constraints.nodes.len(),
            avk.symbolic_constraints.constraints.constraint_idx.len(),
            avk.symbolic_constraints.interactions.len(),
            avk.max_constraint_degree,
            avk.params.num_public_values,
            cnt.keys().collect::<Vec<_>>()
        );
        println!("NV_EXPORT_AIR {line}");
        bus_lines.push(line);
    }
    let mut bus_table = vec![];
    for (bus, v) in &per_bus {
        let parts: Vec<String> = v.iter().map(|(a, n, l)| format!("{a} x{n} (msg len {l:?})")).collect();
        let line = format!("bus {bus} [{}]: {}", names.get(bus).cloned().unwrap_or("?".into()), parts.join("; "));
        println!("NV_EXPORT_BUS {line}");
        bus_table.push(line);
    }

    let avk = &vk.inner.per_air[0];
    assert!(avk.params.width.cached_mains.is_empty() && avk.preprocessed_data.is_none());
    assert_eq!(avk.params.width.common_main, NV_WIDTH);
    let sc = &avk.symbolic_constraints;
    let dag = &sc.constraints;
    let ints = &sc.interactions;
    let cz = canon(sc, false);
    let avk_t = &vk_t.inner.per_air[0];
    assert!(avk_t.preprocessed_data.is_none());
    assert_eq!(avk_t.params.width.cached_mains, vec![N_PROG]);
    let ct = canon(&avk_t.symbolic_constraints, true);
    println!(
        "NV_EXPORT_TREE_VARIANT common_main={} cached_mains={:?} nodes={} constraints={} interactions={} max_deg={} sha256(rekeyed)={}",
        avk_t.params.width.common_main,
        avk_t.params.width.cached_mains,
        ct.nodes.len(),
        avk_t.symbolic_constraints.constraints.constraint_idx.len(),
        avk_t.symbolic_constraints.interactions.len(),
        avk_t.max_constraint_degree,
        ct.hex
    );
    let same = ct.hex == cz.hex;
    println!("NV_EXPORT_TREE_VARIANT_SAME_AS_FINAL {same}");

    let deg = degrees(sc);
    let cmax = dag.constraint_idx.iter().map(|&i| deg[i]).max().unwrap_or(0);
    let imax = ints.iter().map(|i| deg[i.count] + i.message.iter().map(|&m| deg[m]).max().unwrap_or(0)).max().unwrap_or(0);
    let mut by_bus: BTreeMap<u16, (usize, Vec<usize>, Vec<u32>)> = BTreeMap::new();
    for i in ints {
        let e = by_bus.entry(i.bus_index).or_default();
        e.0 += 1;
        if !e.1.contains(&i.message.len()) {
            e.1.push(i.message.len());
        }
        if !e.2.contains(&i.count_weight) {
            e.2.push(i.count_weight);
        }
    }
    let mut nv_bus_lines = vec![];
    for (b, (n, l, w)) in &by_bus {
        let line = format!("bus {b} [{}]: {n} interactions, msg len {l:?}, count_weight {w:?}", names.get(b).cloned().unwrap_or("?".into()));
        println!("NV_EXPORT_NVBUS {line}");
        nv_bus_lines.push(line);
    }
    let summary = format!(
        "nodes = {}, constraints = {}, interactions = {}, width = {} (common main; preprocessed none; no after-challenge trace: LogUp-GKR), public values = {}, max constraint degree (DAG) = {}, max interaction degree (count + msg) = {}, vk max_constraint_degree = {}",
        cz.nodes.len(),
        dag.constraint_idx.len(),
        ints.len(),
        avk.params.width.common_main,
        avk.params.num_public_values,
        cmax,
        imax,
        avk.max_constraint_degree
    );
    println!("NV_EXPORT {summary} sha256={}", cz.hex);
    assert!(same, "tree variant (program_part) DAG differs from the FINAL variant after re-keying");

    let Ok(out) = std::env::var("NV_EXPORT_OUT") else { return };
    let header = std::env::var("NV_EXPORT_HEADER").unwrap_or_default();
    let mut s = String::new();
    s.push_str("/-!\n# ZkFormal.PQ.NvAirExport — GENERATED, do not edit\n\n");
    s.push_str("The pinned NvAir (table 0 of the NV circuit) as exported by\n");
    s.push_str("`research/near-compression/native/recursion/nv-export/nv_export.rs`: the verifier's\n");
    s.push_str("`SymbolicConstraintsDag` from keygen, nodes in topological order. Self-contained (core\n");
    s.push_str("Lean only); not imported by any module.\n\n");
    s.push_str(&header);
    s.push_str(&format!("\n\n* {summary}\n"));
    s.push_str(&format!("* sha256(canonical nodes|constraints|interactions) = `{}`\n", cz.hex));
    s.push_str("* exported variant: `program_part = false` (wrap / FINAL); the `program_part = true` variant\n");
    s.push_str("  (tree leaves / nodes, P0..P3 a cached part) has the identical DAG after re-keying its\n");
    s.push_str(&format!("  columns to the full row (checked by the exporter: sha256 `{}`)\n", ct.hex));
    s.push_str("* NvAir interactions per bus:\n");
    for l in &nv_bus_lines {
        s.push_str(&format!("  * `{l}`\n"));
    }
    s.push_str("* all AIRs of the circuit (keygen):\n");
    for l in &bus_lines {
        s.push_str(&format!("  * `{l}`\n"));
    }
    s.push_str("* interactions per bus over all AIRs (the tables that balance each bus):\n");
    for l in &bus_table {
        s.push_str(&format!("  * `{l}`\n"));
    }
    s.push_str("-/\n\nnamespace ZkFormal.PQ.NvAirExport\n\n");
    s.push_str("/-- A node of the backend's symbolic DAG; children are earlier node indices. -/\n");
    s.push_str("inductive DagNode where\n  | v (c : Nat) (nx : Bool)\n  | p (i : Nat)\n  | k (n : Nat)\n  | add (a b : Nat)\n  | sub (a b : Nat)\n  | mul (a b : Nat)\n  | neg (a : Nat)\n  | first\n  | last\n  | trans\n  deriving Repr, DecidableEq\n\n");
    s.push_str("open DagNode\n\n");
    const CH: usize = 256;
    let nch = cz.nodes.len().div_ceil(CH);
    for (ci, ch) in cz.nodes.chunks(CH).enumerate() {
        s.push_str(&format!("def nvNodes{ci} : List DagNode := [\n"));
        let body: Vec<String> = ch.iter().map(|n| format!("  {n}")).collect();
        s.push_str(&body.join(",\n"));
        s.push_str("]\n\n");
    }
    let parts: Vec<String> = (0..nch).map(|i| format!("nvNodes{i}")).collect();
    s.push_str(&format!("/-- All {} DAG nodes. -/\ndef nvNodes : List DagNode :=\n  {}\n\n", cz.nodes.len(), parts.join(" ++ ")));
    let cs: Vec<String> = dag.constraint_idx.iter().map(|c| c.to_string()).collect();
    s.push_str(&format!("/-- Node indices of the {} constraints. -/\ndef nvConstraintIdx : List Nat := [{}]\n\n", cs.len(), cs.join(", ")));
    s.push_str(&format!(
        "/-- The {} interactions `(bus, count, message)` as node indices. -/\ndef nvInteractionIdx : List (Nat × Nat × List Nat) := [\n  {}]\n\n",
        ints.len(),
        cz.int_txt.join(",\n  ")
    ));
    let ws: Vec<String> = ints.iter().map(|i| i.count_weight.to_string()).collect();
    s.push_str(&format!("/-- `count_weight` of each interaction (same order). -/\ndef nvCountWeights : List Nat := [{}]\n\n", ws.join(", ")));
    s.push_str(&format!(
        "def nvNumNodes : Nat := {}\ndef nvWidth : Nat := {}\ndef nvNumPub : Nat := {}\n\n",
        cz.nodes.len(),
        avk.params.width.common_main,
        avk.params.num_public_values
    ));
    s.push_str("end ZkFormal.PQ.NvAirExport\n");
    std::fs::write(&out, s).unwrap();
    println!("NV_EXPORT wrote {out}");
}
