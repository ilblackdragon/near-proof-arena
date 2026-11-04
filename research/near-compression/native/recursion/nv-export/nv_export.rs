//! [lane E, M11e] Export the pinned NvAir constraint DAG and interactions as Lean data.
//!
//! Installed as `crates/recursion/src/nv/nv_export.rs` by `nv-export/setup.sh` (a private copy
//! of the pq-agg tree; the shared tree is never modified).  Run:
//!
//!   NV_EXPORT_OUT=<file.lean> cargo test --release -p openvm-recursion-circuit nv_export -- --nocapture
//!
//! What is exported is exactly the object the verifier consumes: `vk.inner.per_air[0]
//! .symbolic_constraints` (the `SymbolicConstraintsDag` after the backend's DAG builder, i.e. after
//! its structural dedup and algebraic simplifications), from keygen of the aggregation node's
//! circuit `NvCircuit::new(3, 17, 1)` (`agg_tests::agg_shape`; `program_part = false`, the agg
//! node default, so P0..P3 are common-main columns 6..9).  Constraints and interactions do not
//! depend on `log_rows` / `k` (they size traces and the program only).
//!
//! Lean format (`ZkFormal.PQ.NvAir.DagNode`): `v c nx` (main column `c`, next row iff `nx`),
//! `p i` (public value `i`), `k n` (constant, canonical), `add/sub/mul a b`, `neg a`, `first`,
//! `last`, `trans`; children are earlier node indices.  Interactions are `(bus, count, msg)` with
//! node indices; the count is the signed field multiplicity of the backend's LogUp
//! (`send`/`lookup_key`: +enabled; `receive`/`add_key_with_lookups`: -count).
//! The SHA-256 is over the canonical text `nodes|constraints|interactions` printed below.
use openvm_stark_backend::{
    air_builders::symbolic::{symbolic_variable::Entry, SymbolicExpressionNode},
    StarkEngine,
};
use p3_field::PrimeField32;
use sha2::{Digest as _, Sha256};

use super::circuit::NvCircuit;
use crate::sha384::config::*;

fn node_text(n: &SymbolicExpressionNode<F>) -> String {
    match n {
        SymbolicExpressionNode::Variable(var) => match var.entry {
            Entry::Main { part_index, offset } => {
                assert_eq!(part_index, 0, "unpartitioned NvAir expected");
                format!("v {} {}", var.index, if offset == 0 { "false" } else { "true" })
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

#[test]
fn nv_export() {
    let circ = NvCircuit::new(3, 17, 1);
    let airs = circ.airs::<Sha384Config>();
    let mut p = crate::sha384::e2e_tests::parent_params_debug();
    p.max_constraint_degree = NvCircuit::new(3, 16, 1).layout().degree().max(6);
    let engine = Sha384CpuEngine::new(p);
    let (_, vk) = engine.keygen(&airs);

    // bus sets of every AIR (the mem bus must be NvAir-only for the Lean model's balance premise)
    let mut bus_lines = vec![];
    for (a, avk) in airs.iter().zip(&vk.inner.per_air) {
        let mut bs: Vec<u16> = avk.symbolic_constraints.interactions.iter().map(|i| i.bus_index).collect();
        bs.sort();
        bs.dedup();
        let line = format!(
            "{} width={} constraints={} interactions={} buses={:?} pvs={}",
            a.name(),
            avk.params.width.common_main,
            avk.symbolic_constraints.constraints.constraint_idx.len(),
            avk.symbolic_constraints.interactions.len(),
            bs,
            avk.params.num_public_values
        );
        println!("NV_EXPORT_AIR {line}");
        bus_lines.push(line);
    }

    let avk = &vk.inner.per_air[0];
    assert!(avk.params.width.cached_mains.is_empty() && avk.preprocessed_data.is_none());
    let dag = &avk.symbolic_constraints.constraints;
    let ints = &avk.symbolic_constraints.interactions;
    let nodes: Vec<String> = dag.nodes.iter().map(node_text).collect();
    let mut canon = String::new();
    for n in &nodes {
        canon.push_str(n);
        canon.push('\n');
    }
    canon.push('|');
    for c in &dag.constraint_idx {
        canon.push_str(&format!("{c}\n"));
    }
    canon.push('|');
    let mut int_txt = vec![];
    for i in ints {
        let m: Vec<String> = i.message.iter().map(|x| x.to_string()).collect();
        let t = format!("({}, {}, [{}])", i.bus_index, i.count, m.join(", "));
        canon.push_str(&t);
        canon.push('\n');
        int_txt.push(t);
    }
    let h = Sha256::digest(canon.as_bytes());
    let hex: String = h.iter().map(|b| format!("{b:02x}")).collect();
    println!(
        "NV_EXPORT nodes={} constraints={} interactions={} width={} pvs={} sha256={hex}",
        nodes.len(),
        dag.constraint_idx.len(),
        ints.len(),
        avk.params.width.common_main,
        avk.params.num_public_values
    );

    let Ok(out) = std::env::var("NV_EXPORT_OUT") else { return };
    let header = std::env::var("NV_EXPORT_HEADER").unwrap_or_default();
    let mut s = String::new();
    s.push_str("import ZkFormal.PQ.NvAirDag\n\n");
    s.push_str("/-!\n# ZkFormal.PQ.NvAirExport — GENERATED, do not edit\n\n");
    s.push_str("The pinned NvAir (table 0 of the aggregation node circuit) as exported by\n");
    s.push_str("`research/near-compression/native/recursion/nv-export/nv_export.rs`: the verifier's\n");
    s.push_str("`SymbolicConstraintsDag` from keygen, nodes in topological order.\n\n");
    s.push_str(&header);
    s.push_str(&format!(
        "\n* nodes = {}, constraints = {}, interactions = {}, width = {}, public values = {}\n",
        nodes.len(),
        dag.constraint_idx.len(),
        ints.len(),
        avk.params.width.common_main,
        avk.params.num_public_values
    ));
    s.push_str(&format!("* sha256(canonical nodes|constraints|interactions) = `{hex}`\n"));
    s.push_str("* all AIRs of the circuit (keygen):\n");
    for l in &bus_lines {
        s.push_str(&format!("  * `{l}`\n"));
    }
    s.push_str("-/\n\nnamespace ZkFormal.PQ.NvAir\n\nopen DagNode\n\n");
    const CH: usize = 256;
    let nch = nodes.len().div_ceil(CH);
    for (ci, ch) in nodes.chunks(CH).enumerate() {
        s.push_str(&format!("def nvNodes{ci} : List DagNode := [\n"));
        let body: Vec<String> = ch.iter().map(|n| format!("  {n}")).collect();
        s.push_str(&body.join(",\n"));
        s.push_str("]\n\n");
    }
    let parts: Vec<String> = (0..nch).map(|i| format!("nvNodes{i}")).collect();
    s.push_str(&format!("/-- All {} DAG nodes. -/\ndef nvNodes : List DagNode :=\n  {}\n\n", nodes.len(), parts.join(" ++ ")));
    let cs: Vec<String> = dag.constraint_idx.iter().map(|c| c.to_string()).collect();
    s.push_str(&format!("/-- Node indices of the {} constraints. -/\ndef nvConstraintIdx : List Nat := [{}]\n\n", cs.len(), cs.join(", ")));
    s.push_str(&format!(
        "/-- The {} interactions `(bus, count, message)` as node indices. -/\ndef nvInteractionIdx : List (Nat × Nat × List Nat) := [\n  {}]\n\n",
        ints.len(),
        int_txt.join(",\n  ")
    ));
    s.push_str(&format!("def nvNumNodes : Nat := {}\ndef nvWidth : Nat := {}\ndef nvNumPub : Nat := {}\n\n", nodes.len(), avk.params.width.common_main, avk.params.num_public_values));
    s.push_str("end ZkFormal.PQ.NvAir\n");
    std::fs::write(&out, s).unwrap();
    println!("NV_EXPORT wrote {out}");
}
