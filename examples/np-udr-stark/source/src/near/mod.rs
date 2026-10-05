//! NEAR honest-trace generator for `nearAir` (lane L8, port of lane L6's
//! `ZkFormal/Near/Render/*.lean`, cell for cell).
//!
//! # Pipeline
//!
//! ```text
//! request.bin, witness.bin
//!   └─ spec::load_inputs ──► Inputs { claim: Claim, witness: Witness }
//!        (NearSpec.Codec.decodeRequest/decodeWitness/buildWitness; claim from the
//!         reexec engine = Codec.deriveClaim, bytes = claim.encode())
//!   └─ ext::ext_of(&claim, &witness) ──► Ext          (Spec/Prune.lean `extOf`)
//!   └─ info::mk_info(&claim, &ext)   ──► Info         (Render/Common.lean `mkInfo`)
//!   └─ table generators (Render/{Node,Walk,Rcpt,Acct,Mrk,Sort}.lean) + messages
//! ```
//!
//! # Modules / API
//!
//! * [`spec`] — owned mirrors of NearSpec: [`spec::Receipt`] (fields
//!   `predecessor_id, receiver_id, receipt_id, signer_id, signer_pk {tag, data},
//!   gas_price, deposit`), [`spec::Account`] (`encode`/`decode`),
//!   [`spec::Outcome`] (`partial_encode`, `leaf`), `gas_refund_receipt`,
//!   `encode_receipts`, `receipts_commitment`, `refunds_commitment`,
//!   `outcome_root`, `merkle_root`, `account_key_path`, `nibbles`, `hex_prefix`,
//!   byte encoders `le_n/u16b/u32b/u64b/u128b/borsh_bytes`, the partial trie
//!   [`spec::PTrie`] and [`spec::load_inputs`].  `Claim` = the reexec claim
//!   (`encode()` = `claim.bin`).
//! * [`ext`] — records `NodeRec`/`VSlot`/`Kid`, `ser`, `tree_of`/`trie_of`,
//!   [`ext::Ext`] with `vals0, slot, acc0, rc, amt_at, vals_at, tok_at,
//!   refund_of, outcome_of, outcomes, refunds`; `burn_price, burnt_of,
//!   surplus_of`; `prune, recs, vl, slot_idx, ext_of`.
//! * [`info`] — `Row = Vec<u32>`, `Msg {id, bytes}`, `clog2, log_of, pad_to,
//!   zero_row, mk_tab, le_bytes, inv_p, sha_n`; [`info::Info`] (`pre, post,
//!   depth, res, vpre, vpost, touched` + `pre_dig, post_dig, node_at, n_rcpt,
//!   pub_nats`) and [`info::mk_info`]; walks `key_syms, step_of, walk_of,
//!   walks_of, walk_errors, edge_uses, final_of, WStep`; `tprev_of, tlast_of`.
//! * [`ids`] — `K_*`, `msg_id`, `B_*`, `SYM_*`, `PV_*`, `T_*` (Ids.lean).
//! * [`sim`] — RcptSim byte strings: `peo_bytes, leaf_bytes, has_refund,
//!   rid_bytes, rc_bytes, rf_bytes, rcpt_msgs_sim`.
//! * [`rcpt`] — `rcpt_rows_all(&Info) -> Vec<Vec<u32>>`,
//!   `rcpt_msgs(&Info) -> Vec<Msg>` (owned by the rcpt sub-agent).
//! * [`node`], [`small`] (walk, acct, sort, mrk) — table generators
//!   (`*_rows_all`, `*_msgs`); [`trace`] — `bundle`, `render` (7 traces in
//!   `nearAir` order), `bundle_traces`, `sha_matrix`.
//! * [`reexec`] — copied reexec-witness decoder/engine.
//!
//! Top level: [`near_air`] (the committed Lean export `near-air.json` =
//! `Air.exportJson ZkFormal.Near.nearAir`), [`prepare`] (inputs → claim.bin,
//! AIR, traces), [`dump`] (`np-near-render-v1` cross-check format, see
//! `conformance/NearRender.lean`).
pub mod ext;
pub mod ids;
pub mod info;
pub mod node;
pub mod rcpt;
pub mod reexec;
pub mod sim;
pub mod small;
pub mod spec;
pub mod trace;

use p3_matrix::dense::RowMajorMatrix;

use crate::air::Air;
use crate::field::F;

/// `Air.exportJson ZkFormal.Near.nearAir` (committed, `np-lean-export near`).
pub const NEAR_AIR_JSON: &str = include_str!("../../near-air.json");

/// The NEAR AIR (`ZkFormal.Near.nearAir`).
pub fn near_air() -> Air { Air::from_json(NEAR_AIR_JSON).expect("near-air.json") }

/// Public inputs of a claim: its bytes as field elements (`publicOf`).
pub fn public_of(claim_bin: &[u8]) -> Vec<F> { claim_bin.iter().map(|&b| F::new(b as u32)).collect() }

/// Records of the inputs: `(claim, ext_of claim witness)`.
pub fn load(request: &[u8], witness: &[u8]) -> Result<(spec::Claim, ext::Ext), String> {
    let inp = spec::load_inputs(request, witness)?;
    let e = ext::ext_of(&inp.claim, &inp.witness);
    Ok((inp.claim, e))
}

/// `request.bin`, `witness.bin` → (`claim.bin`, `nearAir`, honest traces).
pub fn prepare(request: &[u8], witness: &[u8]) -> Result<(Vec<u8>, Air, Vec<RowMajorMatrix<F>>), String> {
    let (c, e) = load(request, witness)?;
    let b = trace::bundle(&c, &e);
    if !b.errors.is_empty() {
        return Err(format!("walk errors: {:?}", b.errors));
    }
    Ok((c.encode(), near_air(), trace::bundle_traces(&b)))
}

/// Dump a bundle in the `np-near-render-v1` format (`conformance/NearRender.lean`).
pub fn dump(claim_bin: &[u8], b: &trace::Bundle) -> Vec<u8> {
    let mut o = vec![];
    let u = |o: &mut Vec<u8>, x: usize| o.extend_from_slice(&(x as u32).to_le_bytes());
    u(&mut o, claim_bin.len());
    o.extend_from_slice(claim_bin);
    u(&mut o, b.msgs.len());
    for m in &b.msgs {
        u(&mut o, m.id as usize);
        u(&mut o, m.bytes.len());
        o.extend_from_slice(&m.bytes);
    }
    let parts = b.parts();
    u(&mut o, parts.len());
    for (_, w, rows) in parts {
        u(&mut o, w);
        u(&mut o, rows.len());
        for r in rows.iter() {
            for c in 0..w {
                u(&mut o, r.get(c).copied().unwrap_or(0) as usize);
            }
        }
    }
    o
}
