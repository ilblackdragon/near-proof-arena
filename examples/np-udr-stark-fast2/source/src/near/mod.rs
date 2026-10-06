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
pub mod genmax;
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
///
/// `Err` for malformed or out-of-domain inputs: the claim is derived first by
/// the reexec engine (`deriveClaim`, which rejects everything outside
/// `ClaimDomain` / `NearRelation`), then [`domain_guard`] re-checks the ranges
/// the trace generators' arithmetic relies on.
pub fn load(request: &[u8], witness: &[u8]) -> Result<(spec::Claim, ext::Ext), String> {
    let inp = spec::load_inputs(request, witness)?;
    let e = ext::ext_of(&inp.claim, &inp.witness);
    domain_guard(&inp.claim, &e)?;
    Ok((inp.claim, e))
}

/// The value ranges the generators assume (all implied by `deriveClaim`
/// succeeding; checked again so that no generator arithmetic can overflow):
/// per receipt `G·burnPrice`, `G·surplus`, the running `tokens_burnt`, and per
/// touched account the running `amount` (< u128::MAX) and `amount + locked`.
pub fn domain_guard(c: &spec::Claim, e: &ext::Ext) -> Result<(), String> {
    use spec::params::{G, U128_MAX};
    let bgp = c.block_gas_price;
    let mut tok: u128 = 0;
    let mut amt: std::collections::HashMap<usize, u128> = std::collections::HashMap::new();
    for (r, rc) in e.rs.iter().enumerate() {
        let bad = |w: &str| format!("out of domain: receipt {r}: {w}");
        let p = rc.gas_price.min(bgp);
        let burnt = G.checked_mul(p).ok_or_else(|| bad("burnt overflow"))?;
        G.checked_mul(rc.gas_price - p).ok_or_else(|| bad("surplus overflow"))?;
        tok = tok.checked_add(burnt).ok_or_else(|| bad("tokens overflow"))?;
        let k = e.slot(r);
        let a0 = e.acc0(k);
        let a = amt.entry(k).or_insert(a0.amount);
        *a = a.checked_add(rc.deposit).filter(|&x| x < U128_MAX).ok_or_else(|| bad("amount overflow"))?;
        a.checked_add(a0.locked).ok_or_else(|| bad("amount + locked overflow"))?;
    }
    Ok(())
}

/// `request.bin`, `witness.bin` → (`claim.bin`, `nearAir`, honest traces).
///
/// Never panics: malformed / out-of-domain inputs, traces taller than a
/// table's `2^maxLog`, and (backstop) any panic inside the generators all
/// become `Err`. Deep (in-domain) tries recurse deeply: call it on a thread
/// with a large stack ([`with_big_stack`]).
pub fn prepare(request: &[u8], witness: &[u8]) -> Result<(Vec<u8>, Air, Vec<RowMajorMatrix<F>>), String> {
    catch_panic(|| prepare_unguarded(request, witness))
}

/// [`prepare`] without the `catch_unwind` backstop (tests use it to find panics).
pub fn prepare_unguarded(request: &[u8], witness: &[u8]) -> Result<(Vec<u8>, Air, Vec<RowMajorMatrix<F>>), String> {
    let (c, e) = load(request, witness)?;
    let b = trace::bundle(&c, &e);
    if !b.errors.is_empty() {
        return Err(format!("walk errors: {:?}", b.errors));
    }
    let air = near_air();
    let traces = trace::bundle_traces(&b);
    check_heights(&air, &traces)?;
    Ok((c.encode(), air, traces))
}

/// [`prepare`] with compact traces ([`trace::render_cols`]; low peak memory).
pub fn prepare_cols(request: &[u8], witness: &[u8]) -> Result<(Vec<u8>, Air, Vec<crate::cols::TraceCols>), String> {
    catch_panic(|| {
        let (c, e) = load(request, witness)?;
        let (traces, errors) = trace::render_cols_checked(&c, &e);
        if !errors.is_empty() {
            return Err(format!("walk errors: {errors:?}"));
        }
        let air = near_air();
        if traces.len() != air.tables.len() {
            return Err(format!("{} traces for {} tables", traces.len(), air.tables.len()));
        }
        for (k, (t, m)) in air.tables.iter().zip(&traces).enumerate() {
            if m.log_h > t.max_log {
                return Err(format!("trace {k}: 2^{} rows > 2^{} (maxLog)", m.log_h, t.max_log));
            }
        }
        Ok((c.encode(), air, traces))
    })
}

/// Every trace fits its table: `height ≤ 2^maxLog`.
pub fn check_heights(air: &Air, traces: &[RowMajorMatrix<F>]) -> Result<(), String> {
    use p3_matrix::Matrix;
    if traces.len() != air.tables.len() {
        return Err(format!("{} traces for {} tables", traces.len(), air.tables.len()));
    }
    for (k, (t, m)) in air.tables.iter().zip(traces).enumerate() {
        if m.height() > 1usize << t.max_log {
            return Err(format!("trace {k}: {} rows > 2^{} (maxLog)", m.height(), t.max_log));
        }
    }
    Ok(())
}

/// `f()`, with a panic turned into `Err("internal error: …")`.
pub fn catch_panic<T>(f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(p) => {
            let m = p
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| p.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "panic".into());
            Err(format!("internal error: {m}"))
        }
    }
}

/// Stack for [`with_big_stack`]: in-domain tries may have revealed paths of
/// up to ~70k nodes (chains of empty-key extensions), and the reexec engine,
/// `prune`/`recs`/`sers` recurse along them. Reserved, not committed.
pub const BIG_STACK: usize = 1 << 30;

/// Run `f` on a fresh thread with a [`BIG_STACK`] stack; a panic → `Err`.
pub fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> Result<T, String> + Send + 'static) -> Result<T, String> {
    let h = std::thread::Builder::new()
        .name("npudr-main".into())
        .stack_size(BIG_STACK)
        .spawn(move || catch_panic(f))
        .map_err(|e| format!("spawn: {e}"))?;
    h.join().unwrap_or_else(|_| Err("internal error: worker thread panicked".into()))
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
