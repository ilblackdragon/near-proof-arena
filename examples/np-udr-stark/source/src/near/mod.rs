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
//! * [`reexec`] — copied reexec-witness decoder/engine.
pub mod ext;
pub mod ids;
pub mod info;
pub mod rcpt;
pub mod reexec;
pub mod sim;
pub mod spec;
