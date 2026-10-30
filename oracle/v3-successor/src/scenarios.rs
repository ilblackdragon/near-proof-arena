//! Opt-in successor scenarios beyond `global-cache` (README.md):
//!
//! * `yield` — `promise_yield_create` / `promise_yield_resume` (and the `_with_id` variants) on
//!   dedicated accounts: resume in the same receipt, the same chunk and a later chunk, timeout,
//!   duplicate resumes, wrong/malformed data ids, payload-size limit, cross-shard triggers and
//!   cross-shard receipts emitted by yield callbacks, a resume racing the timeout. Baseline
//!   traffic keeps running.
//! * `storage-limits` — a quiet chain (no baseline traffic, no crafted injections) running
//!   nearcore-driven binary searches for the exact per-receipt storage-proof limit
//!   (`per_receipt_storage_proof_size_limit`, shard 0) and the chunk soft limit
//!   (`main_storage_proof_size_soft_limit`, `check_proof_size_limit_exceed`, shard 1), followed by
//!   below/at/above probes and boundary variants; fixed misc cases on shards 2 and 3.
//! * `fuel-stress` — a quiet chain (W02) running Wasm workloads that maximise interpreter steps
//!   per unit of gas or non-metered work per step: the cheapest instruction burning the full
//!   300 Tgas, zero-fee control-flow loops (`block`/`end` chains up to `max_blocks_per_function`),
//!   recursion to the stack limit, maximal memory with bulk fills/copies, and long loops of host
//!   calls. Three 300 Tgas calls share one chunk (900 Tgas of the 1 Pgas chunk limit).
//!
//! * `gate-b-caps` — a quiet chain for the W02 Gate-B caps: chunks whose state witness is just
//!   below / just above / well above the former 8 MiB `w.size` bound (large transactions in two
//!   consecutive chunks plus a 3.9 MB read), chunks whose function-call gas is below / above the
//!   former 1 Pgas `e.g_alpha` bound (two 900 Tgas `memory.fill` burners in one chunk), and a call
//!   whose loop executes about 1,000 zero-fee `block`/`end` instructions per charged one (the
//!   evaluator-fuel bound).
//!
//! * `eval-loops` — a quiet chain (W02/W16) with the label-keeping loop shapes the Lean label memo
//!   targets, each burning 300 Tgas (and 3 Tgas, for the single-stepping checker): push-then-pop
//!   across a charged group, a `br_if` back-edge, a `br_table` back-edge, and a shallow `br_if`
//!   loop under 4,998 enclosing blocks.
//! * `code-response` — a quiet chain (W02 size limits) with 18 genesis contracts on shard 0: 16 of
//!   4,194,000 B and two small ones whose sizes put the chunk's accessed pre-state code, as one
//!   borsh `Vec<CodeBytes>` (`4 + Σ (4 + |code|)`), exactly at 64 MiB and one byte over
//!   (`MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE`, `contract_distribution.rs:371-373`). Each
//!   chunk calls 17 of them (one transaction each, signer = receiver, so all execute in the
//!   chunk that includes them); a control chunk calls 9.
//!
//! * `removal-soft` — a quiet chain (W12 O4 ground truth) where ContractData removals alone push
//!   the recorder's proof-size upper bound (`recorded + 2000 · removals`) past the 4,000,000 B
//!   chunk soft limit, while the witness's own values stay below it: VM `storage_remove` (first-time
//!   deletions and repeated delete+reinsert of the same keys) and `DeleteAccount` (an account at the
//!   10,000 B deletion cap next to a 3.7 MB read, and the literal > 2,000-key account, which
//!   nearcore refuses with `DeleteAccountWithLargeState`). Each probe chunk also carries an incoming
//!   transfer and sometimes a local victim receipt, which nearcore postpones once the soft limit is
//!   crossed.
//!
//! The searches use only nearcore's own outcomes (success/failure of the probe receipt, the
//! execution height of a receipt that follows it in the same chunk). The probe's only knob is the
//! length of one value written in an earlier chunk, so the trie structure is unchanged between
//! probes. `finish` writes `scenario-<chain>.json` with every probe and its observed outcome.

use crate::chaingen::Setup;
use crate::d2gen::World;
use near_crypto::InMemorySigner;
use near_primitives::account::{AccessKey, AccountContract};
use near_primitives::action::{Action, DeployContractAction, FunctionCallAction};
use near_primitives::hash::CryptoHash;
use near_primitives::state_record::StateRecord;
use near_primitives::transaction::{ExecutionStatus, SignedTransaction};
use near_primitives::types::{AccountId, Balance, Gas};
use near_primitives_core::account::Account;
use serde_json::json;
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scenario {
    GlobalCache,
    Yield,
    StorageLimits,
    FuelStress,
    EvalTime,
    GateBCaps,
    EvalLoops,
    CodeResponse,
    RemovalSoft,
}

pub fn scenario() -> Option<Scenario> {
    // `crate::d3gen::scenario` is the single parser of `NEAR_SUCCESSOR_SCENARIO`; the scenarios
    // of other modules (curve-hosts, keys) are not this module's.
    match crate::d3gen::scenario() {
        Some(crate::d3gen::Scenario::GlobalCache) => Some(Scenario::GlobalCache),
        Some(crate::d3gen::Scenario::Yield) => Some(Scenario::Yield),
        Some(crate::d3gen::Scenario::StorageLimits) => Some(Scenario::StorageLimits),
        Some(crate::d3gen::Scenario::FuelStress) => Some(Scenario::FuelStress),
        Some(crate::d3gen::Scenario::EvalTime) => Some(Scenario::EvalTime),
        Some(crate::d3gen::Scenario::GateBCaps) => Some(Scenario::GateBCaps),
        Some(crate::d3gen::Scenario::EvalLoops) => Some(Scenario::EvalLoops),
        Some(crate::d3gen::Scenario::CodeResponse) => Some(Scenario::CodeResponse),
        Some(crate::d3gen::Scenario::RemovalSoft) => Some(Scenario::RemovalSoft),
        _ => None,
    }
}

/// Quiet scenarios suppress baseline D2/D3 traffic and crafted injections.
pub fn quiet() -> bool {
    matches!(scenario(),
        Some(Scenario::StorageLimits | Scenario::FuelStress | Scenario::EvalTime | Scenario::GateBCaps
             | Scenario::EvalLoops | Scenario::CodeResponse | Scenario::RemovalSoft))
        // `runtime-errors` (src/xfam.rs): only its own transactions, so every case is about them
        || crate::xfam::kind() == Some(crate::xfam::Kind::RuntimeErrors)
}

fn acct(s: &str) -> AccountId {
    s.parse().unwrap()
}

// ---------------------------------------------------------------------------------------------
// contracts
// ---------------------------------------------------------------------------------------------

/// Yield contract. Input is loaded at 16384; byte 0 of the input is the slot.
///   create [slot]                  yield (callback `cb`, args [slot], 20 Tgas); d<slot> := data id
///   create_ret [slot]              create + promise_return(yield)
///   create_fail [slot]             create, then panic (rollback)
///   create_resume [slot] payload   create + resume in one call
///   resume [slot] payload          resume d<slot>; r<slot> := result (2: no stored data id)
///   resume2 [slot] payload         resume twice in one call; r<slot> := both results
///   resume_raw [n] id(n) payload   resume with a raw data id of length n
///   createid [slot] yid(32)        promise_yield_create_with_id; i<slot> := result (u64)
///   resumeid [slot] yid(32) payload promise_yield_resume_with_yield_id; r<slot> := result
///   cb [slot]                      c<slot> := [promise_result status] ++ payload; slot & 0x80:
///                                  promise_create(s2ynote.note, that value); slot & 0x40: panic
///   note payload                   n\0 := payload
pub const YIELD_WAT: &str = r#"(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "read_register" (func $rr (param i64 i64)))
  (import "env" "register_len" (func $rl (param i64) (result i64)))
  (import "env" "storage_write" (func $sw (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_read" (func $sr (param i64 i64 i64) (result i64)))
  (import "env" "value_return" (func $vr (param i64 i64)))
  (import "env" "panic" (func $panic))
  (import "env" "promise_yield_create" (func $pyc (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_yield_resume" (func $pyr (param i64 i64 i64 i64) (result i32)))
  (import "env" "promise_yield_create_with_id" (func $pyci (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_yield_resume_with_yield_id" (func $pyri (param i64 i64 i64 i64) (result i32)))
  (import "env" "promise_result" (func $pres (param i64 i64) (result i64)))
  (import "env" "promise_results_count" (func $prc (result i64)))
  (import "env" "promise_create" (func $pc (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_return" (func $pret (param i64)))
  (memory 1)
  (data (i32.const 1024) "cb")
  (data (i32.const 1040) "note")
  (data (i32.const 1056) "s2ynote")
  (global $len (mut i64) (i64.const 0))
  (func $load
    (call $input (i64.const 0))
    (global.set $len (call $rl (i64.const 0)))
    (call $rr (i64.const 0) (i64.const 16384)))
  (func $key (param $tag i32)
    (i32.store8 (i32.const 1200) (local.get $tag))
    (i32.store8 (i32.const 1201) (i32.load8_u (i32.const 16384))))
  (func $create (result i64) (local $p i64)
    (local.set $p (call $pyc (i64.const 2) (i64.const 1024) (i64.const 1) (i64.const 16384)
                             (i64.const 20000000000000) (i64.const 0) (i64.const 1)))
    (call $rr (i64.const 1) (i64.const 4096))
    (call $key (i32.const 100))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 32) (i64.const 4096) (i64.const 2)))
    (local.get $p))
  (func $resume (param $off i32)
    (call $key (i32.const 100))
    (if (i64.eqz (call $sr (i64.const 2) (i64.const 1200) (i64.const 1)))
      (then (i32.store8 (i32.add (i32.const 3000) (local.get $off)) (i32.const 2)) (return)))
    (call $rr (i64.const 1) (i64.const 4096))
    (i32.store8 (i32.add (i32.const 3000) (local.get $off))
      (call $pyr (i64.const 32) (i64.const 4096) (i64.sub (global.get $len) (i64.const 1)) (i64.const 16385))))
  (func $store_result (param $n i64)
    (call $key (i32.const 114))
    (drop (call $sw (i64.const 2) (i64.const 1200) (local.get $n) (i64.const 3000) (i64.const 2)))
    (call $vr (local.get $n) (i64.const 3000)))
  (func (export "create") (call $load) (drop (call $create)) (call $vr (i64.const 32) (i64.const 4096)))
  (func (export "create_ret") (call $load) (call $pret (call $create)))
  (func (export "create_fail") (call $load) (drop (call $create)) (call $panic))
  (func (export "create_resume") (call $load) (drop (call $create)) (call $resume (i32.const 0)) (call $store_result (i64.const 1)))
  (func (export "resume") (call $load) (call $resume (i32.const 0)) (call $store_result (i64.const 1)))
  (func (export "resume2") (call $load) (call $resume (i32.const 0)) (call $resume (i32.const 1)) (call $store_result (i64.const 2)))
  (func (export "resume_raw") (local $n i64)
    (call $load)
    (local.set $n (i64.extend_i32_u (i32.load8_u (i32.const 16384))))
    (i32.store8 (i32.const 3000)
      (call $pyr (local.get $n) (i64.const 16385)
                 (i64.sub (global.get $len) (i64.add (local.get $n) (i64.const 1)))
                 (i64.add (local.get $n) (i64.const 16385))))
    (call $vr (i64.const 1) (i64.const 3000)))
  (func (export "createid")
    (call $load)
    (i64.store (i32.const 3000)
      (call $pyci (i64.const 2) (i64.const 1024) (i64.const 1) (i64.const 16384) (i64.const 1100)
                  (i64.const 20000000000000) (i64.const 0) (i64.const 32) (i64.const 16385)))
    (call $key (i32.const 105))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 8) (i64.const 3000) (i64.const 2)))
    (call $vr (i64.const 8) (i64.const 3000)))
  (func (export "resumeid")
    (call $load)
    (i32.store8 (i32.const 3000)
      (call $pyri (i64.const 32) (i64.const 16385) (i64.sub (global.get $len) (i64.const 33)) (i64.const 16417)))
    (call $store_result (i64.const 1)))
  (func (export "cb") (local $st i64) (local $pl i64)
    (call $load)
    (drop (call $prc))
    (local.set $st (call $pres (i64.const 0) (i64.const 1)))
    (i32.store8 (i32.const 3000) (i32.wrap_i64 (local.get $st)))
    (if (i64.eq (local.get $st) (i64.const 1))
      (then (local.set $pl (call $rl (i64.const 1))) (call $rr (i64.const 1) (i64.const 3001))))
    (call $key (i32.const 99))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.add (local.get $pl) (i64.const 1)) (i64.const 3000) (i64.const 2)))
    (if (i32.and (i32.load8_u (i32.const 16384)) (i32.const 128))
      (then (drop (call $pc (i64.const 7) (i64.const 1056) (i64.const 4) (i64.const 1040)
                            (i64.add (local.get $pl) (i64.const 1)) (i64.const 3000) (i64.const 1100)
                            (i64.const 5000000000000)))))
    (if (i32.and (i32.load8_u (i32.const 16384)) (i32.const 64)) (then (call $panic)))
    (call $vr (i64.add (local.get $pl) (i64.const 1)) (i64.const 3000)))
  (func (export "note")
    (call $load)
    (i32.store8 (i32.const 1200) (i32.const 110))
    (i32.store8 (i32.const 1201) (i32.const 0))
    (drop (call $sw (i64.const 2) (i64.const 1200) (global.get $len) (i64.const 16384) (i64.const 2))))
)"#;

/// Storage program contract. `run` interprets its input:
///   'R' klen key            storage_read
///   'D' klen key            storage_remove
///   'H' klen key            storage_has_key
///   'W' klen key fill len32 storage_write of `len` bytes equal to `fill` (built at 65536)
///   'P'                     panic
/// `LARGE_PAD` bytes of a data segment at 32 MiB make the large-code variant.
const SLIM_WAT_HEAD: &str = r#"(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "read_register" (func $rr (param i64 i64)))
  (import "env" "register_len" (func $rl (param i64) (result i64)))
  (import "env" "storage_write" (func $sw (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_read" (func $sr (param i64 i64 i64) (result i64)))
  (import "env" "storage_remove" (func $srm (param i64 i64 i64) (result i64)))
  (import "env" "storage_has_key" (func $shk (param i64 i64) (result i64)))
  (import "env" "panic" (func $panic))
  (memory 1)
  (func (export "run") (local $pc i32) (local $len i32) (local $op i32) (local $kl i32) (local $kp i32)
                       (local $vl i32) (local $i i32) (local $pat i64)
    (call $input (i64.const 0))
    (local.set $len (i32.wrap_i64 (call $rl (i64.const 0))))
    (call $rr (i64.const 0) (i64.const 0))
    (block $done (loop $next
      (br_if $done (i32.ge_u (local.get $pc) (local.get $len)))
      (local.set $op (i32.load8_u (local.get $pc)))
      (if (i32.eq (local.get $op) (i32.const 80)) (then (call $panic)))
      (local.set $kl (i32.load8_u (i32.add (local.get $pc) (i32.const 1))))
      (local.set $kp (i32.add (local.get $pc) (i32.const 2)))
      (local.set $pc (i32.add (local.get $kp) (local.get $kl)))
      (if (i32.eq (local.get $op) (i32.const 82)) (then
        (drop (call $sr (i64.extend_i32_u (local.get $kl)) (i64.extend_i32_u (local.get $kp)) (i64.const 1)))))
      (if (i32.eq (local.get $op) (i32.const 68)) (then
        (drop (call $srm (i64.extend_i32_u (local.get $kl)) (i64.extend_i32_u (local.get $kp)) (i64.const 1)))))
      (if (i32.eq (local.get $op) (i32.const 72)) (then
        (drop (call $shk (i64.extend_i32_u (local.get $kl)) (i64.extend_i32_u (local.get $kp))))))
      (if (i32.eq (local.get $op) (i32.const 87)) (then
        (local.set $pat (i64.mul (i64.extend_i32_u (i32.load8_u (local.get $pc))) (i64.const 0x0101010101010101)))
        (local.set $vl (i32.load (i32.add (local.get $pc) (i32.const 1))))
        (local.set $pc (i32.add (local.get $pc) (i32.const 5)))
        (local.set $i (i32.const 0))
        (block $f (loop $fl
          (br_if $f (i32.ge_u (local.get $i) (local.get $vl)))
          (i64.store (i32.add (i32.const 65536) (local.get $i)) (local.get $pat))
          (local.set $i (i32.add (local.get $i) (i32.const 8)))
          (br $fl)))
        (drop (call $sw (i64.extend_i32_u (local.get $kl)) (i64.extend_i32_u (local.get $kp))
                        (i64.extend_i32_u (local.get $vl)) (i64.const 65536) (i64.const 1)))))
      (br $next))))
"#;

/// Fuel-stress contract (W02). Every method takes no input.
///   nops / spin          infinite loop of `nop`s / of a bare `br` (out of gas at the attached gas)
///   blocks200 / blocks4999  infinite loop whose body is k empty `block`s (zero finite-wasm fee each)
///   recurse / recurse_big   unbounded recursion (empty frame / 1,000 i64 locals) to the stack limit
///   memmax               grow to 2,048 pages, fill 128 MiB, copy 64 MiB, return sha256 of 8 KiB
///   memfill_loop         infinite loop of 64 MiB `memory.fill`
///   sha_loop / host_loop / grow_loop  infinite loops of sha256(64 KiB) / used_gas / memory.grow(0)
///   count                10,000,000 iterations, then returns the counter (succeeds)
pub fn fuel_wat() -> String {
    let locals = vec!["i64"; 1000].join(" ");
    format!(r#"(module
  (import "env" "sha256" (func $sha (param i64 i64 i64)))
  (import "env" "used_gas" (func $ug (result i64)))
  (import "env" "read_register" (func $rr (param i64 i64)))
  (import "env" "value_return" (func $vr (param i64 i64)))
  (memory 1)
  (func (export "nops") (loop $l nop nop nop nop nop nop nop nop br $l))
  (func (export "spin") (loop $l br $l))
  (func (export "blocks200") (loop $l {b200} br $l))
  (func (export "blocks4999") (loop $l {b4999} br $l))
  (func $rec (call $rec))
  (func (export "recurse") (call $rec))
  (func $recbig (local {locals}) (call $recbig))
  (func (export "recurse_big") (call $recbig))
  (func (export "memmax")
    (drop (memory.grow (i32.const 1024)))
    (memory.fill (i32.const 0) (i32.const 171) (i32.const 134217728))
    (i32.store (i32.const 4096) (memory.size))
    (memory.copy (i32.const 67108864) (i32.const 0) (i32.const 67108864))
    (call $sha (i64.const 67104768) (i64.const 8192) (i64.const 0))
    (call $rr (i64.const 0) (i64.const 0))
    (call $vr (i64.const 32) (i64.const 0)))
  (func (export "memfill_loop") (loop $l (memory.fill (i32.const 0) (i32.const 7) (i32.const 67108864)) br $l))
  (func (export "sha_loop") (loop $l (call $sha (i64.const 0) (i64.const 65536) (i64.const 0)) br $l))
  (func (export "host_loop") (loop $l (drop (call $ug)) br $l))
  (func (export "grow_loop") (loop $l (drop (memory.grow (i32.const 0))) br $l))
  (func (export "count") (local $i i32)
    (loop $l
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 10000000))))
    (i32.store (i32.const 0) (local.get $i))
    (call $vr (i64.const 4) (i64.const 0)))
)"#, b200 = "(block)".repeat(200), b4999 = "(block)".repeat(4999))
}

pub fn fuel_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(fuel_wat()).expect("fuel wat"))
}

/// Evaluation-time contract (W02, `NearSpecV3.Wasm.Arcs`): the zero-fee control shapes of
/// `research/lean-arcs/gen_wasm.py`. Every method takes no input and loops until out of gas.
///   blocks4999   (loop (block)x4999 br $l): one free run, then the back-edge (fused by the arcs)
///   deep4999     (loop block x4999 br $l end x4999): the back-edge discards 4,998 pushed labels
///   midrun4998   (loop (block (br_if 0 (i32.const 1))) (block)x4998 br $l): lands mid-run
///   pushpop4999  (loop block x4999 i32.const 0 drop end x4999 br $l): labels pushed by one run
///                and popped by another, across a charged group
///   brif4999     (loop block x4999 i32.const 1 br_if $l end x4999): a br_if back-edge
pub fn eval_wat() -> String {
    let open = "block ".repeat(4999);
    let close = "end ".repeat(4999);
    format!(r#"(module
  (memory 1)
  (func (export "blocks4999") (loop $l {b4999} br $l))
  (func (export "deep4999") (loop $l {open} br $l {close}))
  (func (export "midrun4998") (loop $l (block (br_if 0 (i32.const 1))) {b4998} br $l))
  (func (export "pushpop4999") (loop $l {open} i32.const 0 drop {close} br $l))
  (func (export "brif4999") (loop $l {open} i32.const 1 br_if $l {close}))
)"#, b4999 = "(block)".repeat(4999), b4998 = "(block)".repeat(4998))
}

pub fn eval_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(eval_wat()).expect("eval wat"))
}

/// Label-keeping loop shapes (W02/W16, the label memo of `NearSpecV3.Wasm.Arcs`). Every method takes
/// no input and loops until out of gas.
///   pushpop4999   (loop block x4999 i32.const 0 drop end x4999 br $l)
///   brif4999      (loop block x4999 i32.const 1 br_if $l end x4999)
///   brtable4999   (loop block x4999 i32.const 0 br_table $l $l end x4999)
///   deepbrif4998  block x4998 (loop $l i32.const 1 br_if $l) end x4998: a shallow back-edge whose
///                 frame holds 5,000 labels
///   brtablealt4997 (loop $a (loop $b i ^= 1; block x4997 local.get i br_table $b $a end x4997)):
///                 a `br_table` back-edge alternating between two depths
pub fn eval2_wat() -> String {
    let open = "block ".repeat(4999);
    let close = "end ".repeat(4999);
    let open8 = "block ".repeat(4998);
    let close8 = "end ".repeat(4998);
    let open7 = "block ".repeat(4997);
    let close7 = "end ".repeat(4997);
    format!(r#"(module
  (memory 1)
  (func (export "pushpop4999") (loop $l {open} i32.const 0 drop {close} br $l))
  (func (export "brif4999") (loop $l {open} i32.const 1 br_if $l {close}))
  (func (export "brtable4999") (loop $l {open} i32.const 0 br_table $l $l {close}))
  (func (export "deepbrif4998") {open8} (loop $l (br_if $l (i32.const 1))) {close8})
  (func (export "brtablealt4997") (local $i i32)
    (loop $a (loop $b (local.set $i (i32.xor (local.get $i) (i32.const 1)))
      {open7} local.get $i br_table $b $a {close7})))
)"#)
}

pub fn eval2_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(eval2_wat()).expect("eval2 wat"))
}

/// `code-response` sizes. 16 · (4 + 4,194,000) + (4 + 4,792) + 4 = 67,108,864 exactly.
pub const CR_BIG: usize = 4_194_000;
pub const CR_N_BIG: usize = 16;
pub const CR_AT: usize = 4_792;
pub const CR_OVER: usize = 4_793;

fn leb(mut n: usize, out: &mut Vec<u8>) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 { out.push(b); return; }
        out.push(b | 0x80);
    }
}

/// A valid module of exactly `size` bytes: `(memory 64) (func (export "run")) (data (i32.const 0) …)`
/// whose data bytes start with `tag` (so every contract has its own hash).
pub fn sized_wasm(size: usize, tag: u8) -> Vec<u8> {
    let mut head = b"\0asm\x01\0\0\0".to_vec();
    head.extend_from_slice(&[0x01, 0x04, 0x01, 0x60, 0x00, 0x00]); // type () -> ()
    head.extend_from_slice(&[0x03, 0x02, 0x01, 0x00]); // one function of type 0
    head.extend_from_slice(&[0x05, 0x03, 0x01, 0x00, 0x40]); // memory min 64 pages
    head.extend_from_slice(&[0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00]); // export "run"
    head.extend_from_slice(&[0x0a, 0x04, 0x01, 0x02, 0x00, 0x0b]); // empty body
    for n in size.saturating_sub(head.len() + 20)..size {
        let mut payload = vec![0x01, 0x00, 0x41, 0x00, 0x0b];
        leb(n, &mut payload);
        let mut sec = vec![0x0b];
        leb(payload.len() + n, &mut sec);
        if head.len() + sec.len() + payload.len() + n == size {
            let mut out = head.clone();
            out.extend_from_slice(&sec);
            out.extend_from_slice(&payload);
            let mut data = vec![tag.wrapping_mul(37).wrapping_add(11); n];
            for (i, b) in data.iter_mut().take(8).enumerate() {
                *b = tag ^ (i as u8);
            }
            out.extend_from_slice(&data);
            assert_eq!(out.len(), size);
            return out;
        }
    }
    panic!("no module of exactly {size} bytes");
}

/// The `code-response` contracts: `crb00`…`crb15` (4,194,000 B), `crsat` (4,792 B), `crsover` (4,793 B).
pub fn cr_contracts() -> &'static [(String, Vec<u8>)] {
    static W: OnceLock<Vec<(String, Vec<u8>)>> = OnceLock::new();
    W.get_or_init(|| {
        let mut v: Vec<(String, Vec<u8>)> = (0..CR_N_BIG).map(|i| (format!("crb{i:02}"), sized_wasm(CR_BIG, i as u8))).collect();
        v.push(("crsat".into(), sized_wasm(CR_AT, 0xA0)));
        v.push(("crsover".into(), sized_wasm(CR_OVER, 0xA1)));
        v
    })
}

/// Data-segment bytes of the large-code contract: the deploy transaction stays under
/// `max_transaction_size` (1,572,864 B).
pub const LARGE_PAD: usize = 1_500_000;

pub fn yield_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(YIELD_WAT).expect("yield wat"))
}

pub fn slim_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(format!("{SLIM_WAT_HEAD})")).expect("slim wat"))
}

pub fn slim_large_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| {
        let pad = "L".repeat(LARGE_PAD);
        wat::parse_str(format!("{SLIM_WAT_HEAD}  (data (i32.const 33554432) \"{pad}\"))")).expect("slim large wat")
    })
}

/// Number of nested zero-fee `block … end` pairs per iteration of `gburn.nest`.
pub const NEST_DEPTH: usize = 500;

/// Gate-B burner: `fill` loops `memory.fill(0, 0, 64 MiB)` (linear fee, cheap to evaluate per gas)
/// until the call runs out of gas; `nest` loops over `NEST_DEPTH` nested empty blocks, so each
/// charged `loop`/`br` pair is followed by `2·NEST_DEPTH` zero-fee instructions.
pub fn burn_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| {
        let open = "(block ".repeat(NEST_DEPTH);
        let close = ")".repeat(NEST_DEPTH);
        wat::parse_str(format!(
            r#"(module
  (memory 1)
  (func (export "fill")
    (loop $l (memory.fill (i32.const 0) (i32.const 0) (i32.const 67108864)) (br $l)))
  (func (export "nest")
    (loop $l {open}{close} (br $l))))"#
        ))
        .expect("burn wat")
    })
}

/// Registry additions of the active scenario (none for the baseline and `global-cache`).
pub fn contracts() -> Vec<(&'static str, Vec<u8>)> {
    match scenario() {
        Some(Scenario::Yield) => vec![("yieldc", yield_wasm().to_vec())],
        Some(Scenario::StorageLimits) => vec![
            ("slim", slim_wasm().to_vec()),
            ("slimlarge", slim_large_wasm().to_vec()),
            ("yieldc", yield_wasm().to_vec()),
        ],
        Some(Scenario::FuelStress) => vec![("fuelc", fuel_wasm().to_vec())],
        Some(Scenario::EvalTime) => vec![("evalc", eval_wasm().to_vec())],
        Some(Scenario::GateBCaps) => vec![("slim", slim_wasm().to_vec()), ("gburn", burn_wasm().to_vec())],
        Some(Scenario::RemovalSoft) => vec![("slim", slim_wasm().to_vec())],
        Some(Scenario::EvalLoops) => vec![("evalc2", eval2_wasm().to_vec())],
        Some(Scenario::CodeResponse) => {
            // registry names must be 'static
            static N: OnceLock<Vec<&'static str>> = OnceLock::new();
            let names = N.get_or_init(|| cr_contracts().iter().map(|(n, _)| &*Box::leak(n.clone().into_boxed_str())).collect());
            names.iter().zip(cr_contracts()).map(|(n, (_, c))| (*n, c.clone())).collect()
        }
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------------------------
// genesis
// ---------------------------------------------------------------------------------------------

/// Storage-limit sizes. The search knob is `pad`; `big` stays fixed.
pub const BIG_RECEIPT: usize = 3_950_000;
pub const BIG_SOFT: usize = 3_900_000;
pub const BIG_CODE: usize = 3_990_000;
pub const RECEIPT_RANGE: u32 = 65_536;
pub const SOFT_RANGE: u32 = 131_072;

pub fn genesis_records(n_shards: usize) -> (Vec<StateRecord>, Balance) {
    let mut records = Vec::new();
    let mut supply = Balance::ZERO;
    let mut add = |records: &mut Vec<StateRecord>, name: &str, code: Option<&[u8]>, data: Vec<(Vec<u8>, Vec<u8>)>| {
        let account_id = acct(name);
        let amount = Balance::from_near(1_000_000);
        let contract = code.map(|c| AccountContract::Local(CryptoHash::hash_bytes(c))).unwrap_or(AccountContract::None);
        records.push(StateRecord::Account { account_id: account_id.clone(), account: Account::new(amount, Balance::ZERO, contract, 0) });
        records.push(StateRecord::access_key(account_id.clone(), &InMemorySigner::test_signer(&account_id).public_key(), AccessKey::full_access()));
        if let Some(c) = code {
            records.push(StateRecord::Contract { account_id: account_id.clone(), code: c.to_vec() });
        }
        for (k, v) in data {
            records.push(StateRecord::Data { account_id: account_id.clone(), data_key: k.into(), value: v.into() });
        }
        supply = supply.checked_add(amount).unwrap();
    };
    match scenario() {
        Some(Scenario::Yield) => {
            assert!(n_shards >= 3, "the yield scenario needs at least 3 shards");
            add(&mut records, "s0yield", Some(yield_wasm()), vec![]);
            add(&mut records, "s1ycall", None, vec![]);
            add(&mut records, "s2ynote", Some(yield_wasm()), vec![]);
        }
        Some(Scenario::StorageLimits) => {
            assert!(n_shards >= 4, "the storage-limits scenario needs at least 4 shards");
            let slim = slim_wasm();
            add(&mut records, "s0zlim", Some(slim), vec![
                (b"big".to_vec(), vec![0xB1; BIG_RECEIPT]),
                (b"pad".to_vec(), vec![0xC1; 1]),
                (b"m".to_vec(), vec![0; 8]),
                (b"k".to_vec(), vec![0x4B; 100]),
                (b"b".to_vec(), vec![0; 16]),
            ]);
            add(&mut records, "s1zsoft", Some(slim), vec![
                (b"big".to_vec(), vec![0xB2; BIG_SOFT]),
                (b"pad".to_vec(), vec![0xC2; 1]),
                (b"b".to_vec(), vec![0; 16]),
            ]);
            add(&mut records, "s2zsrc", None, vec![]);
            let mut misc = vec![(b"a".to_vec(), vec![0xA1; 300]), (b"big".to_vec(), vec![0xB4; 1_000_000])];
            for i in 0..30u8 {
                misc.push((format!("r{i:02}").into_bytes(), vec![i; 40 + i as usize]));
            }
            add(&mut records, "s2zmisc", Some(slim), misc);
            add(&mut records, "s3zsrc", None, vec![]);
            add(&mut records, "s3zcode", Some(slim), vec![(b"big".to_vec(), vec![0xB3; BIG_CODE])]);
            // yields on the soft-lane shard whose timeouts the soft limit can defer
            add(&mut records, "s1zyield", Some(yield_wasm()), vec![]);
        }
        Some(Scenario::FuelStress) => {
            assert!(n_shards >= 2, "the fuel-stress scenario needs at least 2 shards");
            add(&mut records, "s0fuel", Some(fuel_wasm()), vec![]);
            add(&mut records, "s1fuel", Some(fuel_wasm()), vec![]);
        }
        Some(Scenario::EvalTime) => {
            assert!(n_shards >= 2, "the eval-time scenario needs at least 2 shards");
            add(&mut records, "s0eval", Some(eval_wasm()), vec![]);
            add(&mut records, "s1eval", Some(eval_wasm()), vec![]);
        }
        Some(Scenario::EvalLoops) => {
            assert!(n_shards >= 2, "the eval-loops scenario needs at least 2 shards");
            add(&mut records, "s0evl", Some(eval2_wasm()), vec![]);
            add(&mut records, "s1evl", Some(eval2_wasm()), vec![]);
        }
        Some(Scenario::CodeResponse) => {
            for (n, c) in cr_contracts() {
                add(&mut records, &format!("s0{n}"), Some(c.as_slice()), vec![]);
            }
        }
        Some(Scenario::RemovalSoft) => {
            assert!(n_shards >= 2, "the removal-soft scenario needs at least 2 shards");
            let slim = slim_wasm();
            let keys = |pfx: &str, n: usize, w: usize, vlen: usize, fill: u8| -> Vec<(Vec<u8>, Vec<u8>)> {
                (0..n).map(|i| (format!("{pfx}{i:0w$}").into_bytes(), vec![fill; vlen])).collect()
            };
            let mut vm = keys("k", RS_VM_KEYS, 4, 8, 0x6B);
            vm.push((b"x".to_vec(), vec![0x78; 16]));
            add(&mut records, "s0rvm", Some(slim), vm);
            let mut vm2 = keys("j", RS_REINSERT_KEYS, 4, 8, 0x6A);
            vm2.push((b"x".to_vec(), vec![0x79; 16]));
            add(&mut records, "s0rvm2", Some(slim), vm2);
            add(&mut records, "s0rbig", Some(slim), vec![(b"big".to_vec(), vec![0xB7; RS_BIG])]);
            add(&mut records, "s0rdell", None, keys("d", RS_DEL_LARGE_KEYS, 4, 1, 0x44));
            for i in 0..RS_DEL_ACCOUNTS {
                add(&mut records, &format!("s0rdel{i}"), None, keys("d", RS_DEL_KEYS, 3, 1, 0x45));
            }
            add(&mut records, "s0rrcv", None, vec![]);
            add(&mut records, "s1rsrc", None, vec![]);
        }
        Some(Scenario::GateBCaps) => {
            assert!(n_shards >= 2, "the gate-b-caps scenario needs at least 2 shards");
            add(&mut records, "s0gbig", Some(slim_wasm()), vec![(b"big".to_vec(), vec![0xB6; GATEB_BIG])]);
            add(&mut records, "s0gpad", None, vec![]);
            add(&mut records, "s1gburn", Some(burn_wasm()), vec![]);
        }
        _ => {}
    }
    (records, supply)
}

// ---------------------------------------------------------------------------------------------
// transactions
// ---------------------------------------------------------------------------------------------

fn fc(method: &str, args: Vec<u8>, tgas: u64) -> Action {
    fc_gas(method, args, Gas::from_teragas(tgas))
}

fn fc_gas(method: &str, args: Vec<u8>, gas: Gas) -> Action {
    Action::FunctionCall(Box::new(FunctionCallAction {
        method_name: method.into(),
        args,
        gas,
        deposit: Balance::ZERO,
    }))
}

/// Storage program builder.
#[derive(Clone, Default)]
pub struct Prog(pub Vec<u8>);
impl Prog {
    fn op(mut self, op: u8, key: &[u8]) -> Self {
        self.0.push(op);
        self.0.push(key.len() as u8);
        self.0.extend_from_slice(key);
        self
    }
    pub fn r(self, key: &[u8]) -> Self { self.op(b'R', key) }
    pub fn d(self, key: &[u8]) -> Self { self.op(b'D', key) }
    pub fn h(self, key: &[u8]) -> Self { self.op(b'H', key) }
    pub fn w(self, key: &[u8], fill: u8, len: u32) -> Self {
        let mut p = self.op(b'W', key);
        p.0.push(fill);
        p.0.extend_from_slice(&len.to_le_bytes());
        p
    }
    pub fn panic(mut self) -> Self {
        self.0.push(b'P');
        self
    }
    fn describe(&self) -> String {
        let b = &self.0;
        let mut i = 0;
        let mut out = Vec::new();
        while i < b.len() {
            let op = b[i] as char;
            if op == 'P' {
                out.push("P".to_string());
                i += 1;
                continue;
            }
            let kl = b[i + 1] as usize;
            let key = String::from_utf8_lossy(&b[i + 2..i + 2 + kl]).to_string();
            i += 2 + kl;
            if op == 'W' {
                let len = u32::from_le_bytes(b[i + 1..i + 5].try_into().unwrap());
                out.push(format!("W {key} 0x{:02x} {len}", b[i]));
                i += 5;
            } else {
                out.push(format!("{op} {key}"));
            }
        }
        out.join("; ")
    }
}

/// One scheduled transaction.
#[derive(Clone)]
struct Sched {
    label: String,
    signer: AccountId,
    receiver: AccountId,
    actions: Vec<Action>,
    describe: String,
}

fn run_tx(label: String, signer: &str, receiver: &str, prog: Prog) -> Sched {
    Sched {
        label,
        signer: acct(signer),
        receiver: acct(receiver),
        describe: prog.describe(),
        actions: vec![fc("run", prog.0, 300)],
    }
}

fn yield_tx(label: &str, signer: &str, method: &str, args: Vec<u8>) -> Sched {
    yield_tx_to(label, signer, "s0yield", method, args)
}

fn yield_tx_to(label: &str, signer: &str, receiver: &str, method: &str, args: Vec<u8>) -> Sched {
    Sched {
        label: label.to_string(),
        signer: acct(signer),
        receiver: acct(receiver),
        describe: format!("{method}({})", hex::encode(&args[..args.len().min(48)])),
        actions: vec![fc(method, args, 100)],
    }
}

/// The yield schedule: (offset from the scenario start, transaction). Same-offset transactions of
/// one signer are included in one chunk in nonce order.
fn yield_schedule() -> Vec<(u64, Sched)> {
    let yid_a = [0xA5u8; 32].to_vec();
    let yid_b = [0x5Au8; 32].to_vec();
    let with = |slot: u8, rest: &[u8]| {
        let mut v = vec![slot];
        v.extend_from_slice(rest);
        v
    };
    let y = "s0yield";
    let c = "s1ycall";
    let mut v = vec![
        (0, yield_tx("successor.yield.00.create-later", y, "create", vec![1])),
        (0, yield_tx("successor.yield.01.create-timeout", y, "create", vec![4])),
        (2, yield_tx("successor.yield.02.create-resume-same-receipt", y, "create_resume", with(2, b"same-receipt"))),
        (2, yield_tx("successor.yield.03.create-same-chunk", y, "create", vec![3])),
        (2, yield_tx("successor.yield.04.resume-same-chunk", y, "resume", with(3, b"same-chunk"))),
        (4, yield_tx("successor.yield.05.resume-later-chunk", y, "resume", with(1, b"later-chunk"))),
        (4, yield_tx("successor.yield.06.create-dup-same-receipt", y, "create", vec![5])),
        (6, yield_tx("successor.yield.07.resume-twice-same-receipt", y, "resume2", with(5, b"twice"))),
        (6, yield_tx("successor.yield.08.create-dup-separate", y, "create", vec![6])),
        (8, yield_tx("successor.yield.09.resume-dup-first", y, "resume", with(6, b"first"))),
        (8, yield_tx("successor.yield.10.resume-dup-second-same-chunk", y, "resume", with(6, b"second"))),
        (10, yield_tx("successor.yield.11.resume-after-completion", y, "resume", with(1, b"again"))),
        (10, yield_tx("successor.yield.12.resume-wrong-data-id", y, "resume_raw", {
            let mut a = vec![32];
            a.extend_from_slice(&CryptoHash::hash_bytes(b"not a yield").0);
            a.extend_from_slice(b"wrong");
            a
        })),
        (10, yield_tx("successor.yield.13.resume-malformed-data-id", y, "resume_raw", {
            let mut a = vec![31];
            a.extend_from_slice(&[7u8; 31]);
            a.extend_from_slice(b"short");
            a
        })),
        (12, yield_tx("successor.yield.14.create-payload-max", y, "create", vec![7])),
        (12, yield_tx("successor.yield.15.create-payload-over", y, "create", vec![9])),
        (14, yield_tx("successor.yield.16.resume-payload-1024", y, "resume", with(7, &[0x77; 1024]))),
        (14, yield_tx("successor.yield.17.resume-payload-1025", y, "resume", with(9, &[0x99; 1025]))),
        (16, yield_tx("successor.yield.18.cross-shard-create", c, "create", vec![0x87])),
        (16, yield_tx("successor.yield.19.cross-shard-create-timeout", c, "create", vec![0x88])),
        (20, yield_tx("successor.yield.20.cross-shard-resume", c, "resume", with(0x87, b"from-shard-1"))),
        (20, yield_tx("successor.yield.21.create-then-fail", y, "create_fail", vec![10])),
        (22, yield_tx("successor.yield.22.createid", y, "createid", with(11, &yid_a))),
        (22, yield_tx("successor.yield.23.createid-duplicate", y, "createid", with(12, &yid_a))),
        (24, yield_tx("successor.yield.24.resumeid", y, "resumeid", { let mut a = with(11, &yid_a); a.extend_from_slice(b"by-id"); a })),
        (24, yield_tx("successor.yield.25.resumeid-unknown", y, "resumeid", { let mut a = with(12, &yid_b); a.extend_from_slice(b"none"); a })),
        (26, yield_tx("successor.yield.26.create-returned", y, "create_ret", vec![13])),
        (28, yield_tx("successor.yield.27.resume-returned", y, "resume", with(13, b"returned"))),
        (28, yield_tx("successor.yield.28.create-callback-panics", y, "create", vec![0x4E])),
        (30, yield_tx("successor.yield.29.resume-callback-panics", y, "resume", with(0x4E, b"panic"))),
        (30, yield_tx("successor.yield.30.create-race", y, "create", vec![14])),
        (32, yield_tx("successor.yield.31.createid-timeout", y, "createid", with(15, &yid_b))),
    ];
    // The race resume is submitted so that it executes in the chunk whose yield-timeout loop
    // resolves slot 14 (created in the chunk at offset 31, expiring at offset 231).
    v.push((230, yield_tx("successor.yield.32.resume-at-timeout", y, "resume", with(14, b"race"))));
    v.push((240, yield_tx("successor.yield.33.resume-after-timeout", y, "resume", with(4, b"late"))));
    // Created with slot 14 (same chunk). The local resume runs in the chunk after the timeout loop
    // emitted the timeout resume, before that incoming receipt: nearcore cancels the timeout
    // (status ResumeInitiated) and the callback receives the payload one chunk later.
    v.push((30, yield_tx("successor.yield.34.create-race-cancel", y, "create", vec![16])));
    v.push((231, yield_tx("successor.yield.35.resume-after-timeout-fired", y, "resume", with(16, b"cancel"))));
    v
}

/// The fuel-stress schedule (W02). Gas is chosen so the Lean evaluator finishes in minutes:
/// `blocks4999` runs ~10,000 interpreter steps per 2 `regular_op_cost` of gas, so it gets 0.3 Tgas
/// and `blocks200` 5 Tgas; every other method gets the 300 Tgas maximum.
fn fuel_schedule() -> Vec<(u64, Sched)> {
    let call = |label: &str, signer: &str, method: &str, gas: Gas| Sched {
        label: format!("successor.fuel-stress.{label}"),
        signer: acct(signer),
        receiver: acct(signer),
        describe: format!("{method} gas={}", gas.as_gas()),
        actions: vec![fc_gas(method, vec![], gas)],
    };
    let t = Gas::from_teragas;
    let a = "s0fuel";
    let b = "s1fuel";
    vec![
        (0, call("00.nops-300T", a, "nops", t(300))),
        (0, call("01.spin-300T", b, "spin", t(300))),
        (3, call("02.blocks200-5T", a, "blocks200", t(5))),
        (3, call("03.blocks4999-0.3T", b, "blocks4999", Gas::from_gas(300_000_000_000))),
        (6, call("04.recurse-300T", a, "recurse", t(300))),
        (6, call("05.recurse-big-300T", b, "recurse_big", t(300))),
        (9, call("06.memmax-300T", a, "memmax", t(300))),
        (9, call("07.memfill-loop-300T", b, "memfill_loop", t(300))),
        (12, call("08.sha-loop-300T", a, "sha_loop", t(300))),
        (12, call("09.host-loop-300T", b, "host_loop", t(300))),
        (15, call("10.grow-loop-300T", a, "grow_loop", t(300))),
        (15, call("11.count-300T", b, "count", t(300))),
        // three 300 Tgas receipts of one shard: 900 Tgas of the 1 Pgas chunk gas limit
        (18, call("12.chunk-nops-a", a, "nops", t(300))),
        (18, call("13.chunk-nops-b", a, "nops", t(300))),
        (18, call("14.chunk-nops-c", a, "nops", t(300))),
        (21, call("15.blocks200-1T", b, "blocks200", t(1))),
    ]
}

/// The eval-time schedule (W02 arcs): the three shapes the arcs make O(1) per iteration at the
/// 300 Tgas maximum; the two they do not, and `blocks4999` again, at 3 Tgas so that the
/// single-stepping checker finishes them too. One call per chunk.
fn eval_schedule() -> Vec<(u64, Sched)> {
    let call = |label: &str, signer: &str, method: &str, gas: Gas| Sched {
        label: format!("successor.eval-time.{label}"),
        signer: acct(signer),
        receiver: acct(signer),
        describe: format!("{method} gas={}", gas.as_gas()),
        actions: vec![fc_gas(method, vec![], gas)],
    };
    let t = Gas::from_teragas;
    let a = "s0eval";
    let b = "s1eval";
    vec![
        (0, call("00.blocks4999-300T", b, "blocks4999", t(300))),
        (0, call("01.deep4999-300T", a, "deep4999", t(300))),
        (3, call("02.midrun4998-300T", b, "midrun4998", t(300))),
        (3, call("03.blocks4999-3T", a, "blocks4999", t(3))),
        (6, call("04.pushpop4999-3T", b, "pushpop4999", t(3))),
        (6, call("05.brif4999-3T", a, "brif4999", t(3))),
    ]
}

/// The eval-loops schedule (W02/W16 label memo): the four label-keeping shapes at 300 Tgas, then at
/// 3 Tgas (the single-stepping and memo-less checkers finish those too). One call per chunk.
fn eval2_schedule() -> Vec<(u64, Sched)> {
    let call = |label: &str, signer: &str, method: &str, gas: Gas| Sched {
        label: format!("successor.eval-loops.{label}"),
        signer: acct(signer),
        receiver: acct(signer),
        describe: format!("{method} gas={}", gas.as_gas()),
        actions: vec![fc_gas(method, vec![], gas)],
    };
    let t = Gas::from_teragas;
    let (a, b) = ("s0evl", "s1evl");
    vec![
        (0, call("00.pushpop4999-300T", a, "pushpop4999", t(300))),
        (0, call("01.brif4999-300T", b, "brif4999", t(300))),
        (3, call("02.brtable4999-300T", a, "brtable4999", t(300))),
        (3, call("03.deepbrif4998-300T", b, "deepbrif4998", t(300))),
        (6, call("04.pushpop4999-3T", a, "pushpop4999", t(3))),
        (6, call("05.brif4999-3T", b, "brif4999", t(3))),
        (9, call("06.brtable4999-3T", a, "brtable4999", t(3))),
        (9, call("07.deepbrif4998-3T", b, "deepbrif4998", t(3))),
        (12, call("08.brtablealt4997-300T", a, "brtablealt4997", t(300))),
        (12, call("09.brtablealt4997-3T", b, "brtablealt4997", t(3))),
    ]
}

/// The code-response schedule: one chunk at the 64 MiB cap (16 big + `crsat`), one a byte over (16
/// big + `crsover`), one well under (8 big + `crsat`). Every call is `run` (empty) with 20 Tgas.
fn cr_schedule() -> Vec<(u64, Sched)> {
    let call = |label: String, name: &str| {
        let a = format!("s0{name}");
        Sched {
            label,
            signer: acct(&a),
            receiver: acct(&a),
            describe: format!("{a}.run"),
            actions: vec![fc_gas("run", vec![], Gas::from_teragas(20))],
        }
    };
    let mut v = Vec::new();
    for (off, tag, small, n_big) in [(0u64, "at64", "crsat", CR_N_BIG), (6, "over64", "crsover", CR_N_BIG), (12, "under64", "crsat", 8)] {
        for i in 0..n_big {
            v.push((off, call(format!("successor.code-response.{tag}.crb{i:02}"), &format!("crb{i:02}"))));
        }
        v.push((off, call(format!("successor.code-response.{tag}.{small}"), small)));
    }
    v
}

/// removal-soft sizes. `s0rvm`: first-time deletions, two receipts of `RS_VM_DEL` each
/// (2,000 B each in the recorder's upper bound). `s0rvm2`: `RS_REINSERT_KEYS` delete+reinsert pairs
/// per receipt, three receipts per probe (the third crosses). `s0rdel<i>`: `RS_DEL_KEYS` one-byte entries, storage usage
/// just under `MAX_ACCOUNT_DELETION_STORAGE_USAGE` = 10,000 B; `s0rdell` is far above it.
pub const RS_VM_KEYS: usize = 2_400;
pub const RS_VM_DEL: usize = 1_200;
pub const RS_REINSERT_KEYS: usize = 700;
pub const RS_BIG: usize = 3_700_000;
pub const RS_DEL_KEYS: usize = 190;
pub const RS_DEL_LARGE_KEYS: usize = 2_100;
pub const RS_DEL_ACCOUNTS: usize = 4;

/// The removal-soft schedule. A source transaction at offset `o` (shard 1) and the probe's local
/// transactions at `o + 1` (shard 0) execute in the same shard-0 chunk: the source's receipt is
/// incoming there.
fn removal_soft_schedule(fill_xor: u8) -> Vec<(u64, Sched)> {
    use near_primitives::action::{DeleteAccountAction, TransferAction};
    let lbl = |l: &str| format!("successor.removal-soft.{l}");
    let incoming = |l: &str| Sched {
        label: lbl(&format!("{l}.incoming")),
        signer: acct("s1rsrc"),
        receiver: acct("s0rrcv"),
        describe: "Transfer(1 yocto)".into(),
        actions: vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(1) })],
    };
    let del_acct = |l: &str, who: &str| Sched {
        label: lbl(l),
        signer: acct(who),
        receiver: acct(who),
        describe: format!("DeleteAccount({who} -> s1rsrc)"),
        actions: vec![Action::DeleteAccount(DeleteAccountAction { beneficiary_id: acct("s1rsrc") })],
    };
    let vm = |l: &str, who: &str, p: Prog| run_tx(lbl(l), who, who, p);
    let dels = |lo: usize, hi: usize| {
        let mut p = Prog::default();
        for i in lo..hi {
            p = p.d(format!("k{i:04}").as_bytes());
        }
        p
    };
    let reinserts = |n: usize, fill: u8| {
        let mut p = Prog::default();
        for i in 0..n {
            let k = format!("j{i:04}");
            p = p.d(k.as_bytes()).w(k.as_bytes(), fill, 8);
        }
        p
    };
    let mut v = Vec::new();
    // repeated delete+reinsert: three receipts cross the soft limit (8 probes; odd ones also carry a
    // local victim `R x`, the even ones only the incoming transfer)
    for i in 0..8u64 {
        let o = 4 * i;
        let tag = format!("reinsert.p{i}");
        v.push((o, incoming(&tag)));
        let f = (0x20 + i as u8) ^ fill_xor;
        v.push((o + 1, vm(&format!("{tag}.a"), "s0rvm2", reinserts(RS_REINSERT_KEYS, f))));
        v.push((o + 1, vm(&format!("{tag}.b"), "s0rvm2", reinserts(RS_REINSERT_KEYS, f ^ 1))));
        v.push((o + 1, vm(&format!("{tag}.c"), "s0rvm2", reinserts(RS_REINSERT_KEYS, f ^ 2))));
        if i % 2 == 1 {
            v.push((o + 1, vm(&format!("{tag}.victim"), "s0rvm2", Prog::default().r(b"x"))));
        }
    }
    // control: one delete+reinsert receipt stays under the soft limit (incoming executes)
    v.push((32, incoming("reinsert-one.control")));
    v.push((33, vm("reinsert-one.control.a", "s0rvm2", reinserts(RS_REINSERT_KEYS, 0x55 ^ fill_xor))));
    // DeleteAccount at the deletion cap next to a 3.7 MB read (4 accounts, 4 probes)
    for i in 0..RS_DEL_ACCOUNTS as u64 {
        let o = 36 + 4 * i;
        let tag = format!("delete-account.p{i}");
        v.push((o, incoming(&tag)));
        v.push((o + 1, vm(&format!("{tag}.read-big"), "s0rbig", Prog::default().r(b"big"))));
        v.push((o + 1, del_acct(&format!("{tag}.delete"), &format!("s0rdel{i}"))));
    }
    // the literal shape: DeleteAccount of a 2,100-key account (nearcore: DeleteAccountWithLargeState)
    v.push((52, incoming("delete-account-large")));
    v.push((53, vm("delete-account-large.read-big", "s0rbig", Prog::default().r(b"big"))));
    v.push((53, del_acct("delete-account-large.delete", "s0rdell")));
    // first-time VM deletions: two receipts of 1,200 removals, then a local victim
    v.push((56, incoming("vm-delete")));
    v.push((57, vm("vm-delete.a", "s0rvm", dels(0, RS_VM_DEL))));
    v.push((57, vm("vm-delete.b", "s0rvm", dels(RS_VM_DEL, 2 * RS_VM_DEL))));
    v.push((57, vm("vm-delete.victim", "s0rvm", Prog::default().r(b"x"))));
    v
}

/// Fixed storage-limit misc schedule on shards 2 and 3.
/// Gate-B sizes: the genesis value read by every witness-size probe, and the pad arguments.
pub const GATEB_BIG: usize = 3_900_000;
pub const GATEB_PAD: usize = 1_390_000;

/// The gate-b-caps schedule. A transaction submitted at offset `o` is included in the chunk at
/// `START + o + 1`; the witness of the chunk after it carries that chunk's transactions (applied),
/// its 3.9 MB read (storage proof) and the next chunk's transactions (`new_transactions`).
fn gateb_schedule() -> Vec<(u64, Sched)> {
    let pad = |label: &str, n: usize| Sched {
        label: format!("successor.gate-b.{label}"),
        signer: acct("s0gpad"),
        receiver: acct("s0gpad"),
        describe: format!("pad({n} B args, no contract)"),
        actions: vec![fc("pad", vec![0x50; n], 1)],
    };
    let big = |label: &str| run_tx(format!("successor.gate-b.{label}"), "s0gbig", "s0gbig", Prog::default().r(b"big"));
    let burn = |label: &str, method: &str, gas: Gas| Sched {
        label: format!("successor.gate-b.{label}"),
        signer: acct("s1gburn"),
        receiver: acct("s1gburn"),
        describe: format!("{method}({} gas)", gas.as_gas()),
        actions: vec![Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: method.into(),
            args: vec![],
            gas,
            deposit: Balance::ZERO,
        }))],
    };
    let p = GATEB_PAD;
    vec![
        // witness size: below (about 6.7 MB), just below / just above 8 MiB, well above (about 9.5 MB)
        (0, big("wsize.below.read")),
        (0, pad("wsize.below.pad", p)),
        (1, pad("wsize.below.next", p)),
        (6, big("wsize.near-below.read")),
        (6, pad("wsize.near-below.pad0", p)),
        (6, pad("wsize.near-below.pad1", p)),
        (7, pad("wsize.near-below.next0", p)),
        (7, pad("wsize.near-below.next1", 290_000)),
        (12, big("wsize.near-above.read")),
        (12, pad("wsize.near-above.pad0", p)),
        (12, pad("wsize.near-above.pad1", p)),
        (13, pad("wsize.near-above.next0", p)),
        (13, pad("wsize.near-above.next1", 360_000)),
        (18, big("wsize.above.read")),
        (18, pad("wsize.above.pad0", p)),
        (18, pad("wsize.above.pad1", p)),
        (18, pad("wsize.above.pad2", p)),
        (19, pad("wsize.above.next", p)),
        // chunk function-call gas: one 900 Tgas burner (below 1 Pgas), two in one chunk (about 1.8 Pgas)
        (0, burn("gas.below.fill", "fill", Gas::from_teragas(900))),
        (6, burn("gas.above.fill0", "fill", Gas::from_teragas(900))),
        (6, burn("gas.above.fill1", "fill", Gas::from_teragas(900))),
        // zero-fee instructions: 1.5 Ggas and 30 Ggas of `nest` (the latter exhausted the former 64x fuel)
        (12, burn("fuel.nest.small", "nest", Gas::from_gas(1_500_000_000))),
        (18, burn("fuel.nest.large", "nest", Gas::from_gas(30_000_000_000))),
    ]
}

fn storage_misc_schedule() -> Vec<(u64, Sched)> {
    let code = slim_large_wasm().to_vec();
    let deploy = |label: &str, call: Option<Prog>| {
        let mut actions = vec![Action::DeployContract(DeployContractAction { code: code.clone() })];
        let describe = match &call {
            Some(p) => format!("DeployContract(slimlarge) + run({})", p.describe()),
            None => "DeployContract(slimlarge)".into(),
        };
        if let Some(p) = call {
            actions.push(fc("run", p.0, 300));
        }
        Sched { label: label.into(), signer: acct("s3zcode"), receiver: acct("s3zcode"), actions, describe }
    };
    let m = |label: &str, p: Prog| run_tx(format!("successor.storage-limits.misc.{label}"), "s2zmisc", "s2zmisc", p);
    let c = |label: &str, p: Prog| run_tx(format!("successor.storage-limits.code.{label}"), "s3zcode", "s3zcode", p);
    let mut removals = Prog::default();
    for i in 1..30 {
        removals = removals.d(format!("r{i:02}").as_bytes());
    }
    let mut v: Vec<(u64, Sched)> = (0..ANCHORS)
        .map(|i| (2 * i + 1, yield_tx_to(&format!("{ANCHOR_PREFIX}{i:02}"), "s1zyield", "s1zyield", "create", vec![i as u8])))
        .collect();
    v.extend([
        (0, c("call-small-code-near-limit", Prog::default().r(b"big"))),
        (3, deploy("successor.storage-limits.code.deploy-large", None)),
        (6, c("call-large-code-near-limit", Prog::default().r(b"big"))),
        (9, c("call-large-code-repeated-read", Prog::default().r(b"big").r(b"big").h(b"big"))),
        (12, deploy("successor.storage-limits.code.deploy-and-call-same-receipt", Some(Prog::default().r(b"big")))),
        (15, c("call-large-code-read-then-fail", Prog::default().r(b"big").w(b"x", 0x58, 64).panic())),
        (0, m("delete-reinsert", Prog::default().r(b"a").d(b"a").w(b"a", 0xA2, 300).h(b"a"))),
        (3, m("delete-missing", Prog::default().d(b"absent").d(b"absent"))),
        (6, m("delete-29", removals.clone())),
        (9, m("reinsert-29-then-fail", {
            let mut p = Prog::default();
            for i in 1..30 {
                p = p.w(format!("r{i:02}").as_bytes(), i as u8, 40);
            }
            p.panic()
        })),
        (12, m("repeated-shared-reads", Prog::default().r(b"big").r(b"big").r(b"a").r(b"a").h(b"big"))),
        (15, m("delete-big-reinsert", Prog::default().d(b"big").w(b"big", 0xB5, 1_000_000))),
        (18, m("read-reinserted-big", Prog::default().r(b"big"))),
    ]);
    v
}

/// Yield-timeout anchors of the storage-limits scenario (labels `ANCHOR_PREFIX<NN>`).
const ANCHORS: u64 = 8;
const ANCHOR_PREFIX: &str = "successor.storage-limits.soft.yield-anchor.";

// ---------------------------------------------------------------------------------------------
// searches
// ---------------------------------------------------------------------------------------------

/// One probe of a search lane: optional set transaction (offset 0), source transactions on
/// another shard (offset `b_off`, their receipts arrive in the probe chunk) and the probe
/// transactions themselves (offset `a_off`, local receipts in nonce order).
struct Probe {
    label: String,
    t: u32,
    set: Option<Sched>,
    b: Vec<Sched>,
    a: Vec<Sched>,
    /// align the probe chunk with the expiry of an unused yield anchor:
    /// (anchor label, create transaction, expiry height) once chosen
    timeout: bool,
    anchor: Option<(String, CryptoHash, u64)>,
}

#[derive(Clone, Debug, Default)]
struct Observed {
    /// execution height of the anchor's timeout callback (timeout probes)
    cb: Option<u64>,
    /// per probe transaction: (success, status, execution height of its receipt)
    a: Vec<(bool, String, u64)>,
    /// per source transaction: execution height of its receipt on the probe shard
    b: Vec<(bool, String, u64)>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LaneKind {
    Receipt,
    Soft,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Phase {
    Search,
    Final(u8),
    Extra(u8),
    RemovalSearch,
    RemovalFinal(u8),
    Done,
}

struct Lane {
    kind: LaneKind,
    phase: Phase,
    lo: u32,
    hi: u32,
    lo_seen: bool,
    hi_seen: bool,
    /// boundary of the base search (largest passing pad length)
    at: Option<u32>,
    rm_lo: u32,
    rm_hi: u32,
    rm_at: Option<u32>,
    start: u64,
    current: Option<(Probe, Vec<CryptoHash>, Vec<CryptoHash>)>,
    pending: Option<Probe>,
    anchors_used: Vec<String>,
    log: Vec<serde_json::Value>,
    iterations: u32,
    /// Seed-derived XOR on the pad fill byte (storage-limits honours `--seed`).
    fill_xor: u8,
}

const A_OFF: u64 = 3;
const B_OFF: u64 = 2;
/// The probe transactions are included in the chunk at `start + A_OFF + 1`.
const OBS_OFF: u64 = 6;

impl Lane {
    fn new(kind: LaneKind, start: u64) -> Self {
        let hi = if kind == LaneKind::Receipt { RECEIPT_RANGE } else { SOFT_RANGE };
        Lane { kind, phase: Phase::Search, lo: 0, hi, lo_seen: false, hi_seen: false, at: None, rm_lo: 0, rm_hi: 0,
               rm_at: None, start, current: None, pending: None, anchors_used: vec![], log: vec![], iterations: 0,
               fill_xor: 0 }
    }

    fn acct(&self) -> &'static str {
        if self.kind == LaneKind::Receipt { "s0zlim" } else { "s1zsoft" }
    }

    fn src(&self) -> &'static str {
        if self.kind == LaneKind::Receipt { "s3zsrc" } else { "s2zsrc" }
    }

    fn base(&self, t: u32) -> Prog {
        match self.kind {
            // the marker write is rolled back when the receipt fails
            LaneKind::Receipt => Prog::default().w(b"m", (t % 251) as u8 + 1, 8).r(b"big").r(b"pad"),
            LaneKind::Soft => Prog::default().r(b"big").r(b"pad"),
        }
    }

    fn removal(&self, t: u32) -> Prog {
        self.base(t).d(b"k").w(b"k", 0x4B, 100)
    }

    fn probe(&self, label: &str, t: u32, progs: Vec<Prog>, n_b: usize) -> Probe {
        let me = self.acct();
        let lane = if self.kind == LaneKind::Receipt { "receipt" } else { "soft" };
        let fill = (if self.kind == LaneKind::Receipt { 0xC1u8 } else { 0xC2u8 }) ^ self.fill_xor;
        let set = Some(run_tx(format!("successor.storage-limits.{lane}.set-pad.t{t}"), me, me, Prog::default().w(b"pad", fill, t)));
        let b = (0..n_b)
            .map(|i| run_tx(format!("successor.storage-limits.{lane}.{label}.incoming{i}.t{t}"), self.src(), me,
                            Prog::default().w(b"b", 0x42 + i as u8, 16)))
            .collect();
        let a = progs
            .into_iter()
            .enumerate()
            .map(|(i, p)| run_tx(format!("successor.storage-limits.{lane}.{label}.probe{i}.t{t}"), me, me, p))
            .collect();
        Probe { label: label.into(), t, set, b, a, timeout: false, anchor: None }
    }

    /// The next probe, or None when finished.
    fn next_probe(&mut self) -> Option<Probe> {
        let n_b = if self.kind == LaneKind::Soft { 1 } else { 0 };
        loop {
            match self.phase {
                Phase::Search => {
                    if self.hi - self.lo > 1 || !self.lo_seen || !self.hi_seen {
                        // probe the endpoints first, so that the bracket is observed, not assumed
                        let t = if !self.lo_seen { self.lo } else if !self.hi_seen { self.hi } else { self.lo + (self.hi - self.lo) / 2 };
                        return Some(self.probe("search", t, vec![self.base(t)], n_b));
                    }
                    self.at = Some(self.lo);
                    self.phase = Phase::Final(0);
                }
                Phase::Final(i) if i < 3 => {
                    let at = self.at.unwrap();
                    let (name, t) = [("below", at - 1), ("at", at), ("above", at + 1)][i as usize];
                    // final probes carry an incoming receipt on both lanes
                    return Some(self.probe(&format!("final-{name}"), t, vec![self.base(t)], 1));
                }
                Phase::Final(_) => self.phase = Phase::Extra(0),
                Phase::Extra(i) => {
                    let at = self.at.unwrap();
                    let p = match (self.kind, i) {
                        // repeated reads of recorded values add nothing
                        (LaneKind::Receipt, 0) => self.probe("dup-read-at", at, vec![self.base(at).r(b"big").r(b"pad")], 0),
                        (LaneKind::Receipt, 1) => self.probe("dup-read-above", at + 1, vec![self.base(at + 1).r(b"big")], 0),
                        // a receipt failing for another reason at the limit: recorded reads stay
                        (LaneKind::Receipt, 2) => self.probe("panic-at", at, vec![self.base(at).panic()], 1),
                        (LaneKind::Receipt, _) => {
                            self.phase = Phase::RemovalSearch;
                            self.rm_lo = at.saturating_sub(8192);
                            self.rm_hi = at;
                            self.lo_seen = false;
                            self.hi_seen = false;
                            continue;
                        }
                        // a failed (panicking) receipt still counts toward the chunk soft limit
                        (LaneKind::Soft, 0) => self.probe("panic-at", at, vec![self.base(at).panic()], 1),
                        (LaneKind::Soft, 1) => self.probe("panic-above", at + 1, vec![self.base(at + 1).panic()], 1),
                        // the remaining local and incoming receipts are all delayed
                        (LaneKind::Soft, 2) => self.probe("multi-above", at + 1,
                            vec![self.base(at + 1), Prog::default().w(b"b", 0x51, 16)], 2),
                        (LaneKind::Soft, 3) => self.probe("multi-at", at,
                            vec![self.base(at), Prog::default().w(b"b", 0x52, 16)], 2),
                        // a yield timeout due in the probe chunk: resolved there iff the soft limit
                        // is not exceeded after the probe receipt (no incoming receipt here). The
                        // anchors add yield state to this shard, so the margin is 256 bytes.
                        (LaneKind::Soft, 4 | 5) => {
                            let t = if i == 4 { at - 256 } else { at + 256 };
                            let mut p = self.probe(if i == 4 { "timeout-below" } else { "timeout-above" }, t, vec![self.base(t)], 0);
                            p.timeout = true;
                            p
                        }
                        (LaneKind::Soft, _) => {
                            self.phase = Phase::Done;
                            continue;
                        }
                    };
                    self.phase = Phase::Extra(i + 1);
                    return Some(p);
                }
                Phase::RemovalSearch => {
                    if self.rm_hi - self.rm_lo > 1 || !self.lo_seen || !self.hi_seen {
                        let t = if !self.lo_seen { self.rm_lo } else if !self.hi_seen { self.rm_hi } else { self.rm_lo + (self.rm_hi - self.rm_lo) / 2 };
                        return Some(self.probe("removal-search", t, vec![self.removal(t)], 0));
                    }
                    self.rm_at = Some(self.rm_lo);
                    self.phase = Phase::RemovalFinal(0);
                }
                Phase::RemovalFinal(i) if i < 3 => {
                    let at = self.rm_at.unwrap();
                    let (name, t) = [("below", at - 1), ("at", at), ("above", at + 1)][i as usize];
                    return Some(self.probe(&format!("removal-final-{name}"), t, vec![self.removal(t)], 0));
                }
                Phase::RemovalFinal(_) => self.phase = Phase::Done,
                Phase::Done => return None,
            }
        }
    }

    /// Feed an observation of the current probe.
    fn feed(&mut self, p: &Probe, o: &Observed) {
        let a0 = &o.a[0];
        // Receipt lane: pass = the probe receipt succeeded. Soft lane: pass = the incoming receipt
        // executed in the probe receipt's chunk (not delayed).
        let pass = match (self.kind, &p.anchor) {
            // the timeout was resolved in the probe chunk (callback in the next one)
            (_, Some((_, _, e))) => o.cb == Some(e + 1) && a0.2 == *e,
            (LaneKind::Receipt, None) => a0.0,
            (LaneKind::Soft, None) => o.b.first().is_some_and(|b| b.2 == a0.2),
        };
        let deferred: Vec<bool> = o.b.iter().map(|b| b.2 > a0.2).collect();
        self.log.push(json!({
            "label": p.label, "t": p.t, "phase": format!("{:?}", self.phase), "pass": pass,
            "probe_height": a0.2,
            "a": o.a.iter().zip(&p.a).map(|(x, s)| json!({"label": s.label, "program": s.describe, "ok": x.0, "status": x.1, "height": x.2})).collect::<Vec<_>>(),
            "b": o.b.iter().zip(&p.b).map(|(x, s)| json!({"label": s.label, "ok": x.0, "status": x.1, "height": x.2})).collect::<Vec<_>>(),
            "incoming_deferred": deferred,
            "anchor": p.anchor.as_ref().map(|(l, _, e)| json!({"label": l, "expiry_height": e, "callback_height": o.cb})),
        }));
        self.iterations += 1;
        match self.phase {
            Phase::Search | Phase::RemovalSearch => {
                let rm = self.phase == Phase::RemovalSearch;
                if !self.lo_seen {
                    if !pass {
                        eprintln!("WARNING: {:?} lane: lower bracket t={} does not pass; lane stopped", self.kind, p.t);
                        self.phase = Phase::Done;
                    }
                    self.lo_seen = true;
                } else if !self.hi_seen {
                    if pass {
                        eprintln!("WARNING: {:?} lane: upper bracket t={} passes; lane stopped", self.kind, p.t);
                        self.phase = Phase::Done;
                    }
                    self.hi_seen = true;
                } else {
                    let (lo, hi) = if rm { (&mut self.rm_lo, &mut self.rm_hi) } else { (&mut self.lo, &mut self.hi) };
                    if pass { *lo = p.t } else { *hi = p.t }
                }
            }
            Phase::Final(i) => {
                let want = i < 2;
                if pass != want {
                    eprintln!("WARNING: {:?} final probe {i} t={} pass={pass}, expected {want}", self.kind, p.t);
                }
                self.phase = Phase::Final(i + 1);
            }
            Phase::RemovalFinal(i) => {
                let want = i < 2;
                if pass != want {
                    eprintln!("WARNING: removal final probe {i} t={} pass={pass}, expected {want}", p.t);
                }
                self.phase = Phase::RemovalFinal(i + 1);
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------------------------
// the driver
// ---------------------------------------------------------------------------------------------

pub struct Driver {
    start: u64,
    fixed: Vec<(u64, Sched)>,
    lanes: Vec<Lane>,
    submitted: Vec<serde_json::Value>,
}

/// The first scenario height (the chain starts at 10001, after genesis at 10000).
const START: u64 = 10004;

impl Driver {
    pub fn new() -> Self {
        Self::with_seed(None)
    }

    /// The scenario driver for a chain with generator seed `seed`. Only `storage-limits` uses it:
    /// the scenario is a quiet chain whose schedule is otherwise a pure function of the heights, so
    /// every seed produced byte-identical chains. With a seed, its start height moves by
    /// `seed % 5` blocks (which moves every probe across epoch and chunk boundaries) and the pad
    /// fill byte is XORed with `(seed / 5) % 16`, so the recorded values differ. `None` (and every
    /// other scenario) keeps the previous behaviour.
    pub fn with_seed(seed: Option<u64>) -> Self {
        let (shift, fill_xor) = match (scenario(), seed) {
            (Some(Scenario::StorageLimits | Scenario::RemovalSoft), Some(s)) => (s % 5, ((s / 5) % 16) as u8),
            _ => (0, 0),
        };
        let start = START + shift;
        let (fixed, mut lanes) = match scenario() {
            Some(Scenario::Yield) => (yield_schedule(), vec![]),
            Some(Scenario::FuelStress) => (fuel_schedule(), vec![]),
            Some(Scenario::EvalTime) => (eval_schedule(), vec![]),
            Some(Scenario::StorageLimits) => (storage_misc_schedule(),
                vec![Lane::new(LaneKind::Receipt, start), Lane::new(LaneKind::Soft, start)]),
            Some(Scenario::GateBCaps) => (gateb_schedule(), vec![]),
            Some(Scenario::EvalLoops) => (eval2_schedule(), vec![]),
            Some(Scenario::CodeResponse) => (cr_schedule(), vec![]),
            Some(Scenario::RemovalSoft) => (removal_soft_schedule(fill_xor), vec![]),
            _ => (vec![], vec![]),
        };
        for l in lanes.iter_mut() {
            l.fill_xor = fill_xor;
        }
        Driver { start, fixed, lanes, submitted: vec![] }
    }

    fn tx(&mut self, w: &mut World, s: &Setup, bh: &CryptoHash, height: u64, x: &Sched) -> Option<(String, SignedTransaction)> {
        let tx = w.plain_tx(s, bh, &x.signer, &x.receiver, x.actions.clone())?;
        self.submitted.push(json!({"label": x.label, "height": height, "tx": tx.get_hash().to_string(),
                                    "signer": x.signer.to_string(), "receiver": x.receiver.to_string(),
                                    "call": x.describe}));
        Some((x.label.clone(), tx))
    }

    /// Scenario transactions to submit before the block at `height`.
    pub fn txs(&mut self, w: &mut World, s: &Setup, bh: &CryptoHash, height: u64) -> Vec<(String, SignedTransaction)> {
        let mut out = Vec::new();
        if height < self.start {
            return out;
        }
        let off = height - self.start;
        let fixed: Vec<Sched> = self.fixed.iter().filter(|(o, _)| *o == off).map(|x| x.1.clone()).collect();
        for x in &fixed {
            out.extend(self.tx(w, s, bh, height, x));
        }
        for li in 0..self.lanes.len() {
            // observe the current probe
            if let Some((p, a_h, b_h)) = self.lanes[li].current.take() {
                let lane = &self.lanes[li];
                let rel = height - lane.start;
                if rel < OBS_OFF {
                    // submit the probe's transactions on schedule
                    let mut lane_txs = Vec::new();
                    let (mut a_h, mut b_h) = (a_h, b_h);
                    if rel == B_OFF {
                        for x in &p.b {
                            lane_txs.push(x.clone());
                        }
                    }
                    if rel == A_OFF {
                        for x in &p.a {
                            lane_txs.push(x.clone());
                        }
                    }
                    for x in lane_txs {
                        if let Some((l, tx)) = self.tx(w, s, bh, height, &x) {
                            if rel == B_OFF { b_h.push(tx.get_hash()) } else { a_h.push(tx.get_hash()) }
                            out.push((l, tx));
                        }
                    }
                    self.lanes[li].current = Some((p, a_h, b_h));
                    continue;
                }
                let a: Option<Vec<_>> = a_h.iter().map(|h| outcome_of_tx(s, h)).collect();
                let b: Option<Vec<_>> = b_h.iter().map(|h| outcome_of_tx(s, h)).collect();
                let cb = p.anchor.as_ref().and_then(|(_, tx, _)| timeout_callback_height(s, tx));
                match (a, b) {
                    (Some(a), Some(b)) if a.len() == p.a.len() && b.len() == p.b.len()
                        && (p.anchor.is_none() || cb.is_some()) => {
                        let o = Observed { a, b, cb };
                        self.lanes[li].feed(&p, &o);
                    }
                    _ => {
                        if rel > OBS_OFF + 20 {
                            panic!("probe {} t={} has no outcome after {} blocks", p.label, p.t, rel);
                        }
                        self.lanes[li].current = Some((p, a_h, b_h));
                        continue;
                    }
                }
            }
            // start the next probe (a timeout probe waits until its chunk is an anchor's expiry)
            let p = match self.lanes[li].pending.take() {
                Some(p) => Some(p),
                None => self.lanes[li].next_probe(),
            };
            let Some(mut p) = p else { continue };
            if p.timeout && p.anchor.is_none() {
                match self.choose_anchor(s, li, height) {
                    Some(a) => p.anchor = Some(a),
                    None => {
                        eprintln!("WARNING: no yield anchor left for {}; lane stopped", p.label);
                        self.lanes[li].phase = Phase::Done;
                        continue;
                    }
                }
            }
            if let Some((_, _, e)) = &p.anchor {
                if height + 4 < *e {
                    self.lanes[li].pending = Some(p);
                    continue;
                }
            }
            self.lanes[li].start = height;
            if let Some(set) = &p.set {
                let set = set.clone();
                out.extend(self.tx(w, s, bh, height, &set));
            }
            self.lanes[li].current = Some((p, vec![], vec![]));
        }
        out
    }

    /// The unused anchor with the earliest expiry E = create height + 200 such that a probe
    /// started now or later executes in chunk E (probe chunk = start + 4).
    fn choose_anchor(&mut self, s: &Setup, li: usize, height: u64) -> Option<(String, CryptoHash, u64)> {
        let mut best: Option<(String, CryptoHash, u64)> = None;
        for x in &self.submitted {
            let label = x["label"].as_str().unwrap();
            if !label.starts_with(ANCHOR_PREFIX) || self.lanes[li].anchors_used.iter().any(|u| u == label) {
                continue;
            }
            let tx: CryptoHash = x["tx"].as_str().unwrap().parse().unwrap();
            let Some((true, _, created)) = outcome_of_tx(s, &tx) else { continue };
            let e = created + 200;
            if e >= height + 4 && best.as_ref().is_none_or(|b| e < b.2) {
                best = Some((label.to_string(), tx, e));
            }
        }
        if let Some((l, _, _)) = &best {
            self.lanes[li].anchors_used.push(l.clone());
        }
        best
    }

    pub fn finish(&self, s: &Setup, out: &std::path::Path, chain_idx: usize) {
        if scenario().is_none() || scenario() == Some(Scenario::GlobalCache) {
            return;
        }
        // nearcore's own outcome tree of every scenario transaction (transaction, receipts,
        // yield callbacks), with execution heights: the ground truth the collector reports
        let submitted: Vec<serde_json::Value> = self.submitted.iter().map(|x| {
            let mut x = x.clone();
            let h: CryptoHash = x["tx"].as_str().unwrap().parse().unwrap();
            x["outcomes"] = json!(outcome_tree(s, &h));
            x
        }).collect();
        let lanes: Vec<_> = self.lanes.iter().map(|l| json!({
            "kind": format!("{:?}", l.kind), "phase": format!("{:?}", l.phase), "iterations": l.iterations,
            "boundary_pad": l.at, "bracket": [l.lo, l.hi], "removal_boundary_pad": l.rm_at,
            "removal_bracket": [l.rm_lo, l.rm_hi], "probes": l.log,
        })).collect();
        let v = json!({
            "scenario": format!("{:?}", scenario().unwrap()), "start_height": self.start,
            "shards": shard_map(s),
            "sizes": {"big_receipt": BIG_RECEIPT, "big_soft": BIG_SOFT, "big_code": BIG_CODE, "large_pad": LARGE_PAD},
            "contracts": contracts().iter().map(|(n, c)| json!({"name": n, "hash": CryptoHash::hash_bytes(c).to_string(), "len": c.len()})).collect::<Vec<_>>(),
            "lanes": lanes, "submitted": submitted,
            "fixed_labels": self.fixed.iter().map(|x| json!({"offset": x.0, "label": x.1.label})).collect::<Vec<_>>(),
        });
        std::fs::write(out.join(format!("scenario-{chain_idx}.json")), serde_json::to_string_pretty(&v).unwrap()).unwrap();
        for l in &self.lanes {
            if l.phase != Phase::Done {
                eprintln!("WARNING: {:?} lane unfinished in phase {:?} (increase --blocks)", l.kind, l.phase);
            }
        }
    }
}

/// (success, status, execution height) of the first receipt of a transaction, from any client
/// that has both outcomes.
fn outcome_of_tx(s: &Setup, tx: &CryptoHash) -> Option<(bool, String, u64)> {
    // clients track different shards: the transaction and its receipt are looked up separately
    let rid = s.env.clients.iter().find_map(|c| {
        c.chain.get_execution_outcome(tx).ok().and_then(|t| t.outcome_with_id.outcome.receipt_ids.first().copied())
    })?;
    s.env.clients.iter().find_map(|c| {
        let r = c.chain.get_execution_outcome(&rid).ok()?;
        let h = c.chain.get_block_header(&r.block_hash).ok()?;
        let st = &r.outcome_with_id.outcome.status;
        let ok = matches!(st, ExecutionStatus::SuccessValue(_) | ExecutionStatus::SuccessReceiptId(_));
        Some((ok, format!("{st:?}"), h.height()))
    })
}

/// Every outcome reachable from `id` (breadth first): id, height, executor, status, receipts, logs.
fn outcome_tree(s: &Setup, id: &CryptoHash) -> Vec<serde_json::Value> {
    let mut out = Vec::new();
    let mut queue = std::collections::VecDeque::from([*id]);
    while let Some(id) = queue.pop_front() {
        let found = s.env.clients.iter().find_map(|c| {
            let o = c.chain.get_execution_outcome(&id).ok()?;
            let h = c.chain.get_block_header(&o.block_hash).ok()?.height();
            Some((o, h))
        });
        let Some((o, h)) = found else {
            out.push(json!({"id": id.to_string(), "executed": false}));
            continue;
        };
        let oc = &o.outcome_with_id.outcome;
        let status = match &oc.status {
            ExecutionStatus::SuccessValue(v) => json!({"SuccessValue": hex::encode(v)}),
            ExecutionStatus::SuccessReceiptId(r) => json!({"SuccessReceiptId": r.to_string()}),
            other => json!(format!("{other:?}")),
        };
        out.push(json!({"id": id.to_string(), "executed": true, "height": h, "executor": oc.executor_id.to_string(),
                        "status": status, "gas_burnt": oc.gas_burnt.as_gas(), "logs": oc.logs,
                        "receipt_ids": oc.receipt_ids.iter().map(|r| r.to_string()).collect::<Vec<_>>()}));
        queue.extend(oc.receipt_ids.iter().copied());
    }
    out
}

/// (full mutant set, drop-each-node mutants) forced for a chunk by the active scenario: yield —
/// every chunk that ran the yield contract; storage-limits — the chunks of the final at/above
/// probes of the two base searches (their 4 MB witnesses make drop-node mutants too large).
pub fn force_full_mutants(executed: &[serde_json::Value], tx_labels: &[String]) -> (bool, bool) {
    // `mldsa` with the boundary signer (item 10): the full set (with drop-node mutants) for every
    // chunk that carries a `z`-bound step
    if crate::keys::mldsa_bound_mode() {
        let f = tx_labels.iter().any(|l| l.contains("-z-at-") || l.contains("-z-bound-minus-one") || l.contains("-z-neg-bound-minus-one"));
        return (f, f);
    }
    match scenario() {
        Some(Scenario::Yield) => {
            let ran = executed.iter().any(|e| e["name"] == "yieldc");
            (ran, ran)
        }
        Some(Scenario::RemovalSoft) => (tx_labels.iter().any(|l| l.starts_with("successor.removal-soft.")), false),
        Some(Scenario::StorageLimits) => {
            let f = tx_labels.iter().any(|l| (l.contains(".final-at.probe") || l.contains(".final-above.probe")) && !l.contains("removal"));
            (f, false)
        }
        _ => (false, false),
    }
}

/// Shard id of every scenario account (and of each `s<k>` shard prefix) in the final layout.
fn shard_map(s: &Setup) -> serde_json::Value {
    use near_epoch_manager::EpochManagerAdapter;
    let c = &s.env.clients[0];
    let tip = c.chain.head().unwrap();
    let layout = c.epoch_manager.get_shard_layout(&tip.epoch_id).unwrap();
    let names = ["s0yield", "s1ycall", "s2ynote", "s0zlim", "s1zsoft", "s1zyield", "s2zsrc", "s2zmisc", "s3zsrc", "s3zcode",
                 "s0fuel", "s1fuel", "s0eval", "s1eval", "s0gbig", "s0gpad", "s1gburn", "s0evl", "s1evl",
                 "s0rvm", "s0rvm2", "s0rbig", "s0rdell", "s0rdel0", "s0rrcv", "s1rsrc"];
    let mut m = serde_json::Map::new();
    for n in names {
        m.insert(n.into(), json!(layout.account_id_to_shard_id(&acct(n)).to_string()));
    }
    if scenario() == Some(Scenario::CodeResponse) {
        for (n, _) in cr_contracts() {
            let a = format!("s0{n}");
            m.insert(a.clone(), json!(layout.account_id_to_shard_id(&acct(&a)).to_string()));
        }
    }
    json!(m)
}

/// Execution height of the timeout callback of a yield created by `tx` (a callback whose return
/// starts with status byte 2 = PromiseResult::Failed).
fn timeout_callback_height(s: &Setup, tx: &CryptoHash) -> Option<u64> {
    outcome_tree(s, tx).into_iter().find_map(|o| {
        let v = o.get("status")?.get("SuccessValue")?.as_str()?;
        if v.starts_with("02") { o.get("height")?.as_u64() } else { None }
    })
}
