//! Cross-family successor scenarios (README.md "Cross-family scenarios"). Each is opt-in through
//! `NEAR_SUCCESSOR_SCENARIO` (`crate::d3gen::Scenario`), runs on dedicated genesis accounts next to
//! the unchanged baseline traffic, and writes `xfam-<chain>.json`: every scenario transaction with
//! nearcore's own outcome tree, the shard of every scenario account and the per-height congestion
//! info / bandwidth requests of every chunk header. Labels name what was submitted, never what
//! nearcore did with it.
//!
//! * `yield-congestion` — yields created, resumed and timed out while the yield account's shard has
//!   a non-empty delayed queue (on the low-gas-limit chain shapes, gas-heavy receipts exhaust the
//!   chunk gas limit), cross-shard
//!   resume triggers large enough to be buffered by the bandwidth scheduler, and a resume that
//!   follows 360 KB of own-shard receipts.
//! * `curve-callbacks` — every curve host called from a `promise_then` callback (input from the
//!   callback's arguments, from the promise result in memory and in a register), from a three-step
//!   chain, after a cross-shard promise, from a yield-resume callback (arguments or payload, resumed
//!   in the same receipt or by a later cross-shard transaction); plus register and out-of-bounds
//!   input for the BLS writer hosts.
//! * `genesis-tx` — many kinds of transactions submitted before the first block, so that the first
//!   chunks after genesis carry them (`new_transactions` of the genesis-B2 witnesses). With
//!   `crate::d3` this scenario also mutates the genesis-B2 cases (`genesis_mutants`).
//! * `gaskey-target` — gas-key funding, nonce-index transactions, withdrawals, transfers out and
//!   deletion with a balance, executed by receipts on a shard other than the signer's, next to
//!   ordinary cross-shard receipts.
//! * `rollback-refund` — chunks in which failed state initialisation, failed contract
//!   initialisation (global and local code), rolled-back emitted receipts, deposit refunds and
//!   successful emitted receipts are applied together, with global-contract use.

use crate::chaingen::Setup;
use crate::d2gen::{World, view_gk_nonce};
use near_crypto::{InMemorySigner, KeyType, PublicKey, Signer};
use near_primitives::account::{AccessKey, AccessKeyPermission, AccountContract, GasKeyInfo};
use near_primitives::action::{
    Action, AddKeyAction, CreateAccountAction, DeleteAccountAction, DeleteKeyAction, DeployContractAction,
    DeployGlobalContractAction, DeterministicStateInitAction, FunctionCallAction, GlobalContractDeployMode,
    GlobalContractIdentifier, TransferAction, TransferToGasKeyAction, UseGlobalContractAction,
    WithdrawFromGasKeyAction,
};
use near_primitives::hash::CryptoHash;
use near_primitives::state_record::StateRecord;
use near_primitives::transaction::{ExecutionStatus, NonceMode, SignedTransaction, Transaction, TransactionNonce, TransactionV1};
use near_primitives::types::{AccountId, Balance, Gas};
use near_primitives_core::account::Account;
use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    YieldCongestion,
    CurveCallbacks,
    GenesisTx,
    GasKeyTarget,
    RollbackRefund,
    RuntimeErrors,
    /// `host-rows` (Gate-B L0 row validation): a quiet chain whose contracts call the hosts that
    /// no other fixture calls (`contracts/hostrows.wat`), the gas-key promise hosts
    /// (`contracts/kgashost.wat`) and the global / state-init promise hosts
    /// (`tools/d3/global-promise-fixtures/all-hosts-valid-receivers.wat`).
    HostRows,
}

pub fn kind() -> Option<Kind> {
    use crate::d3gen::Scenario as S;
    match crate::d3gen::scenario() {
        Some(S::YieldCongestion | S::YieldCongestionV2Parent) => Some(Kind::YieldCongestion),
        Some(S::CurveCallbacks) => Some(Kind::CurveCallbacks),
        Some(S::GenesisTx) => Some(Kind::GenesisTx),
        Some(S::GasKeyTarget) => Some(Kind::GasKeyTarget),
        Some(S::RollbackRefund) => Some(Kind::RollbackRefund),
        Some(S::RuntimeErrors) => Some(Kind::RuntimeErrors),
        Some(S::HostRows) => Some(Kind::HostRows),
        _ => None,
    }
}

/// `NEAR_XFAM_VARIANT` (workplan item 10): an alternative step table of a scenario, on the same
/// accounts and contracts. `curve-yield-timeout` (with `curve-callbacks`): curve hosts called from
/// timed-out yield callbacks. `state-init-emit` (with `rollback-refund`): state initialisation
/// followed by a successful emit. Unset, every scenario is unchanged.
pub fn variant() -> Option<String> {
    std::env::var("NEAR_XFAM_VARIANT").ok().filter(|v| !v.is_empty())
}

fn acct(s: &str) -> AccountId {
    s.parse().unwrap()
}
const NEAR: u128 = 10u128.pow(24);
/// WithdrawFromGasKey amount replaced at submission by the key's current balance.
const WITHDRAW_ALL: u128 = u128::MAX;

// ---------------------------------------------------------------------------------------------
// contracts
// ---------------------------------------------------------------------------------------------

/// The cross-family contract. Input is loaded at 16384; byte 0 is the slot / mode.
///   noop                         n := first ≤16 input bytes
///   fail                         panic
///   burn [n]                     n × 256 calls of sha256 on empty input (~1.8 Tgas per 256; the
///                                gas is in the host base cost, so a checker replays it cheaply)
///   create [slot]                promise_yield_create(cb, [slot], 20 Tgas); d<slot> := data id
///   resume [slot][pl u16] payload [padding]   resume d<slot> with pl payload bytes; r<slot> := result
///   resume_flood [slot][n][sz u32][pl u16] payload   n promises to self `noop` with sz bytes of
///                                args each, then the resume
///   cb [slot]                    c<slot> := [promise_result status] ++ payload; slot & 0x80:
///                                promise_create(s3xnote.noop, that value); slot & 0x40: panic
///   emit [mode][n] n×([alen][account][mlen][method])   storage w := 2 bytes, one promise per
///                                target (1,000 yocto, 10 Tgas); mode & 2: promise_then(self.cb2) on
///                                the last one; mode & 1: panic afterwards (rollback)
///   cb2                          k := [promise_result status]
///   init_ok / init_fail          i := first input byte; init_fail then panics
pub const XFAM_WAT: &str = r#"(module
  (import "env" "input" (func $input (param i64)))
  (import "env" "read_register" (func $rr (param i64 i64)))
  (import "env" "register_len" (func $rl (param i64) (result i64)))
  (import "env" "storage_write" (func $sw (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_read" (func $sr (param i64 i64 i64) (result i64)))
  (import "env" "value_return" (func $vr (param i64 i64)))
  (import "env" "panic" (func $panic))
  (import "env" "sha256" (func $sha (param i64 i64 i64)))
  (import "env" "current_account_id" (func $cur (param i64)))
  (import "env" "promise_yield_create" (func $pyc (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_yield_resume" (func $pyr (param i64 i64 i64 i64) (result i32)))
  (import "env" "promise_result" (func $pres (param i64 i64) (result i64)))
  (import "env" "promise_results_count" (func $prc (result i64)))
  (import "env" "promise_create" (func $pc (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $pt (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (memory 24)
  (data (i32.const 512) "cb")
  (data (i32.const 528) "noop")
  (data (i32.const 544) "cb2")
  (data (i32.const 560) "s3xnote")
  (data (i32.const 8192) "\e8\03")
  (global $len (mut i64) (i64.const 0))
  (func $load
    (call $input (i64.const 0))
    (global.set $len (call $rl (i64.const 0)))
    (if (i64.ne (global.get $len) (i64.const -1))
      (then (call $rr (i64.const 0) (i64.const 16384)))
      (else (global.set $len (i64.const 0)))))
  (func $b (param $off i32) (result i32) (i32.load8_u (i32.add (i32.const 16384) (local.get $off))))
  (func $key (param $tag i32) (param $slot i32)
    (i32.store8 (i32.const 1200) (local.get $tag))
    (i32.store8 (i32.const 1201) (local.get $slot)))
  (func $me (result i64)
    (call $cur (i64.const 5)) (call $rr (i64.const 5) (i64.const 600)) (call $rl (i64.const 5)))
  (func (export "noop")
    (call $load)
    (call $key (i32.const 110) (i32.const 0))
    (drop (call $sw (i64.const 2) (i64.const 1200)
      (select (global.get $len) (i64.const 16) (i64.lt_u (global.get $len) (i64.const 16)))
      (i64.const 16384) (i64.const 2))))
  (func (export "fail") (call $panic))
  (func (export "burn") (local $i i32) (local $n i32)
    (call $load)
    (local.set $n (i32.mul (call $b (i32.const 0)) (i32.const 256)))
    (block $d (loop $l
      (br_if $d (i32.ge_u (local.get $i) (local.get $n)))
      (call $sha (i64.const 0) (i64.const 524288) (i64.const 9))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l))))
  (func $create
    (drop (call $pyc (i64.const 2) (i64.const 512) (i64.const 1) (i64.const 16384)
                     (i64.const 20000000000000) (i64.const 0) (i64.const 1)))
    (call $rr (i64.const 1) (i64.const 4096))
    (call $key (i32.const 100) (call $b (i32.const 0)))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 32) (i64.const 4096) (i64.const 2))))
  (func (export "create") (call $load) (call $create) (call $vr (i64.const 32) (i64.const 4096)))
  (func $resume (param $plo i32)
    (call $key (i32.const 100) (call $b (i32.const 0)))
    (if (i64.eqz (call $sr (i64.const 2) (i64.const 1200) (i64.const 1)))
      (then (i32.store8 (i32.const 3000) (i32.const 2)) (return)))
    (call $rr (i64.const 1) (i64.const 4096))
    (i32.store8 (i32.const 3000)
      (call $pyr (i64.const 32) (i64.const 4096)
        (i64.extend_i32_u (i32.load16_u (i32.add (i32.const 16384) (local.get $plo))))
        (i64.extend_i32_u (i32.add (i32.const 16386) (local.get $plo))))))
  (func $ret1
    (call $key (i32.const 114) (call $b (i32.const 0)))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 1) (i64.const 3000) (i64.const 2)))
    (call $vr (i64.const 1) (i64.const 3000)))
  (func (export "resume") (call $load) (call $resume (i32.const 1)) (call $ret1))
  (func (export "resume_flood") (local $i i32) (local $ml i64)
    (call $load)
    (local.set $ml (call $me))
    (block $d (loop $l
      (br_if $d (i32.ge_u (local.get $i) (call $b (i32.const 1))))
      (drop (call $pc (local.get $ml) (i64.const 600) (i64.const 4) (i64.const 528)
        (i64.extend_i32_u (i32.load (i32.const 16386))) (i64.const 524288) (i64.const 8208)
        (i64.const 3000000000000)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (call $resume (i32.const 6)) (call $ret1))
  (func (export "cb") (local $st i64) (local $pl i64)
    (call $load)
    (drop (call $prc))
    (local.set $st (call $pres (i64.const 0) (i64.const 1)))
    (i32.store8 (i32.const 3000) (i32.wrap_i64 (local.get $st)))
    (if (i64.eq (local.get $st) (i64.const 1))
      (then (local.set $pl (call $rl (i64.const 1))) (call $rr (i64.const 1) (i64.const 3001))))
    (call $key (i32.const 99) (call $b (i32.const 0)))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.add (local.get $pl) (i64.const 1)) (i64.const 3000) (i64.const 2)))
    (if (i32.and (call $b (i32.const 0)) (i32.const 128))
      (then (drop (call $pc (i64.const 7) (i64.const 560) (i64.const 4) (i64.const 528)
                            (i64.add (local.get $pl) (i64.const 1)) (i64.const 3000) (i64.const 8208)
                            (i64.const 5000000000000)))))
    (if (i32.and (call $b (i32.const 0)) (i32.const 64)) (then (call $panic)))
    (call $vr (i64.add (local.get $pl) (i64.const 1)) (i64.const 3000)))
  (func (export "emit") (local $p i32) (local $i i32) (local $al i64) (local $ap i64)
                        (local $mlen i64) (local $mp i64) (local $last i64) (local $ml i64)
    (call $load)
    (call $key (i32.const 119) (i32.const 0))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 2) (i64.const 16384) (i64.const 2)))
    (local.set $p (i32.const 2))
    (block $d (loop $l
      (br_if $d (i32.ge_u (local.get $i) (call $b (i32.const 1))))
      (local.set $al (i64.extend_i32_u (call $b (local.get $p))))
      (local.set $ap (i64.extend_i32_u (i32.add (i32.const 16385) (local.get $p))))
      (local.set $p (i32.add (local.get $p) (i32.add (i32.const 1) (i32.wrap_i64 (local.get $al)))))
      (local.set $mlen (i64.extend_i32_u (call $b (local.get $p))))
      (local.set $mp (i64.extend_i32_u (i32.add (i32.const 16385) (local.get $p))))
      (local.set $p (i32.add (local.get $p) (i32.add (i32.const 1) (i32.wrap_i64 (local.get $mlen)))))
      (local.set $last (call $pc (local.get $al) (local.get $ap) (local.get $mlen) (local.get $mp)
                                 (i64.const 1) (i64.const 16384) (i64.const 8192) (i64.const 10000000000000)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (if (i32.and (call $b (i32.const 0)) (i32.const 2))
      (then (local.set $ml (call $me))
            (drop (call $pt (local.get $last) (local.get $ml) (i64.const 600) (i64.const 3) (i64.const 544)
                            (i64.const 0) (i64.const 0) (i64.const 8208) (i64.const 10000000000000)))))
    (if (i32.and (call $b (i32.const 0)) (i32.const 1)) (then (call $panic))))
  (func (export "cb2") (local $st i64)
    (local.set $st (call $pres (i64.const 0) (i64.const 1)))
    (i32.store8 (i32.const 3000) (i32.wrap_i64 (local.get $st)))
    (call $key (i32.const 107) (i32.const 0))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 1) (i64.const 3000) (i64.const 2)))
    (call $vr (i64.const 1) (i64.const 3000)))
  (func (export "init_ok")
    (call $load) (call $key (i32.const 105) (i32.const 0))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 1) (i64.const 16384) (i64.const 2))))
  (func (export "init_fail")
    (call $load) (call $key (i32.const 105) (i32.const 0))
    (drop (call $sw (i64.const 2) (i64.const 1200) (i64.const 1) (i64.const 16384) (i64.const 2)))
    (call $panic))
)"#;

pub fn xfam_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(XFAM_WAT).expect("xfam wat"))
}

/// Curve hosts of `xcurve`: (name, kind). Kinds: 0 = alt_bn128 writer without result
/// (`(len, ptr, register)`), 1 = BLS writer `(len, ptr, register) -> u64`, 2 = pairing
/// `(len, ptr) -> u64`, 3 = p256_verify, 4 = ecrecover.
pub const CURVE_HOSTS: &[(&str, u8)] = &[
    ("alt_bn128_g1_multiexp", 0),
    ("alt_bn128_g1_sum", 0),
    ("alt_bn128_pairing_check", 2),
    ("bls12381_p1_sum", 1),
    ("bls12381_p2_sum", 1),
    ("bls12381_g1_multiexp", 1),
    ("bls12381_g2_multiexp", 1),
    ("bls12381_map_fp_to_g1", 1),
    ("bls12381_map_fp2_to_g2", 1),
    ("bls12381_pairing_check", 2),
    ("bls12381_p1_decompress", 1),
    ("bls12381_p2_decompress", 1),
    ("p256_verify", 3),
    ("ecrecover", 4),
];

/// `xcurve`: per host `H` the methods `H` (memory input from the call's arguments), `H_reg`
/// (register 0 = the arguments, `value_len = u64::MAX`), `H_oob` (64 bytes at 0x7fffffff), `H_rm`
/// (memory input = promise result 0), `H_rr` (register input = promise result 0); p256/ecrecover
/// only have `H` and `H_rm`. Every method returns and stores (key `o`) `[u64 result] ++ register 1`
/// like `contracts/curvehosts.wat`. Dispatchers (arguments `[gas Tgas][mlen][method]...`):
///   then   [g][mlen][method][args]          create(self.echo(args)).then(self.method(args), g)
///   then2  [g][mlen][method][args]          create(self.echo).then(self.echo).then(self.method)
///   thenx  [g][mlen][method][olen][other][args]   create(other.echo(args)).then(self.method(args))
///   yield  [g][mlen][method][args]          yield_create(method, args, g) + resume(payload = args)
///   yslot  [slot][g][mlen][method][args]    yield_create only; y<slot> := data id
///   rslot  [slot][payload]                  resume y<slot> with the payload
///   echo                                    value_return(arguments)
pub fn xcurve_wat() -> String {
    let mut s = String::from("(module\n");
    s += r#"  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (import "env" "storage_write" (func $storage_write (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_read" (func $storage_read (param i64 i64 i64) (result i64)))
  (import "env" "current_account_id" (func $cur (param i64)))
  (import "env" "promise_result" (func $pres (param i64 i64) (result i64)))
  (import "env" "promise_create" (func $pc (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $pt (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_yield_create" (func $pyc (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_yield_resume" (func $pyr (param i64 i64 i64 i64) (result i32)))
  (import "env" "alt_bn128_g1_multiexp" (func $alt_bn128_g1_multiexp (param i64 i64 i64)))
  (import "env" "alt_bn128_g1_sum" (func $alt_bn128_g1_sum (param i64 i64 i64)))
  (import "env" "alt_bn128_pairing_check" (func $alt_bn128_pairing_check (param i64 i64) (result i64)))
  (import "env" "bls12381_p1_sum" (func $bls12381_p1_sum (param i64 i64 i64) (result i64)))
  (import "env" "bls12381_p2_sum" (func $bls12381_p2_sum (param i64 i64 i64) (result i64)))
  (import "env" "bls12381_g1_multiexp" (func $bls12381_g1_multiexp (param i64 i64 i64) (result i64)))
  (import "env" "bls12381_g2_multiexp" (func $bls12381_g2_multiexp (param i64 i64 i64) (result i64)))
  (import "env" "bls12381_map_fp_to_g1" (func $bls12381_map_fp_to_g1 (param i64 i64 i64) (result i64)))
  (import "env" "bls12381_map_fp2_to_g2" (func $bls12381_map_fp2_to_g2 (param i64 i64 i64) (result i64)))
  (import "env" "bls12381_pairing_check" (func $bls12381_pairing_check (param i64 i64) (result i64)))
  (import "env" "bls12381_p1_decompress" (func $bls12381_p1_decompress (param i64 i64 i64) (result i64)))
  (import "env" "bls12381_p2_decompress" (func $bls12381_p2_decompress (param i64 i64 i64) (result i64)))
  (import "env" "p256_verify" (func $p256_verify (param i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "ecrecover" (func $ecrecover (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (memory 4)
  (data (i32.const 0) "o")
  (data (i32.const 200) "echo")
  ;; arguments -> memory at 1024; returns their length
  (func $load (result i64)
    (call $input (i64.const 0))
    (call $read_register (i64.const 0) (i64.const 1024))
    (call $register_len (i64.const 0)))
  ;; promise result 0 -> memory at 1024; returns its length
  (func $load_res (result i64)
    (drop (call $pres (i64.const 0) (i64.const 0)))
    (call $read_register (i64.const 0) (i64.const 1024))
    (call $register_len (i64.const 0)))
  (func $finish (param $r i64)
    (local $n i64)
    (i64.store (i32.const 32768) (local.get $r))
    (local.set $n (call $register_len (i64.const 1)))
    (if (i64.eq (local.get $n) (i64.const -1))
      (then (local.set $n (i64.const 0)))
      (else (call $read_register (i64.const 1) (i64.const 32776))))
    (call $value_return (i64.add (local.get $n) (i64.const 8)) (i64.const 32768))
    (drop (call $storage_write (i64.const 1) (i64.const 0)
      (i64.add (local.get $n) (i64.const 8)) (i64.const 32768) (i64.const 2))))
  ;; own account id at 60000; returns its length
  (func $me (result i64)
    (call $cur (i64.const 5)) (call $read_register (i64.const 5) (i64.const 60000)) (call $register_len (i64.const 5)))
  (func (export "echo") (call $value_return (call $load) (i64.const 1024)))
"#;
    for &(h, k) in CURVE_HOSTS {
        let call = |len: &str, ptr: &str| -> String {
            match k {
                0 => format!("(call ${h} {len} {ptr} (i64.const 1)) (call $finish (i64.const 0))"),
                1 => format!("(call $finish (call ${h} {len} {ptr} (i64.const 1)))"),
                2 => format!("(call $finish (call ${h} {len} {ptr}))"),
                _ => unreachable!(),
            }
        };
        let mem = "(local.get $n) (i64.const 1024)";
        if k <= 2 {
            s += &format!("  (func (export \"{h}\") (local $n i64) (local.set $n (call $load)) {})\n", call("(local.get $n)", "(i64.const 1024)"));
            s += &format!("  (func (export \"{h}_rm\") (local $n i64) (local.set $n (call $load_res)) {})\n", call("(local.get $n)", "(i64.const 1024)"));
            s += &format!("  (func (export \"{h}_reg\") (call $input (i64.const 0)) {})\n", call("(i64.const -1)", "(i64.const 0)"));
            s += &format!("  (func (export \"{h}_rr\") (drop (call $pres (i64.const 0) (i64.const 0))) {})\n", call("(i64.const -1)", "(i64.const 0)"));
            s += &format!("  (func (export \"{h}_oob\") {})\n", call("(i64.const 64)", "(i64.const 0x7fffffff)"));
            let _ = mem;
        } else {
            for (suffix, loader) in [("", "$load"), ("_rm", "$load_res")] {
                if k == 3 {
                    s += &format!(r#"  (func (export "{h}{suffix}")
    (local $n i64) (local $sl i64) (local $pl i64)
    (local.set $n (call {loader}))
    (local.set $sl (i64.load8_u (i32.const 1024)))
    (local.set $pl (i64.load8_u (i32.const 1025)))
    (call $finish (call $p256_verify
      (local.get $sl) (i64.const 1026)
      (i64.sub (i64.sub (i64.sub (local.get $n) (i64.const 2)) (local.get $sl)) (local.get $pl))
      (i64.add (i64.const 1026) (i64.add (local.get $sl) (local.get $pl)))
      (local.get $pl) (i64.add (i64.const 1026) (local.get $sl)))))
"#);
                } else {
                    s += &format!(r#"  (func (export "{h}{suffix}")
    (local $sl i64) (local $hl i64)
    (drop (call {loader}))
    (local.set $sl (i64.load8_u (i32.const 1026)))
    (local.set $hl (i64.load8_u (i32.const 1027)))
    (call $finish (call $ecrecover
      (local.get $hl) (i64.add (i64.const 1028) (local.get $sl))
      (local.get $sl) (i64.const 1028)
      (i64.load8_u (i32.const 1024)) (i64.load8_u (i32.const 1025)) (i64.const 1))))
"#);
                }
            }
        }
    }
    // dispatchers: [g][mlen][method][args...] at 1024
    s += r#"  (func (export "then") (local $n i64) (local $ml i64) (local $mlen i64) (local $ap i64) (local $al i64) (local $p i64)
    (local.set $n (call $load))
    (local.set $mlen (i64.load8_u (i32.const 1025)))
    (local.set $ap (i64.add (i64.const 1026) (local.get $mlen)))
    (local.set $al (i64.sub (local.get $n) (i64.add (i64.const 2) (local.get $mlen))))
    (local.set $ml (call $me))
    (local.set $p (call $pc (local.get $ml) (i64.const 60000) (i64.const 4) (i64.const 200)
                            (local.get $al) (local.get $ap) (i64.const 240) (i64.const 10000000000000)))
    (drop (call $pt (local.get $p) (local.get $ml) (i64.const 60000) (local.get $mlen) (i64.const 1026)
                    (local.get $al) (local.get $ap) (i64.const 240)
                    (i64.mul (i64.load8_u (i32.const 1024)) (i64.const 1000000000000)))))
  (func (export "then2") (local $n i64) (local $ml i64) (local $mlen i64) (local $ap i64) (local $al i64) (local $p i64)
    (local.set $n (call $load))
    (local.set $mlen (i64.load8_u (i32.const 1025)))
    (local.set $ap (i64.add (i64.const 1026) (local.get $mlen)))
    (local.set $al (i64.sub (local.get $n) (i64.add (i64.const 2) (local.get $mlen))))
    (local.set $ml (call $me))
    (local.set $p (call $pc (local.get $ml) (i64.const 60000) (i64.const 4) (i64.const 200)
                            (local.get $al) (local.get $ap) (i64.const 240) (i64.const 10000000000000)))
    (local.set $p (call $pt (local.get $p) (local.get $ml) (i64.const 60000) (i64.const 4) (i64.const 200)
                            (local.get $al) (local.get $ap) (i64.const 240) (i64.const 10000000000000)))
    (drop (call $pt (local.get $p) (local.get $ml) (i64.const 60000) (local.get $mlen) (i64.const 1026)
                    (local.get $al) (local.get $ap) (i64.const 240)
                    (i64.mul (i64.load8_u (i32.const 1024)) (i64.const 1000000000000)))))
  (func (export "thenx") (local $n i64) (local $ml i64) (local $mlen i64) (local $ol i64) (local $op i64) (local $ap i64) (local $al i64) (local $p i64)
    (local.set $n (call $load))
    (local.set $mlen (i64.load8_u (i32.const 1025)))
    (local.set $ol (i64.load8_u (i32.wrap_i64 (i64.add (i64.const 1026) (local.get $mlen)))))
    (local.set $op (i64.add (i64.const 1027) (local.get $mlen)))
    (local.set $ap (i64.add (local.get $op) (local.get $ol)))
    (local.set $al (i64.sub (local.get $n) (i64.add (i64.const 3) (i64.add (local.get $mlen) (local.get $ol)))))
    (local.set $ml (call $me))
    (local.set $p (call $pc (local.get $ol) (local.get $op) (i64.const 4) (i64.const 200)
                            (local.get $al) (local.get $ap) (i64.const 240) (i64.const 10000000000000)))
    (drop (call $pt (local.get $p) (local.get $ml) (i64.const 60000) (local.get $mlen) (i64.const 1026)
                    (local.get $al) (local.get $ap) (i64.const 240)
                    (i64.mul (i64.load8_u (i32.const 1024)) (i64.const 1000000000000)))))
  (func (export "yield") (local $n i64) (local $mlen i64) (local $ap i64) (local $al i64)
    (local.set $n (call $load))
    (local.set $mlen (i64.load8_u (i32.const 1025)))
    (local.set $ap (i64.add (i64.const 1026) (local.get $mlen)))
    (local.set $al (i64.sub (local.get $n) (i64.add (i64.const 2) (local.get $mlen))))
    (drop (call $pyc (local.get $mlen) (i64.const 1026) (local.get $al) (local.get $ap)
                     (i64.mul (i64.load8_u (i32.const 1024)) (i64.const 1000000000000)) (i64.const 0) (i64.const 1)))
    (call $read_register (i64.const 1) (i64.const 61000))
    (drop (call $pyr (i64.const 32) (i64.const 61000) (local.get $al) (local.get $ap))))
  (func (export "yslot") (local $n i64) (local $mlen i64) (local $ap i64) (local $al i64)
    (local.set $n (call $load))
    (local.set $mlen (i64.load8_u (i32.const 1026)))
    (local.set $ap (i64.add (i64.const 1027) (local.get $mlen)))
    (local.set $al (i64.sub (local.get $n) (i64.add (i64.const 3) (local.get $mlen))))
    (drop (call $pyc (local.get $mlen) (i64.const 1027) (local.get $al) (local.get $ap)
                     (i64.mul (i64.load8_u (i32.const 1025)) (i64.const 1000000000000)) (i64.const 0) (i64.const 1)))
    (call $read_register (i64.const 1) (i64.const 61000))
    (i32.store8 (i32.const 61100) (i32.const 121))
    (i32.store8 (i32.const 61101) (i32.load8_u (i32.const 1024)))
    (drop (call $storage_write (i64.const 2) (i64.const 61100) (i64.const 32) (i64.const 61000) (i64.const 2))))
  (func (export "rslot") (local $n i64)
    (local.set $n (call $load))
    (i32.store8 (i32.const 61100) (i32.const 121))
    (i32.store8 (i32.const 61101) (i32.load8_u (i32.const 1024)))
    (if (i64.eqz (call $storage_read (i64.const 2) (i64.const 61100) (i64.const 2))) (then (return)))
    (call $read_register (i64.const 2) (i64.const 61000))
    (i32.store8 (i32.const 61200)
      (call $pyr (i64.const 32) (i64.const 61000) (i64.sub (local.get $n) (i64.const 1)) (i64.const 1025)))
    (call $value_return (i64.const 1) (i64.const 61200)))
)"#;
    s
}

pub fn xcurve_wasm() -> &'static [u8] {
    static W: OnceLock<Vec<u8>> = OnceLock::new();
    W.get_or_init(|| wat::parse_str(xcurve_wat()).expect("xcurve wat"))
}

/// Registry additions of the active cross-family scenario.
pub fn contracts() -> Vec<(&'static str, Vec<u8>)> {
    match kind() {
        Some(Kind::CurveCallbacks) => vec![("xcurve", xcurve_wasm().to_vec())],
        Some(Kind::RuntimeErrors) => {
            let mut v = vec![("xfam", xfam_wasm().to_vec())];
            v.extend(crate::rterr::contracts().iter().cloned());
            v
        }
        Some(Kind::HostRows) => HR_CONTRACTS.iter().map(|n| (*n, hr_code(n).to_vec())).collect(),
        Some(_) => vec![("xfam", xfam_wasm().to_vec())],
        None => vec![],
    }
}

// ---------------------------------------------------------------------------------------------
// genesis
// ---------------------------------------------------------------------------------------------

/// Dedicated accounts of the active scenario: (name, has `xfam`/`xcurve` code).
fn accounts() -> Vec<(&'static str, bool)> {
    match kind() {
        Some(Kind::YieldCongestion) => vec![("s0xyield", true), ("s0xburn", true), ("s1xcall", false), ("s2xburn", false), ("s3xnote", true)],
        Some(Kind::CurveCallbacks) => vec![("s0xcurve", true), ("s2xcurve", true), ("s1xccall", false)],
        Some(Kind::GenesisTx) => vec![("s0gx", true), ("s1gx", true), ("s2gx", true), ("s3gx", false), ("s3xnote", true)],
        Some(Kind::GasKeyTarget) => vec![("s0gkt", false), ("s1gkc", true), ("s2gkr", false), ("s3gks", false)],
        Some(Kind::RollbackRefund) => vec![("s0rbg", false), ("s0rbu", false), ("s1rbs", false), ("s2rbt", true), ("s3rbt", true), ("s3xnote", true)],
        Some(Kind::RuntimeErrors) => RT_ACCOUNTS.iter().map(|(n, c)| (*n, c.is_some())).collect(),
        Some(Kind::HostRows) => HR_ACCOUNTS.iter().map(|(n, c)| (*n, c.is_some())).collect(),
        None => vec![],
    }
}

/// `runtime-errors` accounts and their genesis code (`None`: no code; `xfam`: the caller). The
/// `s<k>rtdep` accounts receive in-chain deployments.
const RT_ACCOUNTS: &[(&str, Option<&str>)] = &[
    ("s0rtload", Some("rtload")),
    ("s1rtfita", Some("rtfita")),
    ("s1rtovra", Some("rtovra")),
    ("s2rtfitb", Some("rtfitb")),
    ("s2rtovrb", Some("rtovrb")),
    ("s3rtfitc", Some("rtfitc")),
    ("s3rtovrc", Some("rtovrc")),
    ("s0rtcombo", Some("rtcombo")),
    ("s1rtlink", Some("rtunk_nosuch")),
    ("s2rtbadty", Some("rtbad_storage_write")),
    ("s3rtx", Some("xfam")),
    ("s0rtdep", None),
    ("s1rtdep", None),
    ("s2rtdep", None),
    ("s3rtdep", None),
];

/// `host-rows` contracts (registry names).
const HR_CONTRACTS: &[&str] = &["hostrows", "kgashost", "hrall"];

fn hr_code(name: &str) -> &'static [u8] {
    static C: OnceLock<Vec<Vec<u8>>> = OnceLock::new();
    let c = C.get_or_init(|| vec![
        wat::parse_str(include_str!("../contracts/hostrows.wat")).expect("hostrows.wat"),
        crate::keys::host_code(),
        wat::parse_str(include_str!("../../../tools/d3/global-promise-fixtures/all-hosts-valid-receivers.wat")).expect("all-hosts wat"),
    ]);
    &c[HR_CONTRACTS.iter().position(|n| *n == name).unwrap_or_else(|| panic!("host-rows contract {name}"))]
}

/// `host-rows` accounts and their genesis code (`None`: no code; the global-contract users and the
/// in-chain deployer start without code).
const HR_ACCOUNTS: &[(&str, Option<&str>)] = &[
    ("s0hrow", Some("hostrows")),
    ("s1hrow", Some("hostrows")),
    ("s2hrkg", Some("kgashost")),
    ("s3hrall", Some("hrall")),
    ("s2hrglob", None),
    ("s3hrglob", None),
    ("s3hrgacc", None),
    ("s1hrgbya", None),
    ("s1hrdep", None),
];

fn account_code(name: &str) -> &'static [u8] {
    match kind() {
        Some(Kind::CurveCallbacks) => xcurve_wasm(),
        Some(Kind::RuntimeErrors) => match RT_ACCOUNTS.iter().find(|(n, _)| *n == name).and_then(|x| x.1) {
            Some("xfam") | None => xfam_wasm(),
            Some(c) => crate::rterr::code(c),
        },
        // accounts without genesis code: the code is unused (`genesis_records` checks `with_code`)
        Some(Kind::HostRows) => HR_ACCOUNTS.iter().find(|(n, _)| *n == name).and_then(|x| x.1).map(hr_code).unwrap_or(&[]),
        _ => xfam_wasm(),
    }
}

pub fn genesis_records(n_shards: usize) -> (Vec<StateRecord>, Balance) {
    let mut records = Vec::new();
    let mut supply = Balance::ZERO;
    if kind().is_none() {
        return (records, supply);
    }
    assert!(n_shards >= 4, "the cross-family scenarios need at least 4 shards");
    for (name, with_code) in accounts() {
        let code = account_code(name);
        let account_id = acct(name);
        let amount = Balance::from_near(1_000_000);
        let contract = if with_code { AccountContract::Local(CryptoHash::hash_bytes(code)) } else { AccountContract::None };
        records.push(StateRecord::Account { account_id: account_id.clone(), account: Account::new(amount, Balance::ZERO, contract, 0) });
        records.push(StateRecord::access_key(account_id.clone(), &InMemorySigner::test_signer(&account_id).public_key(), AccessKey::full_access()));
        if with_code {
            records.push(StateRecord::Contract { account_id: account_id.clone(), code: code.to_vec() });
        }
        supply = supply.checked_add(amount).unwrap();
    }
    (records, supply)
}

// ---------------------------------------------------------------------------------------------
// steps
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum How {
    /// the account's ED25519 test key (World nonces)
    Main,
    /// a gas key of the signer: (seed tag, nonce index)
    GasKey(&'static str, u16),
}

#[derive(Clone, Debug)]
struct Step {
    off: u64,
    label: String,
    signer: AccountId,
    receiver: AccountId,
    actions: Vec<Action>,
    how: How,
    describe: String,
}

fn fc(method: &str, args: Vec<u8>, tgas: u64, deposit: u128) -> Action {
    Action::FunctionCall(Box::new(FunctionCallAction {
        method_name: method.into(),
        args,
        gas: Gas::from_teragas(tgas),
        deposit: Balance::from_yoctonear(deposit),
    }))
}
fn tr(d: u128) -> Action {
    Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(d) })
}
fn gas_key(a: &AccountId, tag: &str) -> Signer {
    InMemorySigner::from_seed(a.clone(), KeyType::ED25519, &format!("xfam-{tag}-{a}"))
}
fn add_gas_key(pk: PublicKey, n: u16) -> Action {
    Action::AddKey(Box::new(AddKeyAction {
        public_key: pk,
        access_key: AccessKey { nonce: 0, permission: AccessKeyPermission::GasKeyFullAccess(GasKeyInfo { balance: Balance::ZERO, num_nonces: n }) },
    }))
}
fn add_full(pk: PublicKey) -> Action {
    Action::AddKey(Box::new(AddKeyAction { public_key: pk, access_key: AccessKey::full_access() }))
}
fn fund(pk: PublicKey, d: u128) -> Action {
    Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: pk, deposit: Balance::from_yoctonear(d) }))
}
fn withdraw(pk: PublicKey, d: u128) -> Action {
    Action::WithdrawFromGasKey(Box::new(WithdrawFromGasKeyAction { public_key: pk, amount: Balance::from_yoctonear(d) }))
}
fn del_key(pk: PublicKey) -> Action {
    Action::DeleteKey(Box::new(DeleteKeyAction { public_key: pk }))
}

fn step(off: u64, label: String, signer: &str, receiver: &str, actions: Vec<Action>, how: How) -> Step {
    let describe = actions.iter().map(describe_action).collect::<Vec<_>>().join(", ");
    Step { off, label, signer: acct(signer), receiver: acct(receiver), actions, how, describe }
}

fn describe_action(a: &Action) -> String {
    match a {
        Action::FunctionCall(f) => format!("FunctionCall({}, {} B args, {} Tgas, deposit {})", f.method_name, f.args.len(),
            f.gas.as_gas() / 10u64.pow(12), f.deposit.as_yoctonear()),
        Action::Transfer(t) => format!("Transfer({})", t.deposit.as_yoctonear()),
        Action::TransferToGasKey(t) => format!("TransferToGasKey({}, {})", t.public_key, t.deposit.as_yoctonear()),
        Action::WithdrawFromGasKey(t) => format!("WithdrawFromGasKey({}, {})", t.public_key, t.amount.as_yoctonear()),
        Action::AddKey(k) => format!("AddKey({}, {:?})", k.public_key, k.access_key.permission),
        Action::DeleteKey(k) => format!("DeleteKey({})", k.public_key),
        Action::DeployContract(d) => format!("DeployContract({} B)", d.code.len()),
        Action::DeployGlobalContract(d) => format!("DeployGlobalContract({} B, {:?})", d.code.len(), d.deploy_mode),
        Action::UseGlobalContract(u) => format!("UseGlobalContract({:?})", u.contract_identifier),
        Action::DeterministicStateInit(s) => format!("DeterministicStateInit(deposit {})", s.deposit.as_yoctonear()),
        other => format!("{other:?}").chars().take(80).collect(),
    }
}

/// `resume` arguments: [slot][payload length u16][payload][padding].
fn resume_args(slot: u8, payload: &[u8], pad: usize) -> Vec<u8> {
    let mut v = vec![slot];
    v.extend((payload.len() as u16).to_le_bytes());
    v.extend_from_slice(payload);
    v.extend(std::iter::repeat_n(0x50u8, pad));
    v
}

fn yield_congestion() -> Vec<Step> {
    let y = "s0xyield";
    let lab = |i: usize, s: &str| format!("successor.yield-congestion.{i:02}.{s}");
    let yc = |off, i, s: &str, signer: &str, m: &str, args: Vec<u8>, tgas| step(off, lab(i, s), signer, y, vec![fc(m, args, tgas, 0)], How::Main);
    let mut v = vec![
        yc(0, 0, "create-resumed-cross-shard-buffered", y, "create", vec![1], 100),
        yc(0, 1, "create-timeout-under-congestion", y, "create", vec![2], 100),
        yc(0, 2, "create-timeout-under-congestion-note", y, "create", vec![0x83], 100),
        yc(0, 3, "create-resumed-locally-under-congestion", y, "create", vec![4], 100),
        yc(0, 4, "create-resumed-after-own-shard-flood", y, "create", vec![5], 100),
        yc(0, 5, "create-resumed-cross-shard-small", y, "create", vec![6], 100),
        yc(0, 6, "create-resume-races-deferred-timeout", y, "create", vec![9], 100),
        yc(6, 7, "resume-local-under-congestion", y, "resume", resume_args(4, b"under-congestion", 0), 100),
        yc(6, 8, "create-under-congestion", y, "create", vec![7], 100),
        yc(7, 9, "resume-cross-shard-buffered", "s1xcall", "resume", resume_args(1, b"buffered", 200_000), 100),
        yc(8, 10, "resume-after-own-shard-flood", y, "resume_flood", {
            let mut a = vec![5, 6];
            a.extend(60_000u32.to_le_bytes());
            a.extend(resume_args(0, b"flood", 0)[1..].to_vec());
            a
        }, 200),
        yc(9, 11, "resume-created-under-congestion", y, "resume", resume_args(7, b"created-under-congestion", 0), 100),
        yc(10, 12, "resume-cross-shard-small", "s1xcall", "resume", resume_args(6, b"cross-small", 0), 100),
        yc(12, 13, "create-cross-shard-under-congestion-note", "s1xcall", "create", vec![0x88], 100),
        yc(203, 14, "resume-after-deferred-timeout-due", y, "resume", resume_args(9, b"late-but-first", 0), 100),
    ];
    // two floods: around the early resumes and around the timeouts (creation + 200)
    let mut n = 0;
    for off in (4..=13).chain(194..=205) {
        for j in 0..5 {
            let (signer, label) = if j < 4 { ("s0xburn", "flood-local") } else { ("s2xburn", "flood-cross-shard") };
            v.push(step(off, format!("successor.yield-congestion.flood.{n:03}.{label}"), signer, "s0xburn",
                        vec![fc("burn", vec![16], 100, 0)], How::Main));
            n += 1;
        }
    }
    v
}

/// The curve callback steps: (label, receiver index 0/1, signer cross?, method, args, gas Tgas).
pub struct CurveStep {
    pub label: String,
    pub method: String,
    pub args: Vec<u8>,
    pub tgas: u64,
    pub cross_signer: bool,
    pub receiver_b: bool,
}

pub fn curve_steps() -> &'static [CurveStep] {
    static S: OnceLock<Vec<CurveStep>> = OnceLock::new();
    S.get_or_init(build_curve_steps)
}

fn build_curve_steps() -> Vec<CurveStep> {
    let base = crate::curve_hosts::steps();
    // per host: the first non-empty pos input, the first neg input, the first edge input and the
    // gas-exhaustion input (callback gas = the original step's gas)
    let mut picks: Vec<(&str, String, Vec<u8>, u64)> = Vec::new();
    for &(h, _) in CURVE_HOSTS {
        let of = |class: &str, skip_empty: bool| base.iter().find(|s| s.method == h && s.label.contains(&format!(".{class}."))
            && !(skip_empty && s.args.is_empty()) && s.tgas >= 100);
        for (class, skip) in [("pos", true), ("neg", false), ("edge", false)] {
            if let Some(s) = of(class, skip) {
                let case = s.label.rsplit('.').next().unwrap().to_string();
                picks.push((h, format!("{class}.{case}"), s.args.clone(), 100));
            }
        }
        if let Some(s) = base.iter().find(|s| s.method == h && s.tgas < 100) {
            picks.push((h, "neg.gas_at_element_charge".into(), s.args.clone(), s.tgas));
        }
    }
    let other = |b: bool| if b { "s0xcurve" } else { "s2xcurve" };
    let mut out: Vec<CurveStep> = Vec::new();
    fn push(out: &mut Vec<CurveStep>, method: &str, host: &str, variant: &str, case: &str, args: Vec<u8>, tgas: u64) {
        let i = out.len();
        out.push(CurveStep {
            label: format!("successor.curve-callbacks.{i:03}.{host}.{variant}.{case}"),
            method: method.into(),
            args,
            tgas,
            cross_signer: i % 3 == 2,
            receiver_b: i % 2 == 1,
        });
    }
    let disp = |g: u64, m: &str, rest: &[u8]| {
        let mut a = vec![g as u8, m.len() as u8];
        a.extend(m.as_bytes());
        a.extend_from_slice(rest);
        a
    };
    let mut slot = 0u8;
    for (h, case, args, g) in &picks {
        let reg = !matches!(*h, "p256_verify" | "ecrecover");
        let g = (*g).min(150);
        push(&mut out, "then", h, "then-args", case, disp(g, h, args), 300);
        push(&mut out, "then", h, "then-result-memory", case, disp(g, &format!("{h}_rm"), args), 300);
        if reg {
            push(&mut out, "then", h, "then-result-register", case, disp(g, &format!("{h}_rr"), args), 300);
        }
        push(&mut out, "then2", h, "chain3-result-memory", case, disp(g, &format!("{h}_rm"), args), 300);
        push(&mut out, "yield", h, "yield-args", case, disp(g, h, args), 300);
        push(&mut out, "yield", h, "yield-payload-memory", case, disp(g, &format!("{h}_rm"), args), 300);
        if reg {
            push(&mut out, "yield", h, "yield-payload-register", case, disp(g, &format!("{h}_rr"), args), 300);
        }
        // thenx: [g][mlen][method][olen][other][args] — the receiver is fixed below, so the
        // "other" account is the opposite contract account (filled in at submission)
        let i = out.len();
        let o = other(i % 2 == 1);
        let mut rest = vec![o.len() as u8];
        rest.extend(o.as_bytes());
        rest.extend(args);
        push(&mut out, "thenx", h, "then-after-cross-shard-promise", case, disp(g, &format!("{h}_rm"), &rest), 300);
    }
    // register / out-of-bounds input for the BLS writers (W05 remaining rows), direct calls
    for &(h, k) in CURVE_HOSTS {
        if k != 1 || h == "bls12381_p1_sum" {
            continue;
        }
        for (_, case, args, _) in picks.iter().filter(|p| p.0 == h && !p.1.contains("gas_at")) {
            push(&mut out, &format!("{h}_reg"), h, "register-input", case, args.clone(), 100);
        }
        push(&mut out, &format!("{h}_oob"), h, "memory-oob", "neg.memory_oob", vec![], 100);
        push(&mut out, &format!("{h}_rr"), h, "direct-register-without-promise", "neg.no_promise_result", vec![], 100);
    }
    // yields resumed by a later cross-shard transaction with the host input as payload
    let mut later = Vec::new();
    for (h, case, args, g) in picks.iter().filter(|p| p.1.starts_with("pos") || p.1.starts_with("neg.")).filter(|p| !p.1.contains("gas_at")).take(10) {
        let mut a = vec![slot, (*g).min(150) as u8, (h.len() + 3) as u8];
        a.extend(format!("{h}_rm").as_bytes());
        push(&mut out, "yslot", h, "yield-resumed-later", case, a, 300);
        let mut r = vec![slot];
        r.extend(args);
        later.push((h.to_string(), case.clone(), r, out.len() - 1));
        slot += 1;
    }
    for (h, case, r, i) in later {
        let receiver_b = out[i].receiver_b;
        let n = out.len();
        out.push(CurveStep {
            label: format!("successor.curve-callbacks.{n:03}.{h}.resume-later-cross-shard.{case}"),
            method: "rslot".into(),
            args: r,
            tgas: 100,
            cross_signer: true,
            receiver_b,
        });
    }
    out
}

fn curve_callbacks() -> Vec<Step> {
    let per_height = 4;
    curve_steps()
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let recv = if c.receiver_b { "s2xcurve" } else { "s0xcurve" };
            let signer = if c.cross_signer { "s1xccall" } else { recv };
            // the later resumes go after every other step
            let off = (i / per_height) as u64;
            step(off, c.label.clone(), signer, recv, vec![fc(&c.method, c.args.clone(), c.tgas, 0)], How::Main)
        })
        .collect()
}

fn genesis_tx() -> Vec<Step> {
    let lab = |i: usize, s: &str| format!("successor.genesis-tx.{i:02}.{s}");
    let emit = |mode: u8, targets: &[(&str, &str)]| {
        let mut a = vec![mode, targets.len() as u8];
        for (t, m) in targets {
            a.push(t.len() as u8);
            a.extend(t.as_bytes());
            a.push(m.len() as u8);
            a.extend(m.as_bytes());
        }
        a
    };
    let gk = gas_key(&acct("s3gx"), "g0");
    let mut v = Vec::new();
    for round in 0..3u64 {
        let i = 20 * round as usize;
        let k = round as u8;
        v.extend([
            step(round, lab(i, "emit-cross-shard-then"), "s0gx", "s0gx", vec![fc("emit", emit(2, &[("s1gx", "noop"), ("s2gx", "fail")]), 100, 0)], How::Main),
            step(round, lab(i + 1, "emit-then-panic"), "s1gx", "s1gx", vec![fc("emit", emit(1, &[("s2gx", "noop")]), 100, 0)], How::Main),
            step(round, lab(i + 2, "yield-create"), "s2gx", "s2gx", vec![fc("create", vec![k], 100, 0)], How::Main),
            step(round, lab(i + 3, "cross-shard-call-with-deposit"), "s3gx", "s0gx", vec![fc("noop", vec![k], 20, NEAR)], How::Main),
            step(round, lab(i + 4, "cross-shard-failing-call-refund"), "s3gx", "s1gx", vec![fc("fail", vec![], 20, NEAR)], How::Main),
            step(round, lab(i + 5, "transfers-multi-action"), "s0gx", "s2gx", vec![tr(NEAR), tr(2)], How::Main),
            step(round, lab(i + 6, "create-sub-account-other-shard"), "s1gx", &format!("s3g{k}.s1gx"),
                 vec![Action::CreateAccount(CreateAccountAction {}), tr(5 * NEAR), add_full(InMemorySigner::test_signer(&acct(&format!("s3g{k}.s1gx"))).public_key())], How::Main),
            step(round, lab(i + 7, "deploy-and-call"), "s3gx", "s3gx", vec![Action::DeployContract(DeployContractAction { code: xfam_wasm().to_vec() }), fc("init_ok", vec![k], 20, 0)], How::Main),
            step(round, lab(i + 8, "add-and-fund-gas-key"), "s3gx", "s3gx", vec![add_gas_key(gas_key(&acct("s3gx"), &format!("g{k}")).public_key(), 2), fund(gas_key(&acct("s3gx"), &format!("g{k}")).public_key(), NEAR)], How::Main),
            step(round, lab(i + 9, "state-init-missing-code"), "s2gx", "s2gx", vec![], How::Main),
            step(round, lab(i + 10, "burn-cross-shard"), "s1gx", "s0gx", vec![fc("burn", vec![2], 100, 0)], How::Main),
            step(round, lab(i + 11, "delete-missing-key"), "s0gx", "s0gx", vec![del_key(gas_key(&acct("s0gx"), "absent").public_key())], How::Main),
        ]);
    }
    let _ = gk;
    // state init: filled in at submission (the receiver is the derived account id)
    for x in v.iter_mut() {
        if x.label.contains("state-init-missing-code") {
            let (r, a) = state_init(GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(b"absent global code")), vec![(b"k".to_vec(), x.label.clone().into_bytes())], NEAR);
            x.receiver = r;
            x.actions = vec![a];
            x.describe = describe_action(&x.actions[0]);
        }
    }
    v
}

fn state_init(code: GlobalContractIdentifier, data: Vec<(Vec<u8>, Vec<u8>)>, deposit: u128) -> (AccountId, Action) {
    use near_primitives_core::deterministic_account_id::{DeterministicAccountStateInit, DeterministicAccountStateInitV1};
    let state_init = DeterministicAccountStateInit::V1(DeterministicAccountStateInitV1 { code, data: BTreeMap::from_iter(data) });
    let receiver = near_primitives::utils::derive_near_deterministic_account_id(&state_init);
    (receiver, Action::DeterministicStateInit(Box::new(DeterministicStateInitAction { state_init, deposit: Balance::from_yoctonear(deposit) })))
}

fn gaskey_target() -> Vec<Step> {
    let lab = |i: usize, s: &str| format!("successor.gaskey-target.{i:02}.{s}");
    let r = acct("s2gkr");
    let g = gas_key(&r, "g").public_key();
    let h = gas_key(&r, "h").public_key();
    let k4 = gas_key(&r, "k4").public_key();
    let ed_r = InMemorySigner::test_signer(&r).public_key();
    let absent = gas_key(&r, "absent").public_key();
    let sub = |n: &str| acct(&format!("{n}.s0gkt"));
    let sk = |n: &str, t: &str| gas_key(&sub(n), t).public_key();
    let create = |n: &str, rest: Vec<Action>| {
        let mut a = vec![Action::CreateAccount(CreateAccountAction {}), tr(5 * NEAR), add_full(InMemorySigner::test_signer(&sub(n)).public_key())];
        a.extend(rest);
        a
    };
    let emit = |targets: &[(&str, &str)]| {
        let mut a = vec![0u8, targets.len() as u8];
        for (t, m) in targets {
            a.push(t.len() as u8);
            a.extend(t.as_bytes());
            a.push(m.len() as u8);
            a.extend(m.as_bytes());
        }
        a
    };
    let gk = |i| How::GasKey(["g", "h", "k4"][i], 0);
    vec![
        step(0, lab(0, "add-gas-keys"), "s2gkr", "s2gkr", vec![add_gas_key(g.clone(), 3), add_gas_key(h.clone(), 1), add_gas_key(k4.clone(), 1)], How::Main),
        step(4, lab(1, "fund-cross-shard"), "s0gkt", "s2gkr", vec![fund(g.clone(), 5 * NEAR)], How::Main),
        step(4, lab(2, "transfer-and-fund-cross-shard"), "s0gkt", "s2gkr", vec![tr(NEAR), fund(h.clone(), NEAR / 2), fund(k4.clone(), NEAR / 2)], How::Main),
        step(4, lab(3, "fund-missing-key-cross-shard"), "s0gkt", "s2gkr", vec![fund(absent.clone(), NEAR)], How::Main),
        step(4, lab(4, "fund-regular-key-cross-shard"), "s0gkt", "s2gkr", vec![fund(ed_r.clone(), NEAR)], How::Main),
        step(4, lab(5, "ordinary-transfer-same-chunk"), "s0gkt", "s2gkr", vec![tr(3 * NEAR)], How::Main),
        step(4, lab(6, "ordinary-call-same-chunk"), "s0gkt", "s1gkc", vec![fc("noop", vec![6], 20, 7)], How::Main),
        step(11, lab(7, "gas-key-transfer-out-index0"), "s2gkr", "s3gks", vec![tr(NEAR)], How::GasKey("g", 0)),
        step(11, lab(8, "gas-key-call-index1"), "s2gkr", "s1gkc", vec![fc("noop", vec![8], 20, 0)], How::GasKey("g", 1)),
        step(11, lab(9, "gas-key-failing-call-deposit-index2"), "s2gkr", "s1gkc", vec![fc("fail", vec![], 20, NEAR)], How::GasKey("g", 2)),
        step(11, lab(10, "gas-key-transfer-out-index0-second"), "s2gkr", "s0gkt", vec![tr(2)], How::GasKey("g", 0)),
        step(11, lab(11, "ordinary-receipts-same-chunk"), "s0gkt", "s2gkr", vec![tr(11), fund(g.clone(), 11)], How::Main),
        step(15, lab(12, "fund-and-spend-same-chunk-fund"), "s0gkt", "s2gkr", vec![fund(g.clone(), NEAR)], How::Main),
        step(15, lab(13, "fund-and-spend-same-chunk-spend"), "s2gkr", "s1gkc", vec![fc("emit", emit(&[("s3gks", "noop")]), 40, 0)], How::GasKey("g", 1)),
        step(15, lab(14, "withdraw-partial"), "s2gkr", "s2gkr", vec![withdraw(g.clone(), NEAR)], How::Main),
        step(19, lab(15, "withdraw-too-much"), "s2gkr", "s2gkr", vec![withdraw(g.clone(), 1000 * NEAR)], How::Main),
        step(19, lab(16, "delete-gas-key-small-balance"), "s2gkr", "s2gkr", vec![del_key(h.clone())], How::Main),
        step(19, lab(17, "refund-to-deleted-gas-key-call"), "s2gkr", "s1gkc", vec![fc("fail", vec![], 20, NEAR / 10)], gk(2)),
        step(19, lab(18, "refund-to-deleted-gas-key-delete"), "s2gkr", "s2gkr", vec![del_key(k4.clone())], How::Main),
        step(23, lab(19, "create-fund-delete-small-cross-shard"), "s0gkt", "s3gkd.s0gkt",
             create("s3gkd", vec![add_gas_key(sk("s3gkd", "k1"), 2), fund(sk("s3gkd", "k1"), 1000), del_key(sk("s3gkd", "k1"))]), How::Main),
        step(23, lab(20, "create-fund-withdraw-cross-shard"), "s0gkt", "s2gke.s0gkt",
             create("s2gke", vec![add_gas_key(sk("s2gke", "k2"), 2), fund(sk("s2gke", "k2"), 2 * NEAR), withdraw(sk("s2gke", "k2"), NEAR)]), How::Main),
        step(23, lab(21, "create-fund-delete-too-much-cross-shard"), "s0gkt", "s1gkf.s0gkt",
             create("s1gkf", vec![add_gas_key(sk("s1gkf", "k3"), 1), fund(sk("s1gkf", "k3"), 3 * NEAR), del_key(sk("s1gkf", "k3"))]), How::Main),
        step(23, lab(22, "create-fund-delete-account-cross-shard"), "s0gkt", "s3gkx.s0gkt",
             create("s3gkx", vec![add_gas_key(sk("s3gkx", "k5"), 1), fund(sk("s3gkx", "k5"), 1000),
                                  Action::DeleteAccount(DeleteAccountAction { beneficiary_id: acct("s0gkt") })]), How::Main),
        step(23, lab(23, "create-fund-delete-account-too-much-cross-shard"), "s0gkt", "s2gky.s0gkt",
             create("s2gky", vec![add_gas_key(sk("s2gky", "k6"), 1), fund(sk("s2gky", "k6"), 2 * NEAR),
                                  Action::DeleteAccount(DeleteAccountAction { beneficiary_id: acct("s0gkt") })]), How::Main),
        step(28, lab(24, "new-account-gas-key-tx-cross-shard"), "s2gke.s0gkt", "s0gkt", vec![tr(24)], How::GasKey("k2", 0)),
        step(28, lab(25, "new-account-gas-key-call-cross-shard"), "s2gke.s0gkt", "s1gkc", vec![fc("noop", vec![25], 20, 0)], How::GasKey("k2", 1)),
        step(32, lab(26, "withdraw-zero-then-delete-funded"), "s2gkr", "s2gkr", vec![withdraw(g.clone(), 0), del_key(g.clone())], How::Main),
        step(36, lab(28, "withdraw-all-then-delete"), "s2gkr", "s2gkr", vec![withdraw(g.clone(), WITHDRAW_ALL), del_key(g.clone())], How::Main),
        step(40, lab(29, "fund-deleted-gas-key-cross-shard"), "s0gkt", "s2gkr", vec![fund(g.clone(), NEAR)], How::Main),
        step(32, lab(27, "gas-key-call-emits-before-delete"), "s2gkr", "s1gkc", vec![fc("emit", emit(&[("s3gks", "noop"), ("s0gkt", "noop")]), 60, 0)], How::GasKey("g", 2)),
    ]
}

fn rollback_refund() -> Vec<Step> {
    let code = xfam_wasm().to_vec();
    let hash_id = GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(&code));
    let acct_id = GlobalContractIdentifier::AccountId(acct("s0rbg"));
    let absent = GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(b"absent global code"));
    let lab = |i: usize, s: &str| format!("successor.rollback-refund.{i:02}.{s}");
    let emit = |mode: u8, targets: &[(&str, &str)]| {
        let mut a = vec![mode, targets.len() as u8];
        for (t, m) in targets {
            a.push(t.len() as u8);
            a.extend(t.as_bytes());
            a.push(m.len() as u8);
            a.extend(m.as_bytes());
        }
        a
    };
    let use_g = |id: GlobalContractIdentifier| Action::UseGlobalContract(Box::new(UseGlobalContractAction { contract_identifier: id }));
    let mut v = vec![
        step(0, lab(0, "deploy-global-hash"), "s0rbg", "s0rbg", vec![Action::DeployGlobalContract(DeployGlobalContractAction { code: code.clone().into(), deploy_mode: GlobalContractDeployMode::CodeHash })], How::Main),
        step(1, lab(1, "deploy-global-account"), "s0rbg", "s0rbg", vec![Action::DeployGlobalContract(DeployGlobalContractAction { code: code.clone().into(), deploy_mode: GlobalContractDeployMode::AccountId })], How::Main),
        step(9, lab(2, "use-global-account-init"), "s0rbu", "s0rbu", vec![use_g(acct_id.clone()), fc("init_ok", vec![2], 20, 0)], How::Main),
    ];
    let mut i = 3;
    for k in 0..4u8 {
        let off = 15 + 6 * k as u64;
        let id = if k % 2 == 0 { acct_id.clone() } else { hash_id.clone() };
        let mut push = |name: &str, signer: &str, receiver: AccountId, actions: Vec<Action>| {
            let describe = actions.iter().map(describe_action).collect::<Vec<_>>().join(", ");
            v.push(Step { off, label: lab(i, &format!("r{k}.{name}")), signer: acct(signer), receiver, actions, how: How::Main, describe });
            i += 1;
        };
        let s = "s1rbs";
        let (r, a) = state_init(absent.clone(), vec![(b"k".to_vec(), vec![k])], NEAR);
        push("state-init-missing-global-code", s, r, vec![a]);
        let (r, a) = state_init(hash_id.clone(), vec![(b"k".to_vec(), vec![k, 1])], NEAR);
        push("state-init-then-emit", s, r, vec![a, fc("emit", emit(2, &[("s2rbt", "noop"), ("s3rbt", "fail")]), 60, 0)]);
        let (r, a) = state_init(hash_id.clone(), vec![(b"big".to_vec(), vec![k; 4096])], 0);
        push("state-init-insufficient-deposit", s, r, vec![a]);
        let n = format!("s0z{k}.s1rbs");
        push("create-use-global-init-fail", s, acct(&n),
             vec![Action::CreateAccount(CreateAccountAction {}), tr(2 * NEAR), use_g(id.clone()), fc("init_fail", vec![k], 20, 0)]);
        push("emit-then-panic", s, acct("s0rbu"), vec![fc("emit", emit(1, &[("s2rbt", "noop"), ("s3rbt", "noop")]), 60, NEAR)]);
        push("emit-to-failing-callee", s, acct("s0rbu"), vec![fc("emit", emit(2, &[("s2rbt", "fail"), ("s3rbt", "noop")]), 60, NEAR)]);
        let n = format!("s0y{k}.s1rbs");
        push("create-deploy-init-ok", s, acct(&n),
             vec![Action::CreateAccount(CreateAccountAction {}), tr(3 * NEAR), Action::DeployContract(DeployContractAction { code: code.clone() }),
                  fc("init_ok", vec![k], 20, 0), add_full(InMemorySigner::test_signer(&acct(&n)).public_key())]);
        let n = format!("s0w{k}.s1rbs");
        push("create-deploy-init-fail", s, acct(&n),
             vec![Action::CreateAccount(CreateAccountAction {}), tr(3 * NEAR), Action::DeployContract(DeployContractAction { code: code.clone() }),
                  fc("init_fail", vec![k], 20, 0)]);
        push("call-fail-deposit-refund", s, acct("s0rbu"), vec![fc("fail", vec![], 20, NEAR)]);
        push("ordinary-transfer", s, acct("s0rbu"), vec![tr(NEAR + k as u128)]);
        // local composition on the target shard itself (receipts applied in the inclusion chunk)
        push("local-emit-then-panic", "s0rbu", acct("s0rbu"), vec![fc("emit", emit(1, &[("s2rbt", "noop")]), 60, NEAR)]);
        push("local-use-global-call-emit", "s0rbu", acct("s0rbu"), vec![fc("emit", emit(2, &[("s3rbt", "fail")]), 60, 0)]);
    }
    v
}

/// `curve-yield-timeout` (item 10, W05/W07): yields created by `yslot` and never resumed, so the
/// runtime's timeout (200 blocks after creation, `PromiseResult::Failed`) runs the callback, which
/// is a curve host method. Per host and input (the `curve-callbacks` picks: first pos / neg / edge
/// input and the gas-exhaustion input with its own callback gas) the callback takes its input from
/// the yield arguments in memory (`H`) and, for the writer and pairing hosts, in a register
/// (`H_reg`); from the failed promise result in memory (`H_rm`) and in a register (`H_rr`). Slots
/// are distinct per receiver account. Four steps per height, so the timeouts of one height share a
/// chunk.
fn curve_yield_timeout() -> Vec<Step> {
    let base = crate::curve_hosts::steps();
    let mut picks: Vec<(&str, u8, String, Vec<u8>, u64)> = Vec::new();
    for &(h, k) in CURVE_HOSTS {
        let of = |class: &str, skip_empty: bool| base.iter().find(|s| s.method == h && s.label.contains(&format!(".{class}."))
            && !(skip_empty && s.args.is_empty()) && s.tgas >= 100);
        for (class, skip) in [("pos", true), ("neg", false), ("edge", false)] {
            if let Some(s) = of(class, skip) {
                let case = s.label.rsplit('.').next().unwrap().to_string();
                picks.push((h, k, format!("{class}.{case}"), s.args.clone(), 100));
            }
        }
        if let Some(s) = base.iter().find(|s| s.method == h && s.tgas < 100) {
            picks.push((h, k, "neg.gas_at_element_charge".into(), s.args.clone(), s.tgas));
        }
    }
    let mut v = Vec::new();
    let mut slots = [0u8; 2];
    let per_height = 4;
    for (h, k, case, args, g) in &picks {
        let gas_case = case.contains("gas_at");
        let mut variants = vec![("args-memory", h.to_string())];
        if !gas_case {
            variants.push(("failed-result-memory", format!("{h}_rm")));
            if *k <= 2 {
                variants.push(("args-register", format!("{h}_reg")));
                variants.push(("failed-result-register", format!("{h}_rr")));
            }
        }
        for (vname, method) in variants {
            let i = v.len();
            let rb = i % 2;
            let recv = ["s0xcurve", "s2xcurve"][rb];
            let signer = if i % 3 == 2 { "s1xccall" } else { recv };
            let slot = slots[rb];
            slots[rb] += 1;
            let mut a = vec![slot, (*g).min(150) as u8, method.len() as u8];
            a.extend(method.as_bytes());
            a.extend(args);
            let label = format!("successor.curve-yield-timeout.{i:03}.{h}.{vname}.{case}");
            v.push(step((i / per_height) as u64, label, signer, recv, vec![fc("yslot", a, 300, 0)], How::Main));
        }
    }
    v
}

/// `state-init-emit` (item 10, W07): a deterministic state init followed, in the same receipt or a
/// later one, by an `emit` that succeeds. The `rollback-refund` composition could not reach this:
/// the derived account holds only its storage stake after the init, so the 1,000-yocto promise
/// amounts failed with `BalanceExceeded`. Here the account is paid first: by the emitting call's
/// own deposit, by a `Transfer` between the init and the call, or by a separate later transaction.
/// Global code by hash and by account id; local and cross-shard targets; with and without a
/// `promise_then` callback, and with a failing target (the callback sees the failure). The unfunded
/// composition is kept as a control step.
fn state_init_emit() -> Vec<Step> {
    let code = xfam_wasm().to_vec();
    let hash_id = GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(&code));
    let acct_id = GlobalContractIdentifier::AccountId(acct("s0rbg"));
    let lab = |i: usize, s: &str| format!("successor.state-init-emit.{i:02}.{s}");
    let emit = |mode: u8, targets: &[(&str, &str)]| {
        let mut a = vec![mode, targets.len() as u8];
        for (t, m) in targets {
            a.push(t.len() as u8);
            a.extend(t.as_bytes());
            a.push(m.len() as u8);
            a.extend(m.as_bytes());
        }
        a
    };
    let mut v = vec![
        step(0, lab(0, "deploy-global-hash"), "s0rbg", "s0rbg", vec![Action::DeployGlobalContract(DeployGlobalContractAction { code: code.clone().into(), deploy_mode: GlobalContractDeployMode::CodeHash })], How::Main),
        step(1, lab(1, "deploy-global-account"), "s0rbg", "s0rbg", vec![Action::DeployGlobalContract(DeployGlobalContractAction { code: code.clone().into(), deploy_mode: GlobalContractDeployMode::AccountId })], How::Main),
    ];
    let mut i = 2;
    for k in 0..4u8 {
        let off = 15 + 8 * k as u64;
        let id = |b: bool| if b { hash_id.clone() } else { acct_id.clone() };
        let even = k % 2 == 0;
        let mut push = |off: u64, name: &str, signer: &str, receiver: AccountId, actions: Vec<Action>| {
            let describe = actions.iter().map(describe_action).collect::<Vec<_>>().join(", ");
            v.push(Step { off, label: lab(i, &format!("r{k}.{name}")), signer: acct(signer), receiver, actions, how: How::Main, describe });
            i += 1;
        };
        let s = "s1rbs";
        let (r, a) = state_init(id(even), vec![(b"k".to_vec(), vec![k, 10])], NEAR);
        push(off, "init-emit-deposit-then-cross-shard", s, r, vec![a, fc("emit", emit(2, &[("s2rbt", "noop"), ("s3rbt", "noop")]), 60, NEAR)]);
        let (r, a) = state_init(id(!even), vec![(b"k".to_vec(), vec![k, 11])], NEAR);
        push(off, "init-transfer-emit-cross-shard", s, r, vec![a, tr(NEAR), fc("emit", emit(0, &[("s2rbt", "noop")]), 60, 0)]);
        let (r, a) = state_init(id(even), vec![(b"k".to_vec(), vec![k, 12])], NEAR);
        push(off, "init-emit-deposit-failing-target-then", s, r, vec![a, fc("emit", emit(2, &[("s3rbt", "fail")]), 60, NEAR)]);
        let (r, a) = state_init(id(!even), vec![(b"k".to_vec(), vec![k, 13]), (b"big".to_vec(), vec![k; 512])], 2 * NEAR);
        let own = r.to_string();
        push(off, "init-data-emit-deposit-self-and-other", s, r, vec![a, fc("emit", emit(0, &[(own.as_str(), "noop"), ("s3xnote", "noop")]), 60, NEAR)]);
        let (r, a) = state_init(id(even), vec![(b"k".to_vec(), vec![k, 14])], NEAR);
        push(off, "init-only", s, r.clone(), vec![a]);
        push(off + 4, "later-emit-deposit-then", s, r.clone(), vec![fc("emit", emit(2, &[("s2rbt", "noop")]), 60, NEAR)]);
        push(off + 4, "later-transfer-and-emit", "s0rbu", r, vec![tr(NEAR), fc("emit", emit(0, &[("s3rbt", "noop"), ("s2rbt", "noop")]), 60, 0)]);
        let (r, a) = state_init(id(!even), vec![(b"k".to_vec(), vec![k, 15])], NEAR);
        push(off, "init-emit-no-funds-control", s, r, vec![a, fc("emit", emit(0, &[("s2rbt", "noop")]), 60, 0)]);
        push(off, "ordinary-transfer", s, acct("s0rbu"), vec![tr(NEAR + k as u128)]);
    }
    v
}

/// `runtime-errors` (W03): calls into the `src/rterr.rs` contracts directly, across shards, from
/// `promise_then` chains (the callback records the callee's promise status), with too little gas
/// for the loading fee, with a missing method, in multi-action receipts, and right after an
/// in-chain deployment (in the same receipt, so a failed call rolls the deployment back, and in a
/// later receipt, so the code is served from the committed state).
fn runtime_errors() -> Vec<Step> {
    let mut v: Vec<Step> = Vec::new();
    let mut i = 0usize;
    let mut push = |v: &mut Vec<Step>, off: u64, name: &str, signer: &str, receiver: &str, actions: Vec<Action>| {
        v.push(step(off, format!("successor.runtime-errors.{i:02}.{name}"), signer, receiver, actions, How::Main));
        i += 1;
    };
    let gas = |method: &str, g: u64, deposit: u128| {
        Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: method.into(),
            args: vec![],
            gas: Gas::from_gas(g),
            deposit: Balance::from_yoctonear(deposit),
        }))
    };
    let main = |deposit: u128| fc("main", vec![], 20, deposit);
    let emit = |targets: &[(&str, &str)]| {
        let mut a = vec![2u8, targets.len() as u8];
        for (t, m) in targets {
            a.push(t.len() as u8);
            a.extend(t.as_bytes());
            a.push(m.len() as u8);
            a.extend(m.as_bytes());
        }
        fc("emit", a, 60, 0)
    };
    // direct calls into the genesis contracts (each signed by the contract account itself)
    for (off, acc) in [(0, "s0rtload"), (0, "s1rtfita"), (0, "s1rtovra"), (1, "s2rtfitb"), (1, "s2rtovrb"),
                       (1, "s3rtfitc"), (1, "s3rtovrc"), (2, "s0rtcombo"), (2, "s1rtlink"), (2, "s2rtbadty")] {
        push(&mut v, off, &format!("call.{acc}"), acc, acc, vec![main(NEAR)]);
    }
    // cross-shard: a transaction from s3rtx, and promise chains whose callback records the status
    push(&mut v, 3, "cross-shard-call.s0rtload", "s3rtx", "s0rtload", vec![main(NEAR)]);
    push(&mut v, 3, "cross-shard-call.s1rtlink", "s3rtx", "s1rtlink", vec![main(NEAR)]);
    push(&mut v, 4, "emit-then.s0rtload", "s3rtx", "s3rtx", vec![emit(&[("s0rtload", "main")])]);
    push(&mut v, 5, "emit-then.s1rtlink", "s3rtx", "s3rtx", vec![emit(&[("s1rtlink", "main")])]);
    push(&mut v, 6, "emit-then.s1rtfita", "s3rtx", "s3rtx", vec![emit(&[("s1rtfita", "main")])]);
    push(&mut v, 7, "emit-then.s0rtcombo+s2rtovrb", "s3rtx", "s3rtx", vec![emit(&[("s0rtcombo", "main"), ("s2rtovrb", "main")])]);
    push(&mut v, 8, "emit-then.s2rtbadty+s3rtfitc", "s3rtx", "s3rtx", vec![emit(&[("s2rtbadty", "main"), ("s3rtfitc", "main")])]);
    // order: loading precedes method resolution; linking precedes it as well
    push(&mut v, 5, "missing-method.s0rtload", "s0rtload", "s0rtload", vec![fc("absent", vec![], 20, 0)]);
    push(&mut v, 5, "missing-method.s1rtlink", "s1rtlink", "s1rtlink", vec![fc("absent", vec![], 20, 0)]);
    push(&mut v, 6, "missing-method.s3rtovrc", "s3rtovrc", "s3rtovrc", vec![fc("absent", vec![], 20, 0)]);
    // gas below the contract-loading fee
    push(&mut v, 7, "low-gas.s0rtload", "s0rtload", "s0rtload", vec![gas("main", 1_000_000, 0)]);
    push(&mut v, 7, "low-gas.s1rtlink", "s1rtlink", "s1rtlink", vec![gas("main", 1_000_000, 0)]);
    push(&mut v, 8, "low-gas.s1rtfita", "s1rtfita", "s1rtfita", vec![gas("main", 1_000_000, 0)]);
    push(&mut v, 8, "low-gas.s2rtovrb", "s2rtovrb", "s2rtovrb", vec![gas("main", 1_000_000, 0)]);
    // multi-action receipts: the failing call stops the receipt and rolls back earlier actions
    push(&mut v, 9, "transfer-then-call.s1rtovra", "s3rtx", "s1rtovra", vec![tr(NEAR), main(0)]);
    push(&mut v, 9, "call-then-transfer.s0rtload", "s3rtx", "s0rtload", vec![main(0), tr(NEAR)]);
    push(&mut v, 10, "call-call.s2rtovrb", "s2rtovrb", "s2rtovrb", vec![main(0), main(0)]);
    push(&mut v, 10, "call-call.s1rtfita", "s1rtfita", "s1rtfita", vec![main(0), main(0)]);
    push(&mut v, 11, "transfer-then-call.s1rtlink", "s3rtx", "s1rtlink", vec![tr(NEAR), main(0)]);
    // in-chain deployments: deploy+call (one receipt), deploy alone, then a call
    let mut deployed: Vec<&str> = crate::rterr::IMPORTS.iter().map(|(n, _)| *n).collect();
    deployed.extend(["rtload", "rtload2", "rtcombo", "rtfitunk", "rtfita", "rtovrc"]);
    let deps = ["s0rtdep", "s1rtdep", "s2rtdep", "s3rtdep"];
    for (k, name) in deployed.iter().enumerate() {
        let acc = deps[k % deps.len()];
        let base = 12 + 9 * (k / deps.len()) as u64;
        let code = crate::rterr::code(name).to_vec();
        push(&mut v, base, &format!("deploy-call.{name}.{acc}"), acc, acc,
             vec![Action::DeployContract(DeployContractAction { code: code.clone() }), main(1000)]);
        push(&mut v, base + 3, &format!("deploy.{name}.{acc}"), acc, acc,
             vec![Action::DeployContract(DeployContractAction { code })]);
        push(&mut v, base + 6, &format!("call-deployed.{name}.{acc}"), "s3rtx", acc, vec![main(1000)]);
    }
    v
}

/// `host-rows`: every host that no other fixture calls, and the gas-key / global / state-init
/// promise hosts, called by transactions on dedicated accounts (labels say what was submitted):
/// `current_contract_code` on a local-code account, on accounts using a global contract by hash
/// and by account id, and right after an in-receipt deploy; `refund_to_account_id` directly, across
/// shards and from a callee whose receipt carries a refund-to account; `promise_set_refund_to` on a
/// transfer to an absent account (the deposit refund goes to the refund-to account), on a callee,
/// with an invalid promise index, on a joint promise, with an invalid and an absent refund account;
/// the three deprecated `storage_iter_*` hosts (a trap) next to a call that only writes; `gas(k)`
/// for k = 0, 1000, 23·10⁶ and 24.4·10⁶ (below / above 20 Tgas prepaid), 300,000, 10⁶ and u32::MAX
/// (above the 300 Tgas burn limit); the five `kgashost`
/// methods (including a missing and a malformed key); the all-hosts global/state-init call at 300
/// and 20 Tgas, directly and across shards.
fn host_rows() -> Vec<Step> {
    let mut v: Vec<Step> = Vec::new();
    let mut i = 0usize;
    let mut push = |v: &mut Vec<Step>, off: u64, name: &str, signer: &str, receiver: &str, actions: Vec<Action>| {
        v.push(step(off, format!("successor.host-rows.{i:02}.{name}"), signer, receiver, actions, How::Main));
        i += 1;
    };
    let code = hr_code("hostrows").to_vec();
    let use_g = |id: GlobalContractIdentifier| Action::UseGlobalContract(Box::new(UseGlobalContractAction { contract_identifier: id }));
    let hash_id = GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(&code));
    let acct_id = GlobalContractIdentifier::AccountId(acct("s3hrgacc"));
    let psr = |mode: u8, target: &str, refund: &str| {
        let mut a = vec![mode, target.len() as u8];
        a.extend(target.as_bytes());
        a.push(refund.len() as u8);
        a.extend(refund.as_bytes());
        fc("psr", a, 30, 0)
    };
    let gas = |k: u32, tgas: u64| fc("gas", k.to_le_bytes().to_vec(), tgas, 0);
    let pkb = |pk: &PublicKey| borsh::to_vec(pk).unwrap();
    let kg = acct("s2hrkg");
    let (k1, k2, k3) = (gas_key(&kg, "hr1"), gas_key(&kg, "hr2"), gas_key(&kg, "hr3"));
    let absent = gas_key(&kg, "hr-absent");
    let mut fundto = vec![kg.as_str().len() as u8];
    fundto.extend(kg.as_bytes());
    fundto.extend(pkb(&k1.public_key()));
    // current_contract_code: local code; global code by hash / by account id (set up in-chain)
    push(&mut v, 0, "ccc.local", "s0hrow", "s0hrow", vec![fc("ccc", vec![], 20, 0)]);
    push(&mut v, 0, "ccc.local.cross-shard", "s3hrall", "s1hrow", vec![fc("ccc", vec![], 20, 0)]);
    push(&mut v, 1, "deploy-global-hash", "s0hrow", "s0hrow",
         vec![Action::DeployGlobalContract(DeployGlobalContractAction { code: code.clone().into(), deploy_mode: GlobalContractDeployMode::CodeHash })]);
    push(&mut v, 1, "deploy-global-account", "s3hrgacc", "s3hrgacc",
         vec![Action::DeployGlobalContract(DeployGlobalContractAction { code: code.clone().into(), deploy_mode: GlobalContractDeployMode::AccountId })]);
    push(&mut v, 8, "use-global-hash", "s2hrglob", "s2hrglob", vec![use_g(hash_id.clone())]);
    push(&mut v, 8, "use-global-account", "s1hrgbya", "s1hrgbya", vec![use_g(acct_id)]);
    push(&mut v, 8, "use-global-hash+ccc", "s3hrglob", "s3hrglob", vec![use_g(hash_id), fc("ccc", vec![], 20, 0)]);
    push(&mut v, 8, "deploy+ccc", "s1hrdep", "s1hrdep", vec![Action::DeployContract(DeployContractAction { code }), fc("ccc", vec![], 20, 0)]);
    push(&mut v, 14, "ccc.global-hash", "s2hrglob", "s2hrglob", vec![fc("ccc", vec![], 20, 0)]);
    push(&mut v, 14, "ccc.global-account", "s1hrgbya", "s1hrgbya", vec![fc("ccc", vec![], 20, 0)]);
    push(&mut v, 15, "ccc.global-account.cross-shard", "s0hrow", "s1hrgbya", vec![fc("ccc", vec![], 20, 0)]);
    // refund_to_account_id
    push(&mut v, 0, "rta.self", "s0hrow", "s0hrow", vec![fc("rta", vec![], 20, 0)]);
    push(&mut v, 2, "rta.cross-shard", "s1hrow", "s0hrow", vec![fc("rta", vec![], 20, 0)]);
    push(&mut v, 15, "rta.global-hash", "s3hrall", "s2hrglob", vec![fc("rta", vec![], 20, 0)]);
    // promise_set_refund_to
    push(&mut v, 2, "psr.transfer-absent", "s0hrow", "s0hrow", vec![psr(0, "s2hrnone", "s3hrall")]);
    push(&mut v, 2, "psr.transfer-ok", "s0hrow", "s0hrow", vec![psr(0, "s1hrow", "s3hrall")]);
    push(&mut v, 3, "psr.call-rta-other", "s0hrow", "s0hrow", vec![psr(1, "s1hrow", "s2hrkg")]);
    push(&mut v, 3, "psr.call-rta-self", "s1hrow", "s1hrow", vec![psr(1, "s1hrow", "s0hrow")]);
    push(&mut v, 4, "psr.bad-promise-index", "s0hrow", "s0hrow", vec![psr(2, "s1hrow", "s3hrall")]);
    push(&mut v, 4, "psr.joint-promise", "s1hrow", "s1hrow", vec![psr(3, "s0hrow", "s3hrall")]);
    push(&mut v, 5, "psr.invalid-refund-id", "s0hrow", "s0hrow", vec![psr(0, "s1hrow", "A!")]);
    push(&mut v, 5, "psr.absent-refund-and-target", "s1hrow", "s1hrow", vec![psr(0, "s2hrnone", "s3hrnone")]);
    push(&mut v, 16, "psr.global-account", "s1hrgbya", "s1hrgbya", vec![psr(1, "s0hrow", "s3hrall")]);
    // storage_iter_* (deprecated: a trap) and a write-only control
    push(&mut v, 6, "iter-prefix", "s0hrow", "s0hrow", vec![fc("itp", vec![], 20, 0)]);
    push(&mut v, 6, "iter-range", "s1hrow", "s1hrow", vec![fc("itr", vec![], 20, 0)]);
    push(&mut v, 7, "iter-next", "s0hrow", "s0hrow", vec![fc("itn", vec![], 20, 0)]);
    push(&mut v, 7, "iter-none", "s1hrow", "s1hrow", vec![fc("itok", vec![], 20, 0)]);
    push(&mut v, 9, "iter-prefix.cross-shard", "s3hrall", "s1hrow", vec![fc("itp", vec![], 20, 0)]);
    // gas(k): 822,756 gas per unit at PV86
    push(&mut v, 7, "gas.0", "s0hrow", "s0hrow", vec![gas(0, 20)]);
    push(&mut v, 9, "gas.1000", "s1hrow", "s1hrow", vec![gas(1000, 20)]);
    push(&mut v, 9, "gas.23e6", "s1hrow", "s1hrow", vec![gas(23_000_000, 20)]);
    push(&mut v, 9, "gas.over-prepaid", "s0hrow", "s0hrow", vec![gas(24_400_000, 20)]);
    push(&mut v, 10, "gas.1e6.300tgas", "s1hrow", "s1hrow", vec![gas(1_000_000, 300)]);
    push(&mut v, 10, "gas.u32max.300tgas", "s0hrow", "s0hrow", vec![gas(u32::MAX, 300)]);
    push(&mut v, 11, "gas.300000.cross-shard", "s3hrall", "s0hrow", vec![gas(300_000, 300)]);
    // gas-key promise hosts (kgashost)
    push(&mut v, 9, "kg.addfull", "s2hrkg", "s2hrkg", vec![fc("addfull", pkb(&k1.public_key()), 30, 0)]);
    push(&mut v, 9, "kg.addfc", "s2hrkg", "s2hrkg", vec![fc("addfc", pkb(&k2.public_key()), 30, 0)]);
    push(&mut v, 11, "kg.fund", "s2hrkg", "s2hrkg", vec![fc("fund", pkb(&k1.public_key()), 30, 0)]);
    push(&mut v, 11, "kg.addfund", "s2hrkg", "s2hrkg", vec![fc("addfund", pkb(&k3.public_key()), 30, 0)]);
    push(&mut v, 12, "kg.fund-missing", "s2hrkg", "s2hrkg", vec![fc("fund", pkb(&absent.public_key()), 30, 0)]);
    push(&mut v, 12, "kg.addfull-malformed", "s2hrkg", "s2hrkg", vec![fc("addfull", vec![7, 1, 2, 3], 30, 0)]);
    push(&mut v, 13, "kg.fundto", "s2hrkg", "s2hrkg", vec![fc("fundto", fundto, 30, 0)]);
    push(&mut v, 13, "kg.addfull.cross-shard", "s0hrow", "s2hrkg", vec![fc("addfull", pkb(&absent.public_key()), 30, 0)]);
    // global / state-init promise hosts (all-hosts-valid-receivers)
    push(&mut v, 10, "all.300tgas", "s3hrall", "s3hrall", vec![fc("run", vec![], 300, 0)]);
    push(&mut v, 12, "all.20tgas", "s3hrall", "s3hrall", vec![fc("run", vec![], 20, 0)]);
    push(&mut v, 14, "all.300tgas.cross-shard", "s0hrow", "s3hrall", vec![fc("run", vec![], 300, 0)]);
    v
}

// ---------------------------------------------------------------------------------------------
// the driver
// ---------------------------------------------------------------------------------------------

pub struct Driver {
    start: u64,
    steps: Vec<Step>,
    /// steps whose builder returned None (a key or account that does not exist yet): retried
    retry: Vec<(Step, u64)>,
    submitted: Vec<serde_json::Value>,
    used: HashMap<(AccountId, PublicKey, u16), u64>,
}

impl Driver {
    pub fn new() -> Self {
        let (start, steps) = match kind() {
            Some(Kind::YieldCongestion) => (10004, yield_congestion()),
            Some(Kind::CurveCallbacks) if variant().as_deref() == Some("curve-yield-timeout") => (10004, curve_yield_timeout()),
            Some(Kind::CurveCallbacks) => (10004, curve_callbacks()),
            // before the first block: the first chunks after genesis carry these transactions
            Some(Kind::GenesisTx) => (10001, genesis_tx()),
            Some(Kind::GasKeyTarget) => (10004, gaskey_target()),
            Some(Kind::RollbackRefund) if variant().as_deref() == Some("state-init-emit") => (10004, state_init_emit()),
            Some(Kind::RollbackRefund) => (10004, rollback_refund()),
            Some(Kind::RuntimeErrors) => (10004, runtime_errors()),
            Some(Kind::HostRows) => (10004, host_rows()),
            None => (u64::MAX, vec![]),
        };
        if let Some(v) = variant() {
            assert!(matches!(kind(), Some(Kind::CurveCallbacks | Kind::RollbackRefund)), "NEAR_XFAM_VARIANT={v} needs its scenario");
            assert!(matches!(v.as_str(), "curve-yield-timeout" | "state-init-emit"), "unknown NEAR_XFAM_VARIANT={v}");
        }
        Driver { start, steps, retry: vec![], submitted: vec![], used: HashMap::new() }
    }

    fn build(&mut self, w: &mut World, s: &Setup, bh: &CryptoHash, x: &Step) -> Option<SignedTransaction> {
        let mut actions = x.actions.clone();
        for a in actions.iter_mut() {
            if let Action::WithdrawFromGasKey(wd) = a {
                if wd.amount.as_yoctonear() == WITHDRAW_ALL {
                    let k = crate::d2gen::view_key(s, bh, &x.receiver, &wd.public_key)?;
                    wd.amount = k.gas_key_info()?.balance;
                }
            }
        }
        let x = &Step { actions, ..x.clone() };
        match &x.how {
            How::Main => w.plain_tx(s, bh, &x.signer, &x.receiver, x.actions.clone()),
            How::GasKey(tag, idx) => {
                let k = gas_key(&x.signer, tag);
                let cur = view_gk_nonce(s, bh, &x.signer, &k.public_key(), *idx)?;
                let key = (x.signer.clone(), k.public_key(), *idx);
                let n = cur.max(self.used.get(&key).copied().unwrap_or(0)) + 1;
                self.used.insert(key, n);
                let tx = Transaction::V1(TransactionV1 {
                    signer_id: x.signer.clone(),
                    public_key: k.public_key(),
                    nonce: TransactionNonce::from_nonce_and_index(n, *idx),
                    receiver_id: x.receiver.clone(),
                    block_hash: *bh,
                    actions: x.actions.clone(),
                    nonce_mode: NonceMode::Monotonic,
                });
                let sig = k.sign(tx.get_hash_and_size().0.as_ref());
                Some(SignedTransaction::new(sig, tx))
            }
        }
    }

    /// Scenario transactions to submit before the block at `height`.
    pub fn txs(&mut self, w: &mut World, s: &Setup, bh: &CryptoHash, height: u64) -> Vec<(String, SignedTransaction)> {
        let mut out = Vec::new();
        if height < self.start {
            return out;
        }
        let off = height - self.start;
        let mut due: Vec<(Step, u64)> = std::mem::take(&mut self.retry);
        due.extend(self.steps.iter().filter(|x| x.off == off).cloned().map(|x| (x, 0)));
        for (x, tries) in due {
            match self.build(w, s, bh, &x) {
                Some(tx) => {
                    self.submitted.push(json!({"label": x.label, "height": height, "offset": off, "tries": tries,
                        "tx": tx.get_hash().to_string(), "signer": x.signer.to_string(), "receiver": x.receiver.to_string(),
                        "signed_with": format!("{:?}", x.how), "actions": x.describe}));
                    out.push((x.label.clone(), tx));
                }
                None if tries < 12 => self.retry.push((x, tries + 1)),
                None => eprintln!("xfam: step {} could not be built; dropped", x.label),
            }
        }
        out
    }

    pub fn finish(&self, s: &Setup, out: &std::path::Path, chain_idx: usize) {
        let Some(k) = kind() else { return };
        let submitted: Vec<serde_json::Value> = self.submitted.iter().map(|x| {
            let mut x = x.clone();
            let h: CryptoHash = x["tx"].as_str().unwrap().parse().unwrap();
            x["outcomes"] = json!(outcome_tree(s, &h));
            x
        }).collect();
        let v = json!({
            "scenario": format!("{k:?}"), "variant": variant(), "start_height": self.start,
            "shards": shard_map(s),
            "contracts": contracts().iter().map(|(n, c)| json!({"name": n, "hash": CryptoHash::hash_bytes(c).to_string(), "len": c.len()})).collect::<Vec<_>>(),
            "chunk_headers": header_series(s),
            "submitted": submitted,
            "planned": self.steps.iter().map(|x| json!({"offset": x.off, "label": x.label})).collect::<Vec<_>>(),
            "unbuilt": self.retry.iter().map(|x| x.0.label.clone()).collect::<Vec<_>>(),
        });
        std::fs::write(out.join(format!("xfam-{chain_idx}.json")), serde_json::to_string_pretty(&v).unwrap()).unwrap();
    }
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
                        "status": status, "gas_burnt": oc.gas_burnt.as_gas(), "tokens_burnt": oc.tokens_burnt.as_yoctonear().to_string(),
                        "logs": oc.logs, "receipt_ids": oc.receipt_ids.iter().map(|r| r.to_string()).collect::<Vec<_>>()}));
        queue.extend(oc.receipt_ids.iter().copied());
    }
    out
}

fn shard_map(s: &Setup) -> serde_json::Value {
    let c = &s.env.clients[0];
    let tip = c.chain.head().unwrap();
    let layout = c.epoch_manager.get_shard_layout(&tip.epoch_id).unwrap();
    let mut m = serde_json::Map::new();
    for (n, _) in accounts() {
        m.insert(n.into(), json!(layout.account_id_to_shard_id(&acct(n)).to_string()));
    }
    for i in 0..8 {
        m.insert(format!("s{i}"), json!(layout.account_id_to_shard_id(&acct(&format!("s{i}a00"))).to_string()));
    }
    json!(m)
}

/// Per block height and shard: whether the chunk is new, its congestion info (the state after the
/// previous chunk of the shard was applied) and the number of bandwidth requests.
fn header_series(s: &Setup) -> Vec<serde_json::Value> {
    let c = &s.env.clients[0];
    let tip = c.chain.head().unwrap().height;
    let mut out = Vec::new();
    for h in 10000..=tip {
        let Ok(b) = c.chain.get_block_by_height(h) else { continue };
        for ch in b.chunks().iter() {
            let ci = ch.congestion_info();
            let br = match ch.bandwidth_requests() {
                Some(near_primitives::bandwidth_scheduler::BandwidthRequests::V1(r)) => r.requests.len(),
                None => 0,
            };
            out.push(json!({"height": h, "shard": ch.shard_id().to_string(), "new": ch.height_included() == h,
                "delayed_receipts_gas": ci.delayed_receipts_gas().to_string(), "buffered_receipts_gas": ci.buffered_receipts_gas().to_string(),
                "receipt_bytes": ci.receipt_bytes(), "allowed_shard": ci.allowed_shard(), "bandwidth_requests": br,
                "prev_gas_used": ch.prev_gas_used().as_gas()}));
        }
    }
    out
}

// ---------------------------------------------------------------------------------------------
// case writer hooks (crate::d3)
// ---------------------------------------------------------------------------------------------

/// (full mutant set, drop-each-node mutants) forced for a chunk by the active scenario. Relevant
/// chunks: those that ran the scenario contract or carry a scenario transaction; for `genesis-tx`,
/// every genesis-B2 chunk and the chunks up to height 10004. Every genesis-B2 chunk gets the full
/// set with drop-each-node mutants; of the other relevant chunks every `NEAR_XFAM_MUTATE_EVERY`-th
/// (default 1) gets the full set, and every second of those the drop-each-node mutants too. The
/// sample is deterministic in the order chunks are written.
pub fn force_full_mutants(executed: &[serde_json::Value], tx_labels: &[String], new_tx_labels: &[String], b2_genesis: bool, height: u64) -> (bool, bool) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static SEEN: AtomicUsize = AtomicUsize::new(0);
    let Some(k) = kind() else { return (false, false) };
    if k == Kind::GenesisTx && b2_genesis {
        return (true, true);
    }
    let mine = |l: &String| l.starts_with("successor.") && !l.contains(".flood.");
    let ran = executed.iter().any(|e| e["name"] == "xfam" || e["name"] == "xcurve"
        || e["name"].as_str().is_some_and(crate::rterr::is_mine)
        || (k == Kind::HostRows && e["name"].as_str().is_some_and(|n| HR_CONTRACTS.contains(&n))));
    let relevant = match k {
        Kind::GenesisTx => height <= 10004 || tx_labels.iter().any(mine),
        _ => ran || tx_labels.iter().any(mine) || new_tx_labels.iter().any(mine),
    };
    if !relevant {
        return (false, false);
    }
    let every: usize = std::env::var("NEAR_XFAM_MUTATE_EVERY").ok().map(|v| v.parse().expect("NEAR_XFAM_MUTATE_EVERY")).unwrap_or(1).max(1);
    let n = SEEN.fetch_add(1, Ordering::Relaxed);
    let full = n % every == 0;
    (full, full && (n / every) % 2 == 0)
}

/// Extra features of an honest case for the cross-family collectors: the chunk header's congestion
/// info and that of the previous chunk of the shard (the main transition's input).
pub fn features(sw: &near_primitives::stateless_validation::state_witness::ChunkStateWitness, b2_genesis: bool) -> Option<serde_json::Value> {
    kind()?;
    let ci = sw.chunk_header().congestion_info();
    Some(json!({
        "post_delayed_receipts_gas": ci.delayed_receipts_gas().to_string(),
        "post_buffered_receipts_gas": ci.buffered_receipts_gas().to_string(),
        "post_receipt_bytes": ci.receipt_bytes(),
        "b2_genesis": b2_genesis,
        "n_transactions": sw.transactions().len(),
        "n_new_transactions": sw.new_transactions().len(),
    }))
}

/// Genesis-B2 mutants (W10): a transaction placed into the genesis chunk's (empty) transaction
/// list, the claim's `tx_valid` flags made inconsistent, and `genesis_chunk_extra` removed or
/// altered. Returns (mutant, derived reason) — a derived mutant's expectation is not nearcore's.
pub fn genesis_mutants(claim: &crate::enc::Claim, sw: &near_primitives::stateless_validation::state_witness::ChunkStateWitness)
    -> Vec<(crate::mutate::Mutant, Option<&'static str>)> {
    use crate::mutate::{Judge, Mutant};
    use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
    use near_primitives::types::chunk_extra::ChunkExtra;
    let mut out = Vec::new();
    if kind() != Some(Kind::GenesisTx) {
        return out;
    }
    let ChunkStateWitness::V2(x) = sw;
    if let Some(t) = x.new_transactions.first() {
        for (name, flag) in [("g.tx_in_genesis_chunk", 1u8), ("g.tx_in_genesis_chunk.flag0", 0u8)] {
            let mut w2 = sw.clone();
            let ChunkStateWitness::V2(y) = &mut w2;
            y.transactions = vec![t.clone()];
            let mut c = claim.clone();
            c.tx_valid = vec![flag];
            out.push((Mutant { name: name.into(), claim: c, witness: borsh::to_vec(&w2).unwrap(), judge: Judge::Nearcore }, None));
        }
    }
    let wb = borsh::to_vec(sw).unwrap();
    for (name, flags) in [("g.tx_valid_extra_flag1", vec![1u8]), ("g.tx_valid_extra_flag0", vec![0u8])] {
        let mut c = claim.clone();
        c.tx_valid = flags;
        out.push((Mutant { name: name.into(), claim: c, witness: wb.clone(), judge: Judge::Claim }, None));
    }
    {
        let mut c = claim.clone();
        c.genesis_chunk_extra = None;
        out.push((Mutant { name: "g.genesis_extra.none".into(), claim: c, witness: wb.clone(), judge: Judge::Claim }, None));
    }
    if let Some(ge) = &claim.genesis_chunk_extra {
        if let Ok(ce) = borsh::from_slice::<ChunkExtra>(ge) {
            let mut edits: Vec<(&str, ChunkExtra)> = Vec::new();
            let mut e = ce.clone();
            e.state_root_mut().0[0] ^= 1;
            edits.push(("g.genesis_extra.state_root", e));
            if let ChunkExtra::V5(v) = &ce {
                let mut v2 = v.clone();
                v2.gas_limit = Gas::from_gas(v2.gas_limit.as_gas() ^ 1);
                edits.push(("g.genesis_extra.gas_limit", ChunkExtra::V5(v2)));
                let mut v2 = v.clone();
                v2.balance_burnt = Balance::from_yoctonear(v2.balance_burnt.as_yoctonear() ^ 1);
                edits.push(("g.genesis_extra.balance_burnt", ChunkExtra::V5(v2)));
                let mut v2 = v.clone();
                v2.outcome_root.0[0] ^= 1;
                edits.push(("g.genesis_extra.outcome_root", ChunkExtra::V5(v2)));
                let mut v2 = v.clone();
                v2.gas_used = Gas::from_gas(v2.gas_used.as_gas() ^ 1);
                edits.push(("g.genesis_extra.gas_used", ChunkExtra::V5(v2)));
            }
            let mut e = ce.clone();
            let near_primitives::congestion_info::CongestionInfo::V1(ref mut c1) = *e.congestion_info_mut();
            c1.delayed_receipts_gas ^= 1;
            edits.push(("g.genesis_extra.congestion", e));
            for (name, e) in edits {
                let mut c = claim.clone();
                c.genesis_chunk_extra = Some(borsh::to_vec(&e).unwrap());
                out.push((Mutant { name: name.into(), claim: c, witness: wb.clone(), judge: Judge::Nearcore },
                          Some("derived: genesis_chunk_extra differs from the validator's stored genesis chunk extra")));
            }
        }
    }
    out
}
