//! D3 PoC differential harness.
//!
//! stdin: one case per line: `<prepaid_gas_decimal> <wasm_hex> [<receiver>,<receiver>…]`
//! (optional output data receivers, comma-separated account ids).
//! stdout: one line per case:
//!   `ok <burnt_gas> <used_gas> <return_hex|-> <balance_yocto>` or
//!   `abort <burnt_gas> <used_gas> <FunctionCallError debug>`.
//! Mode `prepare` instead prints the hex of the prepared (instrumented) module
//! or `prepare-error <PrepareError debug>`.
//!
//! Everything below is nearcore's own code path: `near_vm_runner::prepare` +
//! `near_vm_runner::run` with the mainnet PV86 `RuntimeConfig` (vm_kind = Wasmtime),
//! a `MockedExternal` (no host function used by the PoC touches it) and no
//! compiled-contract cache.
use near_parameters::RuntimeConfigStore;
use near_primitives_core::code::ContractCode;
use near_primitives_core::types::{Balance, Gas};
use near_vm_runner::logic::mocks::mock_external::MockedExternal;
use near_vm_runner::logic::{ReturnData, VMContext};
use near_vm_runner::logic::mocks::mock_external::MockAction;
use std::io::{BufRead, Write};
use std::sync::Arc;

const PV: u32 = 86;

/// Optional per-case context overrides (3rd input token): either a comma list of output data
/// receivers (legacy), or `key=value;…` with keys `rcv` (comma list), `input` (hex),
/// `results` (comma list of `S<hex>` / `F` / `N`), `deposit` (yocto), `balance` (yocto).
#[derive(Default)]
struct Opts {
    receivers: Vec<near_primitives_core::types::AccountId>,
    input: Vec<u8>,
    results: Vec<near_vm_runner::logic::types::PromiseResult>,
    deposit: u128,
    balance: Option<u128>,
}

fn parse_opts(tok: Option<&str>) -> Opts {
    use near_vm_runner::logic::types::PromiseResult;
    let mut o = Opts::default();
    let Some(tok) = tok else { return o };
    if !tok.contains('=') {
        o.receivers = tok.split(',').map(|a| a.parse().expect("receiver")).collect();
        return o;
    }
    for kv in tok.split(';').filter(|s| !s.is_empty()) {
        let (k, v) = kv.split_once('=').expect("k=v");
        match k {
            "rcv" => o.receivers = v.split(',').filter(|s| !s.is_empty()).map(|a| a.parse().expect("rcv")).collect(),
            "input" => o.input = hex::decode(v).expect("input hex"),
            "results" => {
                o.results = v
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|r| match &r[..1] {
                        "S" => PromiseResult::Successful(std::rc::Rc::from(hex::decode(&r[1..]).unwrap())),
                        "F" => PromiseResult::Failed,
                        _ => PromiseResult::NotReady,
                    })
                    .collect()
            }
            "deposit" => o.deposit = v.parse().unwrap(),
            "balance" => o.balance = Some(v.parse().unwrap()),
            _ => panic!("unknown option {k}"),
        }
    }
    o
}

fn context(prepaid_gas: u64, o: Opts) -> VMContext {
    let receivers = o.receivers;
    VMContext {
        current_account_id: "alice.near".parse().unwrap(),
        signer_account_id: "bob.near".parse().unwrap(),
        signer_account_pk: vec![0, 1, 2],
        predecessor_account_id: "bob.near".parse().unwrap(),
        refund_to_account_id: "bob.near".parse().unwrap(),
        input: std::rc::Rc::from(o.input),
        promise_results: o.results.into(),
        block_height: 10,
        block_timestamp: 42,
        epoch_height: 1,
        account_balance: Balance::from_yoctonear(o.balance.unwrap_or(10u128.pow(24))),
        account_locked_balance: Balance::ZERO,
        storage_usage: 1000,
        account_contract: near_primitives_core::account::AccountContract::None,
        attached_deposit: Balance::from_yoctonear(o.deposit),
        prepaid_gas: Gas::from_gas(prepaid_gas),
        random_seed: vec![0; 32],
        view_config: None,
        output_data_receivers: receivers,
    }
}

fn hx(b: &[u8]) -> String {
    hex::encode(b)
}

fn pk(p: &near_crypto::PublicKey) -> String {
    hex::encode(borsh::to_vec(p).unwrap())
}

/// Canonical text of MockedExternal's action log (full mode).
fn fmt_action(a: &MockAction) -> String {
    use MockAction::*;
    match a {
        CreateReceipt { receipt_indices, receiver_id } => format!(
            "CR({})>{}",
            receipt_indices.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(","),
            receiver_id
        ),
        CreateAccount { receipt_index } => format!("CA@{receipt_index}"),
        DeployContract { receipt_index, code } => format!("DC@{receipt_index}:{}", hx(code)),
        FunctionCallWeight { receipt_index, method_name, args, attached_deposit, prepaid_gas, gas_weight } => {
            format!(
                "FC@{receipt_index}:{}:{}:{}:{}:{}",
                hx(method_name),
                hx(args),
                attached_deposit.as_yoctonear(),
                prepaid_gas.as_gas(),
                gas_weight.0
            )
        }
        Transfer { receipt_index, deposit } => format!("TR@{receipt_index}:{}", deposit.as_yoctonear()),
        Stake { receipt_index, stake, public_key } => {
            format!("ST@{receipt_index}:{}:{}", stake.as_yoctonear(), pk(public_key))
        }
        DeleteAccount { receipt_index, beneficiary_id } => format!("DA@{receipt_index}:{beneficiary_id}"),
        DeleteKey { receipt_index, public_key } => format!("DK@{receipt_index}:{}", pk(public_key)),
        AddKeyWithFullAccess { receipt_index, public_key, nonce } => {
            format!("AF@{receipt_index}:{}:{nonce}", pk(public_key))
        }
        AddKeyWithFunctionCall { receipt_index, public_key, nonce, allowance, receiver_id, method_names } => {
            format!(
                "AC@{receipt_index}:{}:{nonce}:{}:{receiver_id}:{}",
                pk(public_key),
                allowance.map(|a| a.as_yoctonear().to_string()).unwrap_or("-".into()),
                method_names.iter().map(|m| hx(m)).collect::<Vec<_>>().join("/")
            )
        }
        YieldCreate { data_id, receiver_id, yield_id } => format!(
            "YC:{}>{}:{}",
            hx(&data_id.0),
            receiver_id,
            yield_id.map(|y| hx(&y.0.0)).unwrap_or("-".into())
        ),
        YieldResume { data_id, data } => format!("YR:{}:{}", hx(&data_id.0), hx(data)),
        SetRefundTo { receipt_index, refund_to } => format!("RT@{receipt_index}:{refund_to}"),
        _ => "OTHER".to_string(),
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "run".into());
    // `full`: like `run`, plus ` || compute <n> || logs <hex,…> || actions <a;…> || trie <k=v,…>`
    let full = mode == "full";
    let store = RuntimeConfigStore::new(None);
    let runtime_config = Arc::clone(store.get_config(PV));
    let wasm_config = Arc::clone(&runtime_config.wasm_config);
    let fees = Arc::clone(&runtime_config.fees);
    assert_eq!(format!("{:?}", wasm_config.vm_kind), "Wasmtime", "PV86 must run on Wasmtime");
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    for line in stdin.lock().lines() {
        let line = line.expect("stdin");
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let mut parts = line.split(' ');
        let gas = parts.next().expect("gas");
        let code_hex = parts.next().expect("hex");
        let opts = parse_opts(parts.next());
        let prepaid: u64 = gas.parse().expect("gas");
        let code = hex::decode(code_hex).expect("hex");
        if mode == "prepare" {
            match near_vm_runner::prepare::prepare_contract(
                &code,
                &wasm_config,
                near_parameters::vm::VMKind::Wasmtime,
            ) {
                Ok(p) => writeln!(out, "{}", hex::encode(p)).unwrap(),
                Err(e) => writeln!(out, "prepare-error {e:?}").unwrap(),
            }
            continue;
        }
        let ctx = context(prepaid, opts);
        let mut ext = MockedExternal::with_code(ContractCode::new(code, None));
        let gas_counter = ctx.make_gas_counter(&wasm_config);
        let prepared =
            near_vm_runner::prepare(&ext, Arc::clone(&wasm_config), None, gas_counter, "main");
        let outcome =
            near_vm_runner::run(prepared, &mut ext, &ctx, Arc::clone(&fees)).expect("VMRunnerError");
        let extra = if full {
            let mut trie: Vec<_> = ext.fake_trie.iter().map(|(k, v)| format!("{}={}", hx(k), hx(v))).collect();
            trie.sort();
            format!(
                " || compute {} || logs {} || actions {} || trie {}",
                outcome.compute_usage,
                outcome.logs.iter().map(|l| hx(l.as_bytes())).collect::<Vec<_>>().join(","),
                ext.action_log.iter().map(fmt_action).collect::<Vec<_>>().join(";"),
                trie.join(",")
            )
        } else {
            String::new()
        };
        let burnt = outcome.burnt_gas.as_gas();
        let used = outcome.used_gas.as_gas();
        match &outcome.aborted {
            Some(err) => writeln!(out, "abort {burnt} {used} {err:?}{extra}").unwrap(),
            None => {
                let ret = match &outcome.return_data {
                    ReturnData::Value(v) => hex::encode(v),
                    ReturnData::None => "-".to_string(),
                    ReturnData::ReceiptIndex(i) => format!("receipt{i}"),
                };
                writeln!(out, "ok {burnt} {used} {ret} {}{extra}", outcome.balance.as_yoctonear()).unwrap()
            }
        }
        out.flush().unwrap();
    }
}
