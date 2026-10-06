//! D3 PoC differential harness.
//!
//! stdin: one case per line: `<prepaid_gas_decimal> <wasm_hex>`.
//! stdout: one line per case:
//!   `ok <burnt_gas> <used_gas> <return_hex|->` or
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
use std::io::{BufRead, Write};
use std::sync::Arc;

const PV: u32 = 86;

fn context(prepaid_gas: u64) -> VMContext {
    VMContext {
        current_account_id: "alice.near".parse().unwrap(),
        signer_account_id: "bob.near".parse().unwrap(),
        signer_account_pk: vec![0, 1, 2],
        predecessor_account_id: "bob.near".parse().unwrap(),
        refund_to_account_id: "bob.near".parse().unwrap(),
        input: std::rc::Rc::from(Vec::new()),
        promise_results: Vec::new().into(),
        block_height: 10,
        block_timestamp: 42,
        epoch_height: 1,
        account_balance: Balance::from_yoctonear(10u128.pow(24)),
        account_locked_balance: Balance::ZERO,
        storage_usage: 1000,
        account_contract: near_primitives_core::account::AccountContract::None,
        attached_deposit: Balance::ZERO,
        prepaid_gas: Gas::from_gas(prepaid_gas),
        random_seed: vec![0; 32],
        view_config: None,
        output_data_receivers: vec![],
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "run".into());
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
        let (gas, code_hex) = line.split_once(' ').expect("`<gas> <hex>`");
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
        let ctx = context(prepaid);
        let mut ext = MockedExternal::with_code(ContractCode::new(code, None));
        let gas_counter = ctx.make_gas_counter(&wasm_config);
        let prepared =
            near_vm_runner::prepare(&ext, Arc::clone(&wasm_config), None, gas_counter, "main");
        let outcome =
            near_vm_runner::run(prepared, &mut ext, &ctx, Arc::clone(&fees)).expect("VMRunnerError");
        let burnt = outcome.burnt_gas.as_gas();
        let used = outcome.used_gas.as_gas();
        match &outcome.aborted {
            Some(err) => writeln!(out, "abort {burnt} {used} {err:?}").unwrap(),
            None => {
                let ret = match &outcome.return_data {
                    ReturnData::Value(v) => hex::encode(v),
                    ReturnData::None => "-".to_string(),
                    ReturnData::ReceiptIndex(i) => format!("receipt{i}"),
                };
                writeln!(out, "ok {burnt} {used} {ret}").unwrap()
            }
        }
        out.flush().unwrap();
    }
}
