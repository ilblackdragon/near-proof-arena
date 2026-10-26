#!/usr/bin/env python3
"""Check that every protocol limit constant the successor Lean spec uses equals the pinned PV86
parameter (docs/research/near-wasm-boundary-inventory.json, extracted from nearcore 44f7ae6c).

W02 Gate-B caps inventory (docs/evidence/lean-chunk-completion/gate-b-caps/README.md): a limit the
successor enforces must be nearcore's own value. Prints one row per constant and exits non-zero on
any mismatch or missing definition."""
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LEAN = REPO / "spec/lean/v3"

# (Lean file, definition or `NearCfg` field, pinned parameter)
ROWS = [
    ("NearSpecV3/D2/Fees.lean", "maxActions", "max_actions_per_receipt"),
    ("NearSpecV3/D2/Fees.lean", "maxDeployActions", "max_deploy_actions_per_receipt"),
    ("NearSpecV3/D2/Fees.lean", "maxTotalPrepaidGas", "max_total_prepaid_gas"),
    ("NearSpecV3/D2/Fees.lean", "maxReceiptSize", "max_receipt_size"),
    ("NearSpecV3/D2/Fees.lean", "maxContractSize", "max_contract_size"),
    ("NearSpecV3/D2/Fees.lean", "maxMethodName", "max_length_method_name"),
    ("NearSpecV3/D2/Fees.lean", "maxArgs", "max_arguments_length"),
    ("NearSpecV3/D2/Fees.lean", "maxMethodNamesBytes", "max_number_bytes_method_names"),
    ("NearSpecV3/D2/Fees.lean", "maxInputDeps", "max_number_input_data_dependencies"),
    ("NearSpecV3/D2/Fees.lean", "maxReturnedData", "max_length_returned_data"),
    ("NearSpecV3/D2/Fees.lean", "minTopLevelLen", "min_allowed_top_level_account_length"),
    ("NearSpecV3/D2/GlobalTypes.lean", "maxStorageKey", "max_length_storage_key"),
    ("NearSpecV3/D2/GlobalTypes.lean", "maxStorageValue", "max_length_storage_value"),
    ("NearSpecV3/TxD1.lean", "maxTransactionSize", "max_transaction_size"),
    ("NearSpecV3/StorageBound.lean", "softLimit", "main_storage_proof_size_soft_limit"),
    ("NearSpecV3/StorageBound.lean", "perReceiptLimit", "per_receipt_storage_proof_size_limit"),
    ("NearSpecV3/Wasm/TrieStore.lean", "perReceiptProofLimit", "per_receipt_storage_proof_size_limit"),
    ("NearSpecV3/Successor/StorageExecution.lean", "softLimit", "main_storage_proof_size_soft_limit"),
    ("NearSpecV3/Wasm/Host.lean", "maxRegisterSize", "max_register_size"),
    ("NearSpecV3/Wasm/Host.lean", "maxNumberRegisters", "max_number_registers"),
    ("NearSpecV3/Wasm/Host.lean", "registersMemoryLimit", "registers_memory_limit"),
    ("NearSpecV3/Wasm/Host.lean", "maxNumberLogs", "max_number_logs"),
    ("NearSpecV3/Wasm/Host.lean", "maxTotalLogLength", "max_total_log_length"),
    ("NearSpecV3/Wasm/Host.lean", "maxPromises", "max_promises_per_function_call_action"),
    ("NearSpecV3/Wasm/Host.lean", "maxInputDataDependencies", "max_number_input_data_dependencies"),
    ("NearSpecV3/Wasm/Host.lean", "maxContractSize", "max_contract_size"),
    ("NearSpecV3/Wasm/Host.lean", "maxLengthStorageKey", "max_length_storage_key"),
    ("NearSpecV3/Wasm/Host.lean", "maxLengthStorageValue", "max_length_storage_value"),
    ("NearSpecV3/Wasm/Host.lean", "maxYieldPayloadSize", "max_yield_payload_size"),
    ("NearSpecV3/Wasm/Machine.lean", "maxGasBurnt", "max_gas_burnt"),
    ("NearSpecV3/Wasm/Machine.lean", "maxLengthReturnedData", "max_length_returned_data"),
    ("NearSpecV3/Wasm/Machine.lean", "maxTableElementsStore", "max_elements_per_contract_table"),
    ("NearSpecV3/Wasm/Prepare.lean", "regularOpCost", "wasm_regular_op_cost"),
    ("NearSpecV3/Wasm/Prepare.lean", "linearOpBaseCost", "wasm_linear_op_base_cost"),
    ("NearSpecV3/Wasm/Prepare.lean", "linearOpUnitCost", "wasm_linear_op_unit_cost"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxStackHeight", "max_stack_height"),
    ("NearSpecV3/Wasm/Prepare.lean", "initialMemoryPages", "initial_memory_pages"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxMemoryPages", "max_memory_pages"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxTypes", "max_types_per_contract"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxFunctions", "max_functions_number_per_contract"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxTables", "max_tables_per_contract"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxTableElements", "max_elements_per_contract_table"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxFunctionBodySize", "max_function_body_size"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxLocals", "max_locals_per_contract"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxParamsPerFunction", "max_params_per_function"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxParamsPerContract", "max_params_per_contract"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxBlocksPerFunction", "max_blocks_per_function"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxBlocksPerContract", "max_blocks_per_contract"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxOperandStackBytes", "max_operand_stack_bytes_per_function"),
    ("NearSpecV3/Wasm/Prepare.lean", "maxInstrumentedCodeSize", "max_instrumented_code_size"),
]


def lean_value(path, name):
    text = (LEAN / path).read_text()
    for pat in (rf"def {name}\s*:\s*Nat\s*:=\s*([0-9_]+)", rf"\b{name}\s*:\s*Nat\s*:=\s*([0-9_]+)"):
        m = re.search(pat, text)
        if m:
            return int(m.group(1).replace("_", ""))
    return None


def main():
    params = json.loads((REPO / "docs/research/near-wasm-boundary-inventory.json").read_text())["parameters"]
    bad = 0
    for path, name, param in ROWS:
        got, want = lean_value(path, name), params.get(param)
        ok = got is not None and got == want
        bad += not ok
        print(f"{'ok ' if ok else 'BAD'} {path}:{name} = {got}  {param} = {want}")
    print(f"{len(ROWS) - bad}/{len(ROWS)} limit constants equal the pinned PV86 parameters")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
