//! Independent pinned-nearcore Borsh normalization probes. No Lean code is involved.
use borsh::{BorshDeserialize, BorshSerialize};
use near_primitives::{
    action::{Action, delegate::SignedDelegateAction},
    transaction::SignedTransaction,
};
use near_primitives_core::deterministic_account_id::DeterministicAccountStateInit;
use serde_json::{Value, json};

fn roundtrip<T: BorshDeserialize + BorshSerialize>(input: &[u8]) -> Result<(T, Vec<u8>), String> {
    let decoded = borsh::from_slice::<T>(input).map_err(|e| e.to_string())?;
    let canonical = borsh::to_vec(&decoded).map_err(|e| e.to_string())?;
    Ok((decoded, canonical))
}

pub fn command(args: &[String]) -> i32 {
    let run = || -> Result<Value, String> {
        let kind = args.get(2).ok_or("missing codec kind")?;
        if kind == "runtime-fees" {
            let store = near_parameters::RuntimeConfigStore::new(None);
            let config = store.get_config(86);
            let fees: Vec<_> = config
                .fees
                .action_fees
                .iter()
                .map(|(kind, fee)| {
                    json!({"kind":format!("{kind:?}"),"send_sir":fee.send_sir.gas(),
                    "send_not_sir":fee.send_not_sir.gas(),"execution":fee.execution.gas()})
                })
                .collect();
            return Ok(json!({"protocol_version":86,"action_fees":fees}));
        }
        let input =
            hex::decode(args.get(3).ok_or("missing hex bytes")?).map_err(|e| e.to_string())?;
        let (canonical, extra) = match kind.as_str() {
            "action" => (roundtrip::<Action>(&input)?.1, json!({})),
            "signed-transaction" => {
                let (value, bytes) = roundtrip::<SignedTransaction>(&input)?;
                (
                    bytes,
                    json!({"transaction_hash_hex": hex::encode(value.get_hash().as_bytes())}),
                )
            }
            "signed-delegate" => {
                let (value, bytes) = roundtrip::<SignedDelegateAction>(&input)?;
                (
                    bytes,
                    json!({"nep461_hash_hex": hex::encode(value.delegate_action.get_nep461_hash().as_bytes())}),
                )
            }
            "state-init" => {
                let (value, bytes) = roundtrip::<DeterministicAccountStateInit>(&input)?;
                (
                    bytes,
                    json!({"derived_account_id": near_primitives::utils::derive_near_deterministic_account_id(&value)}),
                )
            }
            _ => return Err(format!("unknown codec kind: {kind}")),
        };
        Ok(
            json!({"kind":kind,"status":"ok","input_hex":hex::encode(input),
                  "canonical_hex":hex::encode(canonical),"extra":extra}),
        )
    };
    match run() {
        Ok(value) => {
            println!("{value}");
            0
        }
        Err(error) => {
            println!("{}", json!({"status":"error","error":error}));
            1
        }
    }
}
