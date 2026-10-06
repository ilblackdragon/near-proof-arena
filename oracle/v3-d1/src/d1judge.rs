//! nearcore's validator with the store's transaction-validity answers replaced by the claim's
//! `tx_valid` (trusted-fact mutants of D1). The witness path is exactly `judge.rs`
//! (oracle/v3/src/judge.rs, shared with the D0 oracle by `#[path]`); only the flags differ.

use crate::judge::{decode_witness, pre_validate};
use near_chain::stateless_validation::chunk_validation::{MainStateTransitionCache, validate_chunk_state_witness};
use near_chain::ChainStoreAccess;
use near_client::Client;
use near_epoch_manager::EpochManagerAdapter;
use reed_solomon_erasure::galois_8::ReedSolomon;
use std::sync::Arc;

/// As `judge_inner`, but the store's answer to "is transaction i of the last new chunk within
/// its validity period" (`check_transaction_validity_period`, chunk_validation.rs:382-401) is
/// replaced by `tx_valid` — i.e. nearcore run against a chain store whose trusted answer is the
/// claim's `tx_valid` (used for trusted-fact mutants of `tx_valid`).
fn judge_inner_flags(
    client: &Client,
    bytes: &[u8],
    codes: &[Vec<u8>],
    rs: (u16, u16),
    tx_valid: Option<&[u8]>,
) -> Result<(), String> {
    let w = decode_witness(bytes, codes)?;
    let prev = *w.chunk_header().prev_block_hash();
    client.chain.get_block(&prev).map_err(|e| format!("actor: prev block: {e:?}"))?;
    let em: &dyn EpochManagerAdapter = client.epoch_manager.as_ref();
    let expected = em.get_epoch_id_from_prev_block(&prev).map_err(|e| format!("actor: {e:?}"))?;
    if &expected != w.epoch_id() {
        return Err("actor: InvalidChunkStateWitness epoch id".into());
    }
    let mut pre = pre_validate(client, &w)?;
    if let Some(flags) = tx_valid {
        if let near_chain::stateless_validation::chunk_validation::MainTransition::NewChunk { new_chunk_data, .. } =
            &mut pre.main_transition_params
        {
            let (txs, _) = new_chunk_data.transactions.get_potentially_expired_transactions_and_expiration_flags();
            if flags.len() != txs.len() {
                return Err("tx_valid length differs from transactions".into());
            }
            new_chunk_data.transactions = node_runtime::SignedValidPeriodTransactions::new(
                txs.to_vec(),
                flags.iter().map(|f| *f != 0).collect(),
            );
        }
    }
    let (d, total) = (rs.0 as usize, rs.1 as usize);
    if d == 0 || total <= d {
        return Err("rs: invalid parameters".into());
    }
    let rs = Arc::new(ReedSolomon::new(d, total - d).map_err(|e| format!("rs: {e:?}"))?);
    validate_chunk_state_witness(
        w,
        pre,
        em,
        client.runtime_adapter.as_ref(),
        &MainStateTransitionCache::default(),
        client.chain.chain_store().store(),
        false,
        rs,
    )
    .map_err(|e| format!("validate: {e:?}"))
}

/// `nearcore_judge` with the trusted transaction-validity answers replaced (see `judge_inner_flags`).
pub fn nearcore_judge_flags(client: &Client, bytes: &[u8], rs: (u16, u16), tx_valid: &[u8]) -> Result<(), String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| judge_inner_flags(client, bytes, &[], rs, Some(tx_valid)))) {
        Ok(r) => r,
        Err(_) => Err("panic".into()),
    }
}
