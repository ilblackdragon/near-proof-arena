//! Reference judge: nearcore's own stateless validator on the witness bytes,
//! exactly the witness path of ChunkValidationActor (chunk_validation_actor.rs:
//! 338-345, 384-412, 473-486) — never the chunk-extra shortcut.

use near_chain::stateless_validation::chunk_validation::{
    MainStateTransitionCache, PreValidationOutput, pre_validate_chunk_state_witness,
    validate_chunk_state_witness,
};
use near_chain::ChainStoreAccess;
use near_client::Client;
use near_epoch_manager::EpochManagerAdapter;
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use reed_solomon_erasure::galois_8::ReedSolomon;
use std::sync::Arc;

pub const MAX_UNCOMPRESSED: usize = 64 * 1024 * 1024;

pub fn decode_witness(bytes: &[u8], codes: &[Vec<u8>]) -> Result<ChunkStateWitness, String> {
    if bytes.len() > MAX_UNCOMPRESSED {
        return Err("decode: witness larger than 64 MiB".into());
    }
    let mut w: ChunkStateWitness =
        borsh::from_slice(bytes).map_err(|e| format!("decode: {e}"))?;
    let PartialState::TrieValues(values) = &mut w.mut_main_state_transition().base_state;
    values.extend(codes.iter().map(|c| c.clone().into()));
    Ok(w)
}

pub fn pre_validate(client: &Client, w: &ChunkStateWitness) -> Result<PreValidationOutput, String> {
    pre_validate_chunk_state_witness(
        w,
        client.chain.chain_store(),
        client.chain.genesis_block(),
        client.epoch_manager.as_ref(),
        client.runtime_adapter.as_ref(),
    )
    .map_err(|e| format!("pre_validate: {e:?}"))
}

fn judge_inner(client: &Client, bytes: &[u8], codes: &[Vec<u8>], rs: (u16, u16)) -> Result<(), String> {
    let w = decode_witness(bytes, codes)?;
    let prev = *w.chunk_header().prev_block_hash();
    client.chain.get_block(&prev).map_err(|e| format!("actor: prev block: {e:?}"))?;
    let em: &dyn EpochManagerAdapter = client.epoch_manager.as_ref();
    let expected = em.get_epoch_id_from_prev_block(&prev).map_err(|e| format!("actor: {e:?}"))?;
    if &expected != w.epoch_id() {
        return Err("actor: InvalidChunkStateWitness epoch id".into());
    }
    let pre = pre_validate(client, &w)?;
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

/// Ok(()) iff nearcore would endorse. Panics inside nearcore (receipt
/// validation errors, integer overflow, storage inconsistency) count as reject.
pub fn nearcore_judge(client: &Client, bytes: &[u8], codes: &[Vec<u8>], rs: (u16, u16)) -> Result<(), String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| judge_inner(client, bytes, codes, rs))) {
        Ok(r) => r,
        Err(p) => {
            let msg = p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            Err(format!("panic: {msg}"))
        }
    }
}
