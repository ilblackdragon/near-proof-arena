//! Build `claim.bin` (near-arena-claim-v3) for a witness from a client's own
//! chain store and epoch manager — the reference `claimOf(Σ, H)` of
//! spec/near-chunk-validation-v0.md §4. The backward walk mirrors
//! `get_state_witness_block_range` (chunk_validation.rs:144-253).

use crate::enc::{
    ApplyFacts, BlockRec, ChunkSlot, Claim, EpochRec, SplitGate, ValidatorUpdateFacts, block_hash,
};
use near_chain::Block;
use near_chain_configs::GenesisConfig;
use near_client::Client;
use near_epoch_manager::{EpochManagerAdapter, EpochManagerHandle};
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::ShardChunkHeader;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::types::{EpochId, ShardId};
use near_primitives::version::ProtocolFeature;
use std::collections::BTreeSet;
use std::sync::Arc;

pub struct Built {
    pub claim: Claim,
    /// walk-order blocks (newest first) = claim.blocks
    pub blocks: Vec<Arc<Block>>,
    pub b2: usize,
    /// implicit block indices, newest first (walk order)
    pub implicit: Vec<usize>,
    /// source block indices (walk order)
    pub source: Vec<usize>,
    pub shard_id: ShardId,
}

pub fn block_rec(block: &Block) -> Result<BlockRec, String> {
    let header = block.header();
    let hb = borsh::to_vec(header).map_err(|e| e.to_string())?;
    let sig = borsh::to_vec(header.signature()).map_err(|e| e.to_string())?;
    if hb.len() < 1 + 32 + 208 + sig.len() {
        return Err("short header".into());
    }
    let mut prev = [0u8; 32];
    prev.copy_from_slice(&hb[1..33]);
    let mut slots = Vec::new();
    for c in block.chunks().iter_raw() {
        let inner = match c {
            ShardChunkHeader::V3(h) => borsh::to_vec(&h.inner).map_err(|e| e.to_string())?,
            _ => return Err("chunk header not V3".into()),
        };
        slots.push(ChunkSlot { inner, height_included: c.height_included() });
    }
    let rec = BlockRec {
        header_version: hb[0],
        prev_hash: prev,
        inner_lite: hb[33..241].to_vec(),
        inner_rest: hb[241..hb.len() - sig.len()].to_vec(),
        slots,
    };
    if block_hash(&rec) != block.hash().0 {
        return Err("block hash recomputation mismatch (header layout)".into());
    }
    Ok(rec)
}

fn sorted_accts(m: impl IntoIterator<Item = (near_primitives::types::AccountId, near_primitives::types::Balance)>) -> Vec<(String, u128)> {
    let mut v: Vec<(String, u128)> =
        m.into_iter().map(|(a, b)| (a.to_string(), b.as_yoctonear())).collect();
    v.sort();
    v
}

pub fn build_claim(
    client: &Client,
    em: &Arc<EpochManagerHandle>,
    genesis_config: &GenesisConfig,
    witness: &ChunkStateWitness,
) -> Result<Built, String> {
    let e = |x: &dyn std::fmt::Debug| format!("{x:?}");
    let header = witness.chunk_header();
    let shard0 = header.shard_id();
    let chain = &client.chain;
    let emd: &dyn EpochManagerAdapter = em.as_ref();

    // Backward walk.
    let mut blocks: Vec<Arc<Block>> = Vec::new();
    let mut cur = chain.get_block(header.prev_block_hash()).map_err(|x| e(&x))?;
    let mut shard_id = shard0;
    let mut seen = 0u32;
    let (mut implicit, mut source, mut b2) = (Vec::new(), Vec::new(), None);
    loop {
        let idx = blocks.len();
        blocks.push(cur.clone());
        let (_l, prev_shard_id, prev_shard_index) =
            emd.get_prev_shard_id_from_prev_hash(cur.hash(), shard_id).map_err(|x| e(&x))?;
        let is_new = cur
            .chunks()
            .get(prev_shard_index)
            .ok_or("missing slot")?
            .is_new_chunk(cur.header().height());
        let seen2 = seen + is_new as u32;
        match seen2 {
            0 => implicit.push(idx),
            1 => {
                if b2.is_none() {
                    b2 = Some(idx)
                }
                source.push(idx)
            }
            _ => break,
        }
        if cur.header().is_genesis() {
            break;
        }
        cur = chain.get_block(cur.header().prev_hash()).map_err(|x| e(&x))?;
        shard_id = prev_shard_id;
        seen = seen2;
    }
    let b2 = b2.ok_or("walk found no last new chunk")?;

    let recs = blocks.iter().map(|b| block_rec(b)).collect::<Result<Vec<_>, _>>()?;

    // Epoch table.
    let mut eids: BTreeSet<[u8; 32]> = BTreeSet::new();
    eids.insert(witness.epoch_id().0.0);
    for b in &blocks {
        eids.insert(b.header().epoch_id().0.0);
    }
    let mut epochs = Vec::new();
    for id in &eids {
        let eid = EpochId(CryptoHash(*id));
        let info = emd.get_epoch_info(&eid).map_err(|x| e(&x))?;
        let layout = emd.get_shard_layout(&eid).map_err(|x| e(&x))?;
        let mut validators: Vec<(String, u128)> = info
            .validators_iter()
            .map(|v| (v.account_id().to_string(), v.stake().as_yoctonear()))
            .collect();
        validators.sort();
        epochs.push(EpochRec {
            epoch_id: *id,
            protocol_version: info.protocol_version(),
            epoch_height: info.epoch_height(),
            shard_layout: borsh::to_vec(&layout).map_err(|x| e(&x))?,
            validators,
        });
    }
    let pv = emd.get_epoch_protocol_version(witness.epoch_id()).map_err(|x| e(&x))?;

    let mut epoch_start_after = Vec::new();
    for b in &blocks {
        epoch_start_after.push(emd.is_next_block_epoch_start(b.hash()).map_err(|x| e(&x))? as u8);
    }

    // Applied blocks: main (unless genesis), then implicit oldest first.
    let b2_genesis = blocks[b2].header().is_genesis();
    let mut applied: Vec<usize> = Vec::new();
    if !b2_genesis {
        applied.push(b2);
    }
    applied.extend(implicit.iter().rev().copied());
    let mut apply_facts = Vec::new();
    for &i in &applied {
        let x = &blocks[i];
        let prev = x.header().prev_hash();
        let validator_update = if emd.is_next_block_epoch_start(prev).map_err(|x| e(&x))? {
            let (si, vr) = em.read().compute_stake_return_info(prev).map_err(|x| e(&x))?;
            Some(ValidatorUpdateFacts {
                stake_info: sorted_accts(si),
                validator_rewards: sorted_accts(vr),
                protocol_treasury_account: Some(genesis_config.protocol_treasury_account.to_string()),
            })
        } else {
            None
        };
        let minimum_stake = em.read().minimum_stake(prev).map_err(|x| e(&x))?.as_yoctonear();
        let x_epoch = x.header().epoch_id();
        let x_pv = emd.get_epoch_protocol_version(x_epoch).map_err(|x| e(&x))?;
        let cfg = emd.get_epoch_config(x_epoch).map_err(|x| e(&x))?;
        let split_gate = match cfg.dynamic_resharding_config() {
            Some(c)
                if ProtocolFeature::DynamicResharding.enabled(x_pv)
                    && emd
                        .is_next_block_possibly_last_in_epoch(x.header().height(), prev)
                        .map_err(|x| e(&x))?
                    && emd.can_reshard(prev, c.min_epochs_between_resharding).map_err(|x| e(&x))? =>
            {
                Some(SplitGate {
                    memory_usage_threshold: c.memory_usage_threshold,
                    min_child_memory_usage: c.min_child_memory_usage,
                    max_number_of_shards: c.max_number_of_shards as u64,
                    force_split_shards: c.force_split_shards.iter().map(|s| (*s).into()).collect(),
                    block_split_shards: c.block_split_shards.iter().map(|s| (*s).into()).collect(),
                })
            }
            _ => None,
        };
        apply_facts.push(ApplyFacts { validator_update, minimum_stake, split_gate });
    }

    // Transaction validity flags (chunk_validation.rs:382-401).
    let tx_valid = if b2_genesis {
        vec![1u8; witness.transactions().len()]
    } else {
        let ph = chain
            .chain_store()
            .get_block_header(blocks[b2].header().prev_hash())
            .map_err(|x| e(&x))?;
        witness
            .transactions()
            .iter()
            .map(|t| {
                chain
                    .chain_store()
                    .check_transaction_validity_period(&ph, t.transaction.block_hash())
                    .is_ok() as u8
            })
            .collect()
    };
    let genesis_chunk_extra = if b2_genesis {
        let layout = emd.get_shard_layout(blocks[b2].header().epoch_id()).map_err(|x| e(&x))?;
        let ce = near_chain::Chain::genesis_chunk_extra(
            chain.genesis_block(),
            chain.chain_store(),
            &layout,
            shard_id,
        )
        .map_err(|x| e(&x))?;
        Some(borsh::to_vec(&ce).map_err(|x| e(&x))?)
    } else {
        None
    };
    let chunk_inner = match header {
        ShardChunkHeader::V3(h) => borsh::to_vec(&h.inner).map_err(|x| e(&x))?,
        _ => return Err("endorsed header not V3".into()),
    };
    let claim = Claim {
        protocol_version: pv,
        chain_id: genesis_config.chain_id.clone(),
        epoch_id: witness.epoch_id().0.0,
        chunk_inner,
        blocks: recs,
        rs_data_parts: emd.num_data_parts() as u16,
        rs_total_parts: emd.num_total_parts() as u16,
        epochs,
        epoch_start_after,
        apply_facts,
        tx_valid,
        genesis_chunk_extra,
    };
    Ok(Built { claim, blocks, b2, implicit, source, shard_id: shard0 })
}
