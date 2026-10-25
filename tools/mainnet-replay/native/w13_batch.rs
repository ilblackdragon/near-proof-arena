//! Diagnostic export from the actual mainnet store, with synchronous native replay.
#[path = "w13_enc.rs"]
mod enc;
#[path = "w13_claim.rs"]
mod claim;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use near_chain::ChainStoreAccess;
use near_epoch_manager::{EpochManager, EpochManagerAdapter};
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_store::Store;
use nearcore::NearConfig;
use reed_solomon_erasure::galois_8::ReedSolomon;
use near_chain::stateless_validation::chunk_validation::{pre_validate_chunk_state_witness, validate_chunk_state_witness, MainStateTransitionCache};

#[derive(clap::Parser)]
pub struct ReplayExportCmd {
    #[arg(long)] input: PathBuf,
    #[arg(long)] output: PathBuf,
    #[arg(long)] limit: Option<usize>,
}
impl ReplayExportCmd {
    pub(crate) fn run(&self, home: &Path, config: NearConfig, store: Store) {
        assert_eq!(config.genesis.config.chain_id, "mainnet");
        assert!(!self.output.exists(), "output must be new");
        std::fs::create_dir_all(&self.output).unwrap();
        let em = EpochManager::new_arc_handle(store.clone(), &config.genesis.config, Some(home));
        let chain = super::setup_chain(home, config.clone(), store.clone());
        let mut dirs: Vec<_> = std::fs::read_dir(&self.input).unwrap().map(|x| x.unwrap().path())
            .filter(|p| p.join("capture.json").is_file()).collect();
        dirs.sort();
        if let Some(n) = self.limit { dirs.truncate(n); }
        let mut rows = Vec::new();
        for src in dirs {
            let result = (|| -> anyhow::Result<serde_json::Value> {
                let raw = std::fs::read(src.join("state_witness.borsh"))?;
                let witness: ChunkStateWitness = borsh::from_slice(&raw)?;
                let metadata: serde_json::Value = serde_json::from_slice(&std::fs::read(src.join("capture.json"))?)?;
                let block: near_primitives::block::Block = borsh::from_slice(&std::fs::read(src.join("block.borsh"))?)?;
                anyhow::ensure!(chain.get_block(block.hash())?.as_ref() == &block, "captured block differs from native store");
                anyhow::ensure!(chain.chain_store().get_block_hash_by_height(block.header().height())? == *block.hash(), "block is not canonical");
                anyhow::ensure!(block.chunks().iter_raw().any(|h| h.chunk_hash() == witness.chunk_header().chunk_hash()), "chunk absent from captured block");
                anyhow::ensure!(em.get_epoch_protocol_version(witness.epoch_id())? == 86, "not PV86");
                let built = claim::build_claim(&chain, &em, &config.genesis.config, &witness).map_err(|e| anyhow::anyhow!(e))?;
                let cb = built.claim.encode();
                let mut codes = std::collections::BTreeMap::new();
                for entry in std::fs::read_dir(src.join("code"))? {
                    let p = entry?.path();
                    if p.extension().and_then(|x| x.to_str()) != Some("wasm") { continue; }
                    let code = std::fs::read(&p)?;
                    let hash = near_primitives::hash::hash(&code);
                    anyhow::ensure!(p.file_stem().unwrap().to_str().unwrap() == hash.to_string(), "code hash mismatch");
                    codes.insert(hash.0, code);
                }
                let wb = enc::encode_witness(&raw, &codes.into_values().collect::<Vec<_>>());
                let dest = self.output.join(src.file_name().unwrap());
                std::fs::create_dir(&dest)?;
                std::fs::write(dest.join("claim.bin"), &cb)?;
                std::fs::write(dest.join("witness.bin"), &wb)?;
                let data = em.num_data_parts();
                let rs = Arc::new(ReedSolomon::new(data, em.num_total_parts() - data)?);
                let native = pre_validate_chunk_state_witness(&witness, chain.chain_store(), chain.genesis_block(), em.as_ref(), chain.runtime_adapter.as_ref())
                    .and_then(|pre| validate_chunk_state_witness(witness, pre, em.as_ref(), chain.runtime_adapter.as_ref(), &MainStateTransitionCache::default(), store.clone(), false, rs));
                let row = serde_json::json!({"case": dest, "source": src, "block_height": metadata["block_height"],
                    "block_hash": block.hash(), "shard_id": metadata["shard_id"], "chunk_hash": metadata["chunk_hash"],
                    "claim_hash": near_primitives::hash::hash(&cb), "witness_hash": near_primitives::hash::hash(&wb),
                    "facts_source": "pinned native chain store and epoch manager via claim-v3 builder",
                    "native_cache_policy": "fresh transition cache per case; existing node compiled-code cache (not cold W13 adapter)",
                    "native_verdict": if native.is_ok() {"accept"} else {"reject"}, "native_error": native.err().map(|e| format!("{e:?}"))});
                std::fs::write(dest.join("export.json"), serde_json::to_vec_pretty(&row)?)?;
                Ok(row)
            })();
            let row = result.unwrap_or_else(|e| serde_json::json!({"source":src,"export_error":format!("{e:#}")}));
            println!("{}", row);
            rows.push(row);
            std::fs::write(self.output.join("exports.json"), serde_json::to_vec_pretty(&rows).unwrap()).unwrap();
        }
    }
}
