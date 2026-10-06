//! The D3 reference judge: nearcore's stateless validator (`pre_validate_chunk_state_witness`
//! + `validate_chunk_state_witness`, exactly oracle/v3/src/judge.rs) run by a *cold*
//! validator — a `NightshadeRuntime` over the judging client's store and epoch manager whose
//! compiled-contract cache is empty at the start of every judgment.
//!
//! Why: in nearcore 2.13.4 the witness carries no contract code (README.md "How a stateless
//! validator obtains contract code"). A validator executes a FunctionCall from its compiled-
//! contract cache when the code hash is cached, and otherwise needs the code bytes among the
//! witness's trie values; the code blobs a validator fetched with `ContractCodeRequest` are
//! merged into `main_state_transition.base_state` exactly as `decode_witness` does with the
//! blobs appended to witness.bin (partial_witness_tracker.rs:693-696). The TestEnv clients'
//! caches are warm (they apply every chunk), so their verdict does not depend on the appended
//! codes; a cold validator's does: a missing executed code is `MissingTrieValue`
//! (runtime/runtime/src/function_call.rs:293-305), a reject. `Rel` is defined for this
//! cache-independent validator.

use crate::judge::decode_witness;
use near_chain::ChainStoreAccess;
use near_chain::runtime::NightshadeRuntime;
use near_chain::stateless_validation::chunk_validation::{
    MainStateTransitionCache, MainTransition, pre_validate_chunk_state_witness, validate_chunk_state_witness,
};
use near_chain::types::RuntimeAdapter;
use near_client::Client;
use near_epoch_manager::{EpochManagerAdapter, EpochManagerHandle};
use near_primitives::hash::CryptoHash;
use near_vm_runner::{CompiledContractInfo, ContractRuntimeCache};
use reed_solomon_erasure::galois_8::ReedSolomon;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// An in-memory compiled-contract cache that can be emptied. Every `handle()` (taken per apply
/// and per pipelined preparation task) is bound to the generation current when it was taken;
/// `clear()` starts a new generation, so a preparation task still running from an earlier
/// judgment can neither read nor fill the cache of the next one.
#[derive(Clone, Default)]
pub struct ColdCache {
    inner: Arc<Mutex<(u64, HashMap<CryptoHash, CompiledContractInfo>)>>,
    era: Option<u64>,
}

impl ColdCache {
    pub fn clear(&self) {
        let mut g = self.inner.lock().unwrap();
        g.0 += 1;
        g.1.clear();
    }
}

impl ContractRuntimeCache for ColdCache {
    fn handle(&self) -> Box<dyn ContractRuntimeCache> {
        let cur = self.inner.lock().unwrap().0;
        Box::new(ColdCache { inner: self.inner.clone(), era: Some(self.era.unwrap_or(cur)) })
    }
    fn put(&self, key: &CryptoHash, value: CompiledContractInfo) -> std::io::Result<()> {
        let mut g = self.inner.lock().unwrap();
        if self.era.unwrap_or(g.0) == g.0 {
            g.1.insert(*key, value);
        }
        Ok(())
    }
    fn get(&self, key: &CryptoHash) -> std::io::Result<Option<CompiledContractInfo>> {
        let g = self.inner.lock().unwrap();
        if self.era.unwrap_or(g.0) != g.0 {
            return Ok(None);
        }
        Ok(g.1.get(key).cloned())
    }
}

/// One cold validator runtime per TestEnv client (same store and epoch manager).
pub struct ColdJudge {
    rts: Vec<(Arc<NightshadeRuntime>, ColdCache)>,
}

impl ColdJudge {
    pub fn new(clients: &[Client], ems: &[Arc<EpochManagerHandle>], genesis: &near_chain_configs::Genesis, home: &std::path::Path) -> Self {
        let rts = clients
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let cache = ColdCache::default();
                let dir = home.join(format!("cold-{i}"));
                std::fs::create_dir_all(&dir).unwrap();
                let rt = NightshadeRuntime::test_with_runtime_config_store(
                    &dir,
                    c.chain.chain_store().store(),
                    Box::new(cache.clone()),
                    &genesis.config,
                    ems[i].clone(),
                    near_parameters::RuntimeConfigStore::new(None),
                );
                (rt, cache)
            })
            .collect();
        ColdJudge { rts }
    }

    /// nearcore's verdict by a cold validator on `bytes` (borsh ChunkStateWitness) with the
    /// code blobs `codes` appended; `tx_valid` replaces the store's transaction-validity
    /// answers (D1 trusted-fact mutants, as oracle/v3-d1/src/d1judge.rs). Panics reject.
    pub fn judge(&self, ci: usize, client: &Client, bytes: &[u8], codes: &[Vec<u8>], rs: (u16, u16), tx_valid: Option<&[u8]>) -> Result<(), String> {
        let (rt, cache) = &self.rts[ci];
        cache.clear();
        let r = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| judge_inner(client, rt.as_ref(), bytes, codes, rs, tx_valid))) {
            Ok(r) => r,
            Err(p) => {
                let msg = p
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_default();
                Err(format!("panic: {msg}"))
            }
        };
        cache.clear();
        r
    }
}

fn judge_inner(
    client: &Client,
    rt: &dyn RuntimeAdapter,
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
    let mut pre = pre_validate_chunk_state_witness(&w, client.chain.chain_store(), client.chain.genesis_block(), em, rt)
        .map_err(|e| format!("pre_validate: {e:?}"))?;
    if let Some(flags) = tx_valid {
        if let MainTransition::NewChunk { new_chunk_data, .. } = &mut pre.main_transition_params {
            let (txs, _) = new_chunk_data.transactions.get_potentially_expired_transactions_and_expiration_flags();
            if flags.len() != txs.len() {
                return Err("tx_valid length differs from transactions".into());
            }
            new_chunk_data.transactions =
                node_runtime::SignedValidPeriodTransactions::new(txs.to_vec(), flags.iter().map(|f| *f != 0).collect());
        }
    }
    let (d, total) = (rs.0 as usize, rs.1 as usize);
    if d == 0 || total <= d {
        return Err("rs: invalid parameters".into());
    }
    let rs = Arc::new(ReedSolomon::new(d, total - d).map_err(|e| format!("rs: {e:?}"))?);
    validate_chunk_state_witness(w, pre, em, rt, &MainStateTransitionCache::default(), client.chain.chain_store().store(), false, rs)
        .map_err(|e| format!("validate: {e:?}"))
}
