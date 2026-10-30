//! Compiled-cache and preparation-schedule probes of nearcore's stateless validator (W08, UQ-001).
//!
//! The reference judge (`../v3-d3/src/d3judge.rs`, `ColdJudge`) validates a witness with an empty
//! compiled-contract cache. Two questions it cannot answer by itself:
//!
//! 1. **Is the cold verdict a race?** A pre-state contract whose code the witness lacks can still
//!    be executed when an earlier deploy in the chunk (committed: deploy tracker; rolled back:
//!    the deploy's synchronous precompile) holds the same code, unless the call's preparation ran
//!    on a `contract_compilation` worker before that deploy (`runtime/runtime/src/pipelining.rs`
//!    152-424). The judge forces the two extreme schedules with the cache it owns:
//!    * `Eager` — a `put` from the applying thread (the deploy's precompile) first waits, so a
//!      worker task submitted before the deploy has already looked the code up and missed;
//!    * `Lazy`  — a `get` from a worker thread first waits, so by the time it looks the code up
//!      the applying thread has run every earlier deploy (and is blocked on this task).
//!
//!    Equal verdicts: nearcore's result does not depend on the schedule. Different verdicts: it is
//!    a thread race, shown by nearcore itself, not by a model of the scheduler.
//! 2. **Does a warm cache change the verdict?** `Warm` pre-compiles every registry contract (a
//!    coherent cache: each entry is the compilation of bytes whose hash is its key) before the
//!    judgment. `Poisoned` is the deliberate-breakage control: one registry hash is filled with
//!    another contract's compilation (`ContractCode::new(bytes, Some(other_hash))`, whose
//!    hash/bytes coherence is a debug-only assertion in release nearcore).
//!
//! Worker threads are recognised by the name nearcore gives them (`contract_compilation`,
//! `core/async/src/thread_pool.rs:299-310`). Everything else is the reference judge unchanged:
//! `pre_validate_chunk_state_witness` + `validate_chunk_state_witness` on a `NightshadeRuntime`
//! over the judging client's store (the body of `judge_inner` is copied from d3judge.rs, which is
//! pinned and keeps it private).

use crate::judge::decode_witness;
use near_chain::ChainStoreAccess;
use near_chain::runtime::NightshadeRuntime;
use near_chain::stateless_validation::chunk_validation::{
    MainStateTransitionCache, pre_validate_chunk_state_witness, validate_chunk_state_witness,
};
use near_chain::types::RuntimeAdapter;
use near_client::Client;
use near_epoch_manager::{EpochManagerAdapter, EpochManagerHandle};
use near_primitives::hash::CryptoHash;
use near_vm_runner::{CompiledContractInfo, ContractCode, ContractRuntimeCache};
use reed_solomon_erasure::galois_8::ReedSolomon;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Cold = 0,
    Eager = 1,
    Lazy = 2,
    Warm = 3,
    Poisoned = 4,
}

/// Wait long enough that the other side of the race has certainly run: preparation of the small
/// registry contracts takes milliseconds, and so does applying the receipts between submission and
/// the deploy.
fn delay() -> Duration {
    let ms = std::env::var("NEAR_CACHE_PROBE_DELAY_MS").ok().and_then(|v| v.parse().ok()).unwrap_or(400u64);
    Duration::from_millis(ms)
}

fn on_worker() -> bool {
    std::thread::current().name() == Some("contract_compilation")
}

#[derive(Clone)]
pub struct ProbeCache {
    inner: Arc<Mutex<(u64, HashMap<CryptoHash, CompiledContractInfo>)>>,
    mode: Arc<AtomicU8>,
    era: Option<u64>,
}

impl ProbeCache {
    fn new() -> Self {
        ProbeCache { inner: Default::default(), mode: Arc::new(AtomicU8::new(Mode::Cold as u8)), era: None }
    }
    fn clear(&self) {
        let mut g = self.inner.lock().unwrap();
        g.0 += 1;
        g.1.clear();
    }
    fn mode(&self) -> u8 {
        self.mode.load(Ordering::SeqCst)
    }
}

impl ContractRuntimeCache for ProbeCache {
    fn handle(&self) -> Box<dyn ContractRuntimeCache> {
        let cur = self.inner.lock().unwrap().0;
        Box::new(ProbeCache { inner: self.inner.clone(), mode: self.mode.clone(), era: Some(self.era.unwrap_or(cur)) })
    }
    fn put(&self, key: &CryptoHash, value: CompiledContractInfo) -> std::io::Result<()> {
        if self.mode() == Mode::Eager as u8 && !on_worker() {
            std::thread::sleep(delay());
        }
        let mut g = self.inner.lock().unwrap();
        if self.era.unwrap_or(g.0) == g.0 {
            g.1.insert(*key, value);
        }
        Ok(())
    }
    fn get(&self, key: &CryptoHash) -> std::io::Result<Option<CompiledContractInfo>> {
        if self.mode() == Mode::Lazy as u8 && on_worker() {
            std::thread::sleep(delay());
        }
        let g = self.inner.lock().unwrap();
        if self.era.unwrap_or(g.0) != g.0 {
            return Ok(None);
        }
        Ok(g.1.get(key).cloned())
    }
}

/// One probe runtime per TestEnv client (same store and epoch manager as the reference judge).
pub struct CacheJudge {
    rts: Vec<(Arc<NightshadeRuntime>, ProbeCache)>,
    wasm_config: Arc<near_parameters::vm::Config>,
}

impl CacheJudge {
    pub fn new(clients: &[Client], ems: &[Arc<EpochManagerHandle>], genesis: &near_chain_configs::Genesis, home: &std::path::Path) -> Self {
        let rts = clients
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let cache = ProbeCache::new();
                let dir = home.join(format!("probe-{i}"));
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
        let wasm_config = near_parameters::RuntimeConfigStore::new(None)
            .get_config(near_primitives::version::PROTOCOL_VERSION)
            .wasm_config
            .clone();
        CacheJudge { rts, wasm_config }
    }

    /// nearcore's verdict under `mode` on `bytes` with the code blobs `codes` appended.
    pub fn judge(&self, mode: Mode, ci: usize, client: &Client, bytes: &[u8], codes: &[Vec<u8>], rs: (u16, u16)) -> Result<(), String> {
        let (rt, cache) = &self.rts[ci];
        cache.clear();
        match mode {
            Mode::Warm => {
                for (_, code) in crate::d3contracts::all() {
                    let code = ContractCode::new(code, None);
                    let _ = near_vm_runner::precompile_contract(&code, Arc::clone(&self.wasm_config), Some(cache));
                }
            }
            Mode::Poisoned => {
                // every registry contract compiled under the hash of the next one (cyclically):
                // an incoherent cache. A call that hits it runs different code than its hash names.
                let all: Vec<Vec<u8>> = crate::d3contracts::all().into_iter().map(|(_, c)| c).collect();
                for (i, code) in all.iter().enumerate() {
                    let other = CryptoHash::hash_bytes(&all[(i + 1) % all.len()]);
                    let code = ContractCode::new(code.clone(), Some(other));
                    let _ = near_vm_runner::precompile_contract(&code, Arc::clone(&self.wasm_config), Some(cache));
                }
            }
            _ => {}
        }
        cache.mode.store(mode as u8, Ordering::SeqCst);
        let r = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| judge_inner(client, rt.as_ref(), bytes, codes, rs))) {
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
        cache.mode.store(Mode::Cold as u8, Ordering::SeqCst);
        cache.clear();
        r
    }
}

/// Warm and poisoned-cache verdicts are recorded for every case of the `code-cache` scenario, or
/// of any run with `NEAR_CACHE_PROBE_WARM=1` (they cost two extra judgments per case).
pub fn warm_enabled() -> bool {
    crate::d3gen::scenario() == Some(crate::d3gen::Scenario::CodeCache)
        || std::env::var("NEAR_CACHE_PROBE_WARM").is_ok_and(|v| v == "1")
}

/// `{"warm": verdict, "poisoned": verdict}` of the same bytes the cold judge saw.
pub fn cache_probe(p: &CacheJudge, ci: usize, client: &Client, bytes: &[u8], codes: &[Vec<u8>], rs: (u16, u16)) -> serde_json::Value {
    let s = |r: Result<(), String>| r.map(|_| "ok".to_string()).unwrap_or_else(|e| e);
    serde_json::json!({
        "warm": s(p.judge(Mode::Warm, ci, client, bytes, codes, rs)),
        "poisoned": s(p.judge(Mode::Poisoned, ci, client, bytes, codes, rs)),
        "warm_cache": "every registry contract precompiled (coherent)",
        "poisoned_cache": "every registry contract compiled under the next one's hash (incoherent control)",
    })
}

fn judge_inner(client: &Client, rt: &dyn RuntimeAdapter, bytes: &[u8], codes: &[Vec<u8>], rs: (u16, u16)) -> Result<(), String> {
    let w = decode_witness(bytes, codes)?;
    let prev = *w.chunk_header().prev_block_hash();
    client.chain.get_block(&prev).map_err(|e| format!("actor: prev block: {e:?}"))?;
    let em: &dyn EpochManagerAdapter = client.epoch_manager.as_ref();
    let expected = em.get_epoch_id_from_prev_block(&prev).map_err(|e| format!("actor: {e:?}"))?;
    if &expected != w.epoch_id() {
        return Err("actor: InvalidChunkStateWitness epoch id".into());
    }
    let pre = pre_validate_chunk_state_witness(&w, client.chain.chain_store(), client.chain.genesis_block(), em, rt)
        .map_err(|e| format!("pre_validate: {e:?}"))?;
    let (d, total) = (rs.0 as usize, rs.1 as usize);
    if d == 0 || total <= d {
        return Err("rs: invalid parameters".into());
    }
    let rs = Arc::new(ReedSolomon::new(d, total - d).map_err(|e| format!("rs: {e:?}"))?);
    validate_chunk_state_witness(w, pre, em, rt, &MainStateTransitionCache::default(), client.chain.chain_store().store(), false, rs)
        .map_err(|e| format!("validate: {e:?}"))
}
