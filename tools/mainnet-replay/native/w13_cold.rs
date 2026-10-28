//! Cold native W13 adapter (tools/mainnet-replay/README.md, "Native adapter contract").
//!
//! `neard --home HOME view-state state-witness cold-validate CASE_DIR` validates one externally
//! supplied `claim.bin` / `witness.bin` pair against the node's own canonical mainnet store and
//! epoch manager, and prints exactly one JSON object on stdout.
//!
//! * Cold: the compiled-contract cache is a fresh, empty `FilesystemContractRuntimeCache` in a new
//!   temporary home, created per case and deleted afterwards. The node's warm `data/contracts`
//!   cache is never consulted. Contract code comes only from `witness.bin`'s `contract_code`, merged
//!   into the main transition's `base_state` exactly as `partial_witness_tracker.rs:692-696` does.
//!   The main-transition result cache is fresh.
//! * Facts: every trusted claim value (spec/claim-v3.md §2.4, T1–T14) and the authenticated segment
//!   are recomputed from the node's store and epoch manager, and the supplied claim must be
//!   byte-identical. T1 (`epoch_id`) is additionally checked against
//!   `get_epoch_id_from_prev_block`, not only against the witness.
//! * Finality/provenance: the chunk's including block must be the canonical block at its height in
//!   the node's store, contain this chunk as a new chunk, and be at or below the store's final head
//!   (doomslug finality as accepted by the node's own header processing). This is the trust root;
//!   it is not an independent light-client proof.
//! * Verdict: pinned `pre_validate_chunk_state_witness` + `validate_chunk_state_witness`, run
//!   synchronously. Their `Result` is the verdict; nothing is inferred from logs or exit status.
#[path = "w13_enc.rs"]
mod enc;
#[path = "w13_claim.rs"]
mod claim;

use near_chain::ChainStoreAccess;
use near_chain::stateless_validation::chunk_validation::{
    MainStateTransitionCache, pre_validate_chunk_state_witness, validate_chunk_state_witness,
};
use near_epoch_manager::EpochManagerAdapter;
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::contract_distribution::MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE;
use near_primitives::stateless_validation::partial_witness::MAX_COMPRESSED_STATE_WITNESS_SIZE;
use near_primitives::stateless_validation::state_witness::{
    ChunkStateWitness, EncodedChunkStateWitness, MAX_UNCOMPRESSED_STATE_WITNESS_SIZE,
};
use near_primitives::utils::compression::CompressedData;
use near_store::Store;
use nearcore::{NearConfig, NightshadeRuntimeExt};
use reed_solomon_erasure::galois_8::ReedSolomon;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Set by the build recipe from `git rev-parse HEAD` of the pinned checkout (native/README.md).
const NEARCORE_COMMIT: &str = env!("W13_NEARCORE_COMMIT");
const PLAIN_TAG: &[u8] = b"near-arena-witness-v3";
const COMPRESSED_TAG: &[u8] = b"near-arena-cwitness-v3";

#[derive(clap::Parser)]
pub struct ColdValidateCmd {
    /// Case directory holding `claim.bin` and `witness.bin` (appended by gate.py).
    case: PathBuf,
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn sha256_hex(b: &[u8]) -> String {
    hex(&near_primitives::hash::hash(b).0)
}

struct Envelope {
    compressed: bool,
    state_witness: Vec<u8>,
    codes: Vec<Vec<u8>>,
}

fn take<'a>(b: &'a [u8], off: &mut usize) -> anyhow::Result<&'a [u8]> {
    anyhow::ensure!(b.len() >= *off + 4, "witness.bin truncated");
    let n = u32::from_le_bytes(b[*off..*off + 4].try_into().unwrap()) as usize;
    *off += 4;
    anyhow::ensure!(b.len() - *off >= n, "witness.bin truncated");
    let out = &b[*off..*off + n];
    *off += n;
    Ok(out)
}

fn parse_envelope(b: &[u8]) -> anyhow::Result<Envelope> {
    let mut off = 0;
    let tag = take(b, &mut off)?;
    let compressed = match tag {
        PLAIN_TAG => false,
        COMPRESSED_TAG => true,
        _ => anyhow::bail!("unknown witness.bin format id"),
    };
    let state_witness = take(b, &mut off)?.to_vec();
    anyhow::ensure!(b.len() >= off + 4, "witness.bin truncated");
    let count = u32::from_le_bytes(b[off..off + 4].try_into().unwrap()) as usize;
    off += 4;
    let mut codes = Vec::new();
    for _ in 0..count {
        codes.push(take(b, &mut off)?.to_vec());
    }
    anyhow::ensure!(off == b.len(), "trailing bytes after witness.bin");
    Ok(Envelope { compressed, state_witness, codes })
}

/// First differing byte offset, for diagnostics only.
fn first_difference(a: &[u8], b: &[u8]) -> Option<usize> {
    a.iter().zip(b).position(|(x, y)| x != y).or((a.len() != b.len()).then(|| a.len().min(b.len())))
}

/// A fresh, empty temporary home for the cold compiled-contract cache.
struct ColdHome(PathBuf);
impl ColdHome {
    fn new() -> anyhow::Result<Self> {
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos();
        let p = std::env::temp_dir().join(format!("w13-cold-{}-{nanos}", std::process::id()));
        std::fs::create_dir(&p)?; // fails if it already exists: never reuse a cache
        Ok(Self(p))
    }
}
impl Drop for ColdHome {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn dir_entries(p: &Path) -> usize {
    std::fs::read_dir(p).map(|d| d.count()).unwrap_or(0)
}

impl ColdValidateCmd {
    pub(crate) fn run(&self, home: &Path, config: NearConfig, store: Store) {
        let out = self.run_inner(home, config, store).unwrap_or_else(|e| {
            // Still one JSON object; facts are unverified and there is no verdict, so gate.py
            // records an error rather than a match or a mismatch.
            serde_json::json!({"chain_id": "mainnet", "nearcore_commit": NEARCORE_COMMIT,
                               "facts_verified": false, "verdict": null,
                               "adapter_error": format!("{e:#}")})
        });
        println!("{}", out);
    }

    fn run_inner(&self, home: &Path, config: NearConfig, store: Store) -> anyhow::Result<serde_json::Value> {
        anyhow::ensure!(config.genesis.config.chain_id == "mainnet", "node home is not mainnet");
        let claim_bytes = std::fs::read(self.case.join("claim.bin"))?;
        let witness_bytes = std::fs::read(self.case.join("witness.bin"))?;
        let env = parse_envelope(&witness_bytes)?;

        // Size limits as a validator receiving this witness applies them.
        let mut size_reject: Option<String> = None;
        let witness: ChunkStateWitness = if env.compressed {
            if env.state_witness.len() as u64 > MAX_COMPRESSED_STATE_WITNESS_SIZE.as_u64() {
                anyhow::bail!("encoded witness exceeds MAX_COMPRESSED_STATE_WITNESS_SIZE; nearcore never decodes it");
            }
            EncodedChunkStateWitness::from(env.state_witness.clone().into_boxed_slice()).decode()?.0
        } else {
            if env.state_witness.len() as u64 > MAX_UNCOMPRESSED_STATE_WITNESS_SIZE {
                size_reject = Some("state witness exceeds MAX_UNCOMPRESSED_STATE_WITNESS_SIZE".into());
            }
            borsh::from_slice(&env.state_witness)?
        };
        // Borsh size of the Vec<CodeBytes> a cold validator must receive in ContractCodeResponse.
        // Conservative: counts every supplied blob, including deploy-only code.
        let code_response_bytes: u64 = 4 + env.codes.iter().map(|c| 4 + c.len() as u64).sum::<u64>();
        let code_response_ok = code_response_bytes <= MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE;

        let em = near_epoch_manager::EpochManager::new_arc_handle(store.clone(), &config.genesis.config, Some(home));
        let chain = super::setup_chain(home, config.clone(), store.clone());
        let cs = chain.chain_store();
        let header = witness.chunk_header().clone();
        let chunk_hash = header.chunk_hash().clone();
        let height = header.height_created();
        let prev = *header.prev_block_hash();

        // Finality / provenance boundary.
        let included_hash = cs.get_block_hash_by_height(height)?;
        let included = cs.get_block(&included_hash)?;
        let final_head = cs.final_head()?;
        let in_block = included.chunks().iter_raw().any(|c| c.chunk_hash() == &chunk_hash && c.height_included() == height);
        let canonical = *included.header().prev_hash() == prev && in_block;
        let is_final = height <= final_head.height
            && cs.get_block_hash_by_height(final_head.height)? == final_head.last_block_hash;
        let epoch_from_store = em.get_epoch_id_from_prev_block(&prev)?;
        let pv = em.get_epoch_protocol_version(&epoch_from_store)?;

        // Trusted facts: recompute the whole claim from the native store; demand byte equality.
        let built = claim::build_claim(&chain, &em, &config.genesis.config, &witness).map_err(|e| anyhow::anyhow!(e))?;
        let expected = built.claim.encode();
        let claim_equal = expected == claim_bytes;
        let epoch_ok = epoch_from_store == *witness.epoch_id();
        let facts_verified = claim_equal && epoch_ok && canonical && is_final && pv == 86;

        // Cold validation.
        let cold = ColdHome::new()?;
        let mut cold_config = config.clone();
        cold_config.config.store.state_snapshot_config.state_snapshot_type =
            near_store::config::StateSnapshotType::Disabled;
        // A relative store path keeps the cache's legacy-directory migration inside the temporary
        // home; an explicit absolute contract_cache_path would point at a real (warm) cache.
        cold_config.config.store.path = None;
        let cache_dir = cold.0.join(cold_config.config.contract_cache_path());
        anyhow::ensure!(cache_dir.starts_with(&cold.0),
            "configured contract_cache_path escapes the temporary home; refusing a possibly warm cache");
        anyhow::ensure!(!cache_dir.exists(), "cold cache directory already exists");
        let runtime = near_chain::runtime::NightshadeRuntime::from_config(&cold.0, store.clone(), &cold_config, em.clone())?;
        // Created empty by from_config; counted before any execution.
        let entries_before = dir_entries(&cache_dir);
        let mut witness = witness;
        let PartialState::TrieValues(values) = &mut witness.mut_main_state_transition().base_state;
        values.extend(env.codes.iter().map(|c| Arc::<[u8]>::from(c.as_slice())));
        let data = em.num_data_parts();
        let rs = Arc::new(ReedSolomon::new(data, em.num_total_parts() - data)?);
        let started = std::time::Instant::now();
        let native = match &size_reject {
            Some(r) => Err(r.clone()),
            None => pre_validate_chunk_state_witness(&witness, cs, chain.genesis_block(), em.as_ref(), runtime.as_ref())
                .and_then(|pre| validate_chunk_state_witness(witness, pre, em.as_ref(), runtime.as_ref(),
                    &MainStateTransitionCache::default(), store.clone(), false, rs))
                .map_err(|e| format!("{e:?}")),
        };
        let elapsed = started.elapsed().as_secs_f64();
        let entries_after = dir_entries(&cache_dir);
        // A cold validator that cannot receive the code cannot endorse: out of domain
        // (`w.code_response_size`), reported as a native reject with that reason.
        let verdict = if native.is_ok() && code_response_ok { "accept" } else { "reject" };

        Ok(serde_json::json!({
            "chain_id": config.genesis.config.chain_id,
            "nearcore_commit": NEARCORE_COMMIT,
            "block_hash": included_hash.to_string(),
            "chunk_hash": chunk_hash.0.to_string(),
            "shard_id": header.shard_id(),
            "height": height,
            "claim_sha256": sha256_hex(&claim_bytes),
            "witness_sha256": sha256_hex(&witness_bytes),
            "facts_verified": facts_verified,
            "verdict": verdict,
            "native_error": native.err(),
            "native_seconds": elapsed,
            "facts": {
                "method": "claim recomputed from the node's canonical store and epoch manager; byte equality",
                "claim_equal": claim_equal,
                "first_difference_offset": first_difference(&expected, &claim_bytes),
                "expected_claim_sha256": sha256_hex(&expected),
                "epoch_id_matches_get_epoch_id_from_prev_block": epoch_ok,
                "protocol_version": pv,
            },
            "finality": {
                "source": "node store: canonical block at height_created and final head",
                "included_block_hash": included_hash.to_string(),
                "included_block_height": height,
                "canonical": canonical,
                "final": is_final,
                "final_head_height": final_head.height,
                "final_head_hash": final_head.last_block_hash.to_string(),
                "segment_blocks": built.blocks.len(),
            },
            "cache": {
                "policy": "cold",
                "compiled_contract_cache": "fresh empty FilesystemContractRuntimeCache in a new temporary home",
                "entries_before": entries_before,
                "entries_after": entries_after,
                "main_transition_cache": "fresh",
                "code_source": "witness.bin contract_code merged into main_state_transition.base_state",
            },
            "code": {
                "blobs": env.codes.len(),
                "response_bytes_upper_bound": code_response_bytes,
                "response_within_limit": code_response_ok,
            },
            "witness_format": if env.compressed {"near-arena-cwitness-v3"} else {"near-arena-witness-v3"},
        }))
    }
}
