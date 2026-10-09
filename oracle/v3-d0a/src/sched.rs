//! Independent replica of nearcore's bandwidth-scheduler core (domain D0a, `e.chacha_words`).
//!
//! nearcore keeps the scheduler's `ChaCha20Rng` private, so the number of 32-bit ChaCha20
//! words a run draws is not observable from nearcore. This module copies the state-relevant
//! part of `runtime/runtime/src/bandwidth_scheduler/{mod.rs,scheduler.rs}` (nearcore
//! 44f7ae6c): the shard statuses of `run_bandwidth_scheduler`, `SchedulerBandwidthRequest::new`,
//! `calculate_is_link_allowed`, `init_budgets`, `increase_allowances`, `grant_base_bandwidth`,
//! `try_grant_bandwidth`, `process_bandwidth_requests` (the only RNG user: `requests.shuffle`)
//! and `update_scheduler_state` + the sanity-check hash. `distribute_remaining_bandwidth` only
//! adds to the *granted* bandwidth (`grant_more_bandwidth`), never to budgets or allowances,
//! so it influences neither the written state nor the RNG and is not replicated.
//!
//! The words drawn by a run = `ChaCha20Rng::get_word_pos()` after `process_bandwidth_requests`
//! (rand_chacha 0.3.1, `rand::seq::SliceRandom::shuffle` of rand 0.8.5, as nearcore).
//! The replica is validated against nearcore's actual post-state on every honest run
//! (chaingen) and on every case of `oracle/fixtures/v3/vectors/scheduler.json` (`sched-words`).

use near_parameters::RuntimeConfig;
use near_primitives::bandwidth_scheduler::{
    Bandwidth, BandwidthRequest, BandwidthRequestValues, BandwidthRequests,
    BandwidthSchedulerParams, BandwidthSchedulerState, BandwidthSchedulerStateV1,
    BlockBandwidthRequests, LinkAllowance,
};
use near_primitives::congestion_info::{BlockCongestionInfo, CongestionControl};
use near_primitives::hash::CryptoHash;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::types::{ShardId, ShardIndex};
use rand::SeedableRng;
use rand::seq::SliceRandom;
use rand_chacha::ChaCha20Rng;
use std::collections::{BTreeMap, VecDeque};
use std::num::NonZeroU64;

#[derive(Clone, Copy)]
struct ShardStatus {
    is_fully_congested: bool,
    last_chunk_missing: bool,
    allowed_sender_shard_index: Option<ShardIndex>,
}

struct Req {
    link: (ShardIndex, ShardIndex),
    increases: VecDeque<Bandwidth>,
}

/// Result of one replicated scheduler run.
pub struct Run {
    /// The state nearcore writes to `TrieKey::BandwidthSchedulerState` (0x0f).
    pub state: BandwidthSchedulerState,
    /// ChaCha20 32-bit words drawn (`get_word_pos()` after the run).
    pub words: u64,
}

/// `SchedulerBandwidthRequest::new` (scheduler.rs:610-640).
#[allow(clippy::needless_range_loop)] // kept as nearcore's loop
fn convert(
    sender: ShardId,
    r: &BandwidthRequest,
    params: &BandwidthSchedulerParams,
    layout: &ShardLayout,
) -> Option<Req> {
    let s = layout.get_shard_index(sender).ok()?;
    let t = layout.get_shard_index(r.to_shard.into()).ok()?;
    let mut increases = VecDeque::new();
    let mut current_total = params.base_bandwidth;
    let values = BandwidthRequestValues::new(params).values;
    for bit in 0..r.requested_values_bitmap.len() {
        if !r.requested_values_bitmap.get_bit(bit) {
            continue;
        }
        let v = values[bit];
        if v <= current_total {
            continue;
        }
        increases.push_back(v - current_total);
        current_total = v;
    }
    if increases.is_empty() {
        return None;
    }
    Some(Req {
        link: (s, t),
        increases,
    })
}

/// One `run_bandwidth_scheduler` (mod.rs:44-141) on its inputs: the pre-state value of 0x0f,
/// the epoch's shard layout and runtime config, the block's congestion info (with missed-chunk
/// counts) and bandwidth requests, and the RNG seed `ApplyState.prev_block_hash`.
pub fn run(
    layout: &ShardLayout,
    prev: Option<BandwidthSchedulerState>,
    config: &RuntimeConfig,
    congestion: &BlockCongestionInfo,
    requests: &BlockBandwidthRequests,
    seed: [u8; 32],
) -> Run {
    let BandwidthSchedulerState::V1(mut st) =
        prev.unwrap_or(BandwidthSchedulerState::V1(BandwidthSchedulerStateV1 {
            link_allowances: Vec::new(),
            sanity_check_hash: CryptoHash::default(),
        }));
    let n = layout.num_shards() as usize;
    // shard statuses (mod.rs:72-95)
    let mut status: Vec<Option<ShardStatus>> = vec![None; n];
    for (sid, ext) in congestion.iter() {
        let cc = CongestionControl::new(
            config.congestion_control_config,
            ext.congestion_info,
            ext.missed_chunks_count,
        );
        let s = ShardStatus {
            last_chunk_missing: ext.missed_chunks_count > 0,
            allowed_sender_shard_index: layout
                .get_shard_index(ext.congestion_info.allowed_shard().into())
                .ok(),
            is_fully_congested: CongestionControl::is_fully_congested(cc.congestion_level()),
        };
        if let Ok(i) = layout.get_shard_index(*sid) {
            status[i] = Some(s);
        }
    }
    let params = BandwidthSchedulerParams::new(
        NonZeroU64::new(layout.num_shards()).expect("zero shards"),
        config,
    );
    let all_shards: Vec<ShardId> = layout.shard_ids().collect();
    let mut rng = ChaCha20Rng::from_seed(seed);
    if n > 0 {
        let link = |s: usize, r: usize| s * n + r;
        let mut allowance: Vec<Option<Bandwidth>> = vec![None; n * n];
        for la in &st.link_allowances {
            if let (Ok(s), Ok(r)) = (
                layout.get_shard_index(la.sender),
                layout.get_shard_index(la.receiver),
            ) {
                allowance[link(s, r)] = Some(la.allowance);
            }
        }
        // calculate_is_link_allowed
        let mut allowed = vec![false; n * n];
        for s in 0..n {
            for r in 0..n {
                allowed[link(s, r)] = match &status[r] {
                    None => false,
                    Some(rs) if rs.last_chunk_missing => false,
                    Some(_) if status[s].is_some_and(|x| x.last_chunk_missing) => false,
                    Some(rs) if rs.is_fully_congested => rs.allowed_sender_shard_index == Some(s),
                    Some(_) => true,
                };
            }
        }
        let mut reqs: Vec<Req> = Vec::new();
        for (sender, br) in &requests.shards_bandwidth_requests {
            let BandwidthRequests::V1(v1) = br;
            for r in &v1.requests {
                if let Some(q) = convert(*sender, r, &params, layout) {
                    reqs.push(q);
                }
            }
        }
        // init_budgets
        let mut sender_budget = vec![params.max_shard_bandwidth; n];
        let mut receiver_budget = vec![params.max_shard_bandwidth; n];
        let get = |a: &Vec<Option<Bandwidth>>, l: usize| a[l].unwrap_or(0);
        // increase_allowances
        let fair = params.max_shard_bandwidth / n as u64;
        for l in 0..n * n {
            let v = get(&allowance, l)
                .saturating_add(fair)
                .min(params.max_allowance);
            allowance[l] = Some(v);
        }
        // try_grant_bandwidth (granted amounts are not part of the state)
        let mut try_grant = |allowance: &mut Vec<Option<Bandwidth>>,
                             (s, r): (usize, usize),
                             bw: Bandwidth|
         -> bool {
            if !allowed[link(s, r)] || sender_budget[s] < bw || receiver_budget[r] < bw {
                return false;
            }
            sender_budget[s] -= bw;
            receiver_budget[r] -= bw;
            allowance[link(s, r)] = Some(get(allowance, link(s, r)).saturating_sub(bw));
            true
        };
        // grant_base_bandwidth
        for s in 0..n {
            for r in 0..n {
                let _ = try_grant(&mut allowance, (s, r), params.base_bandwidth);
            }
        }
        // process_bandwidth_requests
        let mut by_allowance: BTreeMap<Bandwidth, Vec<Req>> = BTreeMap::new();
        for q in reqs {
            by_allowance
                .entry(get(&allowance, link(q.link.0, q.link.1)))
                .or_default()
                .push(q);
        }
        while let Some((_a, mut v)) = by_allowance.pop_last() {
            v.shuffle(&mut rng);
            for mut q in v {
                let Some(inc) = q.increases.pop_front() else {
                    continue;
                };
                if try_grant(&mut allowance, q.link, inc) && !q.increases.is_empty() {
                    by_allowance
                        .entry(get(&allowance, link(q.link.0, q.link.1)))
                        .or_default()
                        .push(q);
                }
            }
        }
        // update_scheduler_state
        let mut la = Vec::new();
        for s in 0..n {
            for r in 0..n {
                if let Some(a) = allowance[link(s, r)] {
                    la.push(LinkAllowance {
                        sender: layout.get_shard_id(s).unwrap(),
                        receiver: layout.get_shard_id(r).unwrap(),
                        allowance: a,
                    });
                }
            }
        }
        st.link_allowances = la;
    }
    // sanity-check hash (mod.rs:112-123)
    let mut b = Vec::new();
    b.extend_from_slice(st.sanity_check_hash.as_ref());
    b.extend_from_slice(CryptoHash::hash_borsh(&all_shards).as_ref());
    st.sanity_check_hash = CryptoHash::hash_bytes(&b);
    let words = u64::try_from(rng.get_word_pos()).expect("word pos fits u64");
    Run {
        state: BandwidthSchedulerState::V1(st),
        words,
    }
}
