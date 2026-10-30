//! Targeted successor traffic around the unchanged baseline workload.
#[path = "../../v3-d3/src/d3gen.rs"]
mod baseline;
pub use baseline::*;
use near_primitives::action::{Action, FunctionCallAction};
use near_primitives::hash::CryptoHash;
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{Balance, Gas};
use rand::{Rng, rngs::StdRng};

pub struct D3World {
    inner: baseline::D3World,
    next_step: usize,
    next_height: u64,
    /// curve-hosts: (height, steps submitted at it)
    curve_at: (u64, usize),
    driver: crate::scenarios::Driver,
    /// cross-family scenarios (src/xfam.rs)
    xfam: crate::xfam::Driver,
    /// pipeline-race: (next step, next height)
    race: (usize, u64),
}

/// Curve-hosts steps submitted per block height; later steps wait for the next height.
const CURVE_STEPS_PER_HEIGHT: usize = 3;
impl D3World {
    pub fn new(n_shards: usize) -> Self {
        Self::with_seed(n_shards, None)
    }

    /// As `new`, with the chain's generator seed passed to the scenario driver (`storage-limits`
    /// honours it; see `scenarios::Driver::with_seed`).
    pub fn with_seed(n_shards: usize, seed: Option<u64>) -> Self {
        Self {
            inner: baseline::D3World::new(n_shards),
            next_step: 0,
            next_height: 10004,
            curve_at: (0, 0),
            driver: crate::scenarios::Driver::with_seed(seed),
            xfam: crate::xfam::Driver::new(),
            race: (0, 10004),
        }
    }
    /// Scheduled transactions of the opt-in `yield` / `storage-limits` scenarios (none otherwise).
    pub fn scenario_txs(
        &mut self,
        w: &mut crate::d2gen::World,
        s: &crate::chaingen::Setup,
        bh: &CryptoHash,
        height: u64,
    ) -> Vec<(String, SignedTransaction)> {
        let mut txs = self.driver.txs(w, s, bh, height);
        txs.extend(self.xfam.txs(w, s, bh, height));
        if scenario() == Some(Scenario::PipelineRace) && height >= self.race.1 {
            let (next, wait, batch) = race_round(self.race.0, w, s, bh);
            if !batch.is_empty() {
                self.race = (next, height + wait);
                txs.extend(batch);
            }
        }
        if scenario() == Some(Scenario::CodeCache) {
            txs.extend(code_cache_txs(w, s, bh, height));
        }
        txs
    }
    pub fn finish(&self, s: &crate::chaingen::Setup, out: &std::path::Path, chain_idx: usize) {
        self.driver.finish(s, out, chain_idx);
        self.xfam.finish(s, out, chain_idx);
    }
    pub fn one(
        &mut self,
        w: &mut crate::d2gen::World,
        s: &crate::chaingen::Setup,
        bh: &CryptoHash,
        height: u64,
        rng: &mut StdRng,
    ) -> Option<(String, SignedTransaction)> {
        if scenario() == Some(Scenario::CurveHosts) && height >= self.next_height {
            if self.curve_at.0 != height {
                self.curve_at = (height, 0);
            }
            if self.curve_at.1 < CURVE_STEPS_PER_HEIGHT {
                if let Some(step) = crate::curve_hosts::steps().get(self.next_step) {
                    let (a, b) = (
                        baseline::acct(crate::curve_hosts::ACCOUNT_A),
                        baseline::acct(crate::curve_hosts::ACCOUNT_B),
                    );
                    // receivers alternate between the two contract accounts (different shards);
                    // every third step is signed by the other one, so its receipt crosses shards
                    let (recv, other) = if self.next_step % 2 == 0 { (a, b) } else { (b, a) };
                    let signer = if self.next_step % 3 == 0 { other } else { recv.clone() };
                    let action = Action::FunctionCall(Box::new(FunctionCallAction {
                        method_name: step.method.into(),
                        args: step.args.clone(),
                        gas: Gas::from_teragas(step.tgas),
                        deposit: Balance::ZERO,
                    }));
                    if let Some(tx) = w.plain_tx(s, bh, &signer, &recv, vec![action]) {
                        self.next_step += 1;
                        self.curve_at.1 += 1;
                        return Some((step.label.clone(), tx));
                    }
                }
            }
        }
        if scenario() == Some(Scenario::GlobalCache) && height >= self.next_height {
            if let Some((label, signer, receiver, actions)) = global_step(self.next_step) {
                if let Some(tx) = w.plain_tx(s, bh, &signer, &receiver, actions) {
                    // Cross-account rollback and pre-state call may share a block, exercising
                    // preparation ordering. Every other step waits for distribution/receipt delivery.
                    self.next_height = height + if self.next_step == 13 { 0 } else { 6 };
                    self.next_step += 1;
                    return Some((label, tx));
                }
            }
        }
        if std::env::var_os("NEAR_SUCCESSOR_CONTRACT").is_some() && rng.gen_bool(0.5) {
            let shard = rng.gen_range(0..s.accounts.len());
            let signer = &s.accounts[shard][rng.gen_range(0..crate::d2gen::HONEST)];
            let receiver = baseline::acct("s0fl");
            let args = (0..32).map(|_| rng.r#gen()).collect();
            let target_gas = std::env::var("NEAR_SUCCESSOR_GAS_TGAS")
                .map(|value| {
                    value
                        .parse::<u64>()
                        .expect("NEAR_SUCCESSOR_GAS_TGAS must be an integer")
                })
                .unwrap_or(20);
            assert!(
                (1..=300).contains(&target_gas),
                "NEAR_SUCCESSOR_GAS_TGAS must be in 1..=300"
            );
            let action = Action::FunctionCall(Box::new(FunctionCallAction {
                method_name: "run".into(),
                args,
                gas: Gas::from_teragas(target_gas),
                deposit: Balance::from_yoctonear(rng.gen_range(0..1000)),
            }));
            return w
                .plain_tx(s, bh, signer, &receiver, vec![action])
                .map(|tx| ("successor.target_call".into(), tx));
        }
        self.inner.one(w, s, bh, height, rng)
    }
}

/// Dedicated accounts prevent the baseline adversarial workload from replacing scenario keys.
/// The global scenario is opt-in; the pinned D3 oracle and default generator remain unchanged.
pub fn genesis_records(
    accounts: &[Vec<near_primitives::types::AccountId>],
) -> (Vec<near_primitives::state_record::StateRecord>, Balance) {
    use near_crypto::InMemorySigner;
    use near_primitives::{
        account::{AccessKey, AccountContract},
        state_record::StateRecord,
    };
    use near_primitives_core::account::Account;
    let (mut records, mut supply) = baseline::genesis_records(accounts);
    let funded: &[(&str, &[u8])] = match scenario() {
        None => &[],
        Some(Scenario::GlobalCache) => &[
            ("s0global", crate::d3contracts::TINY),
            ("s1globalhash", crate::d3contracts::TINY),
            ("s2globalacct", crate::d3contracts::TINY),
            ("s0cacheleft", crate::d3contracts::TINY),
            ("s0cacheright", crate::d3contracts::TINY),
        ],
        Some(Scenario::CurveHosts | Scenario::Keys | Scenario::Mldsa | Scenario::Yield
             | Scenario::StorageLimits | Scenario::FuelStress | Scenario::EvalTime
             | Scenario::GateBCaps) => &[],
        Some(_) => &[],
    };
    let curve: Vec<(&str, &[u8])> = if scenario() == Some(Scenario::CurveHosts) {
        let code = crate::curve_hosts::code();
        vec![(crate::curve_hosts::ACCOUNT_A, code), (crate::curve_hosts::ACCOUNT_B, code)]
    } else {
        vec![]
    };
    {
        for &(name, code) in funded.iter().chain(curve.iter()) {
            let account_id = baseline::acct(name);
            let amount = Balance::from_near(1_000_000);
            records.push(StateRecord::Account {
                account_id: account_id.clone(),
                account: Account::new(
                    amount,
                    Balance::ZERO,
                    AccountContract::Local(CryptoHash::hash_bytes(code)),
                    10_000,
                ),
            });
            records.push(StateRecord::access_key(
                account_id.clone(),
                &InMemorySigner::test_signer(&account_id).public_key(),
                AccessKey::full_access(),
            ));
            records.push(StateRecord::Contract {
                account_id,
                code: code.to_vec(),
            });
            supply = supply.checked_add(amount).unwrap();
        }
    }
    if scenario() == Some(Scenario::CodeCache) {
        // `code_cache_txs`: one TINY pre-state contract and two code-less accounts per shard
        for k in 0..accounts.len() {
            for (name, code) in [("ccpre", Some(crate::d3contracts::TINY)), ("ccdep", None), ("ccrb", None)] {
                let account_id = baseline::acct(&format!("s{k}{name}"));
                let amount = Balance::from_near(1_000_000);
                let contract = match code {
                    Some(c) => AccountContract::Local(CryptoHash::hash_bytes(c)),
                    None => AccountContract::None,
                };
                records.push(StateRecord::Account {
                    account_id: account_id.clone(),
                    account: Account::new(amount, Balance::ZERO, contract, 10_000),
                });
                records.push(StateRecord::access_key(
                    account_id.clone(),
                    &InMemorySigner::test_signer(&account_id).public_key(),
                    AccessKey::full_access(),
                ));
                if let Some(c) = code {
                    records.push(StateRecord::Contract { account_id, code: c.to_vec() });
                }
                supply = supply.checked_add(amount).unwrap();
            }
        }
    }
    if crate::keys::enabled() {
        let (extra, amount) = crate::keys::genesis_records();
        records.extend(extra);
        supply = supply.checked_add(amount).unwrap();
    }
    if scenario() == Some(Scenario::PipelineRace) {
        let mut add = |name: &str, code: Option<&[u8]>| {
            let account_id = baseline::acct(name);
            let amount = Balance::from_near(1_000_000);
            let contract = match code {
                Some(c) => AccountContract::Local(CryptoHash::hash_bytes(c)),
                None => AccountContract::None,
            };
            records.push(StateRecord::Account {
                account_id: account_id.clone(),
                account: Account::new(amount, Balance::ZERO, contract, 10_000),
            });
            records.push(StateRecord::access_key(
                account_id.clone(),
                &InMemorySigner::test_signer(&account_id).public_key(),
                AccessKey::full_access(),
            ));
            if let Some(c) = code {
                records.push(StateRecord::Contract { account_id, code: c.to_vec() });
            }
            supply = supply.checked_add(amount).unwrap();
        };
        add(RACE_OWNER, Some(crate::d3contracts::TINY));
        add(RACE_GLOBAL_USER, Some(crate::d3contracts::TINY));
        for k in 0..RACE_ROUNDS {
            add(&race_target(k), None);
        }
    }
    let (extra, extra_supply) = crate::xfam::genesis_records(accounts.len());
    records.extend(extra);
    supply = supply.checked_add(extra_supply).unwrap();
    let (extra, extra_supply) = crate::scenarios::genesis_records(accounts.len());
    records.extend(extra);
    supply = supply.checked_add(extra_supply).unwrap();
    (records, supply)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scenario {
    GlobalCache,
    CurveHosts,
    /// `keys` (src/keys.rs): secp256k1 / ML-DSA-65 / gas-key steps.
    Keys,
    /// `mldsa` (src/keys.rs, `step_mldsa`): ML-DSA-65 transaction, delegate, gas-key and
    /// receipt-signer steps, malformed signatures and verification-cost balance boundaries.
    Mldsa,
    /// `yield` / `storage-limits` (src/scenarios.rs).
    Yield,
    StorageLimits,
    /// `fuel-stress` (src/scenarios.rs, W02): interpreter-step and non-metered-work maxima.
    FuelStress,
    /// `eval-time` (src/scenarios.rs, W02): the zero-fee control shapes the Lean arcs target.
    EvalTime,
    /// cross-family scenarios (src/xfam.rs)
    YieldCongestion,
    /// `yield-congestion-v2parent`: `yield-congestion` on a genesis layout that is V2 **with** a
    /// parent map (every shard its own parent, as mainnet's unsplit shards since PV75), so the
    /// bandwidth requests chain each shard's own buffer twice (`congestion_control.rs:545-554`).
    YieldCongestionV2Parent,
    CurveCallbacks,
    GenesisTx,
    GasKeyTarget,
    RollbackRefund,
    /// `runtime-errors` (src/xfam.rs, src/rterr.rs, W03): instance-layout `LoadingError`, import
    /// `LinkError` and the preparation checks that precede them, in whole chunks.
    RuntimeErrors,
    /// `gate-b-caps` (src/scenarios.rs): witnesses above 8 MiB, chunk function-call gas above
    /// 1 Pgas and a zero-fee-instruction loop (W02 Gate-B caps).
    GateBCaps,
    /// `pipeline-race` (W12): a call on a global-contract account (which `Successor.Pipeline`
    /// cannot schedule, so it marks the chunk's preparation timing `uncertain`) in the chunk
    /// where a fresh account deploys code in one receipt and calls it in a later one.
    PipelineRace,
    /// `code-cache` (W08 / UQ-001, `code_cache_txs`): same-code deploys next to pre-state calls,
    /// with warm and poisoned-cache probes of every case (src/cachejudge.rs).
    CodeCache,
    /// `eval-loops` (src/scenarios.rs, W02/W16): the label-keeping loop shapes (push-then-pop,
    /// `br_if`/`br_table` back-edges, a shallow branch under deep nesting) at 300 Tgas.
    EvalLoops,
    /// `code-response` (src/scenarios.rs, W02): chunks whose accessed pre-state contract code is
    /// exactly at / one byte over the 64 MiB `ContractCodeResponse` cap.
    CodeResponse,
    /// `removal-soft` (src/scenarios.rs, W12 O4 ground truth): ContractData removals (VM
    /// `storage_remove`, `DeleteAccount`) that push the recorder's upper bound past the 4,000,000 B
    /// chunk soft limit while the witness's values stay below it.
    RemovalSoft,
}

/// The opt-in successor scenario (`NEAR_SUCCESSOR_SCENARIO`); unset = the baseline workload.
/// The genesis shard layout of a scenario: the base layout unchanged, except that
/// `yield-congestion-v2parent` rebuilds it as a V2 layout with an identity split map (so a parent map
/// in which every shard is its own parent), keeping boundaries and shard ids.
pub fn genesis_layout(base: near_primitives::shard_layout::ShardLayout)
    -> near_primitives::shard_layout::ShardLayout {
    use near_primitives::shard_layout::ShardLayout;
    if scenario() != Some(Scenario::YieldCongestionV2Parent) {
        return base;
    }
    let ids: Vec<_> = base.shard_ids().collect();
    let split = ids.iter().map(|&id| (id, vec![id])).collect();
    ShardLayout::v2(base.boundary_accounts().clone(), ids, Some(split))
}

pub fn scenario() -> Option<Scenario> {
    match std::env::var("NEAR_SUCCESSOR_SCENARIO") {
        Err(std::env::VarError::NotPresent) => None,
        Ok(value) if value == "global-cache" => Some(Scenario::GlobalCache),
        Ok(value) if value == "curve-hosts" => Some(Scenario::CurveHosts),
        Ok(value) if value == crate::keys::SCENARIO => Some(Scenario::Keys),
        Ok(value) if value == crate::keys::SCENARIO_MLDSA => Some(Scenario::Mldsa),
        Ok(value) if value == "yield" => Some(Scenario::Yield),
        Ok(value) if value == "storage-limits" => Some(Scenario::StorageLimits),
        Ok(value) if value == "fuel-stress" => Some(Scenario::FuelStress),
        Ok(value) if value == "eval-time" => Some(Scenario::EvalTime),
        Ok(value) if value == "yield-congestion" => Some(Scenario::YieldCongestion),
        Ok(value) if value == "yield-congestion-v2parent" => Some(Scenario::YieldCongestionV2Parent),
        Ok(value) if value == "curve-callbacks" => Some(Scenario::CurveCallbacks),
        Ok(value) if value == "genesis-tx" => Some(Scenario::GenesisTx),
        Ok(value) if value == "gaskey-target" => Some(Scenario::GasKeyTarget),
        Ok(value) if value == "rollback-refund" => Some(Scenario::RollbackRefund),
        Ok(value) if value == "gate-b-caps" => Some(Scenario::GateBCaps),
        Ok(value) if value == "eval-loops" => Some(Scenario::EvalLoops),
        Ok(value) if value == "code-response" => Some(Scenario::CodeResponse),
        Ok(value) if value == "removal-soft" => Some(Scenario::RemovalSoft),
        Ok(value) if value == "runtime-errors" => Some(Scenario::RuntimeErrors),
        Ok(value) if value == "pipeline-race" => Some(Scenario::PipelineRace),
        Ok(value) if value == "code-cache" => Some(Scenario::CodeCache),
        other => panic!("unsupported NEAR_SUCCESSOR_SCENARIO: {other:?}"),
    }
}

/// `code-cache` (W08 / UQ-001): every shard `k` has a pre-state contract `s{k}ccpre` (TINY at
/// genesis) and two code-less accounts `s{k}ccdep`, `s{k}ccrb`. Each round, per shard, a
/// deterministic pattern of `height` and `k` (no RNG draw, so the baseline stream is unchanged)
/// selects and orders up to five transactions that put a same-code deploy and a pre-state call in
/// one chunk:
///   D  `s{k}ccdep` deploys TINY (local receipt, committed);
///   R  `s{k}ccrb` deploys TINY then calls a missing method (local receipt, rolled back);
///   S  `s{k}ccpre` redeploys TINY then calls it (deploy in the call's own receipt);
///   C  `s{k}ccpre` calls itself (local receipt, pre-state code);
///   X  `s{k}ccdep` calls `s{k}ccpre` (an incoming receipt one chunk later, after that chunk's
///      local receipts).
/// The code mutants of these chunks (`--code-mutant-p`) drop TINY's blob, so a pre-state call is
/// served by an earlier deploy, by nothing, or races its preparation.
fn code_cache_txs(
    w: &mut crate::d2gen::World,
    s: &crate::chaingen::Setup,
    bh: &CryptoHash,
    height: u64,
) -> Vec<(String, SignedTransaction)> {
    use near_primitives::action::DeployContractAction;
    let code = crate::d3contracts::TINY.to_vec();
    let fc = |method: &str| {
        Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: method.into(),
            args: vec![(height % 251) as u8],
            gas: Gas::from_teragas(20),
            deposit: Balance::ZERO,
        }))
    };
    let deploy = || Action::DeployContract(DeployContractAction { code: code.clone() });
    let mut out = Vec::new();
    for k in 0..s.accounts.len() {
        let x = (height.wrapping_mul(2_654_435_761) ^ (k as u64).wrapping_mul(40_503)) >> 3;
        let pattern = (x % 32) as u32;
        if pattern == 0 {
            continue;
        }
        let (pre, dep, rb) = (
            baseline::acct(&format!("s{k}ccpre")),
            baseline::acct(&format!("s{k}ccdep")),
            baseline::acct(&format!("s{k}ccrb")),
        );
        let steps: [(&str, &near_primitives::types::AccountId, &near_primitives::types::AccountId, Vec<Action>); 5] = [
            ("D.deploy-committed", &dep, &dep, vec![deploy()]),
            ("R.deploy-rollback", &rb, &rb, vec![deploy(), fc("absent_method")]),
            ("S.same-receipt-deploy-call", &pre, &pre, vec![deploy(), fc("run")]),
            ("C.prestate-call", &pre, &pre, vec![fc("run")]),
            ("X.incoming-prestate-call", &dep, &pre, vec![fc("run")]),
        ];
        let start = ((x >> 5) % 5) as usize;
        for i in 0..5 {
            let j = (start + i) % 5;
            if pattern & (1 << j) == 0 {
                continue;
            }
            let (label, signer, receiver, actions) = &steps[j];
            if let Some(tx) = w.plain_tx(s, bh, signer, receiver, actions.clone()) {
                out.push((format!("successor.code-cache.{label}"), tx));
            }
        }
    }
    out
}

fn global_step(
    step: usize,
) -> Option<(
    String,
    near_primitives::types::AccountId,
    near_primitives::types::AccountId,
    Vec<Action>,
)> {
    use near_primitives::action::{
        CreateAccountAction, DeployContractAction, DeployGlobalContractAction,
        DeterministicStateInitAction, GlobalContractDeployMode, GlobalContractIdentifier,
        UseGlobalContractAction,
    };
    use near_primitives_core::deterministic_account_id::{
        DeterministicAccountStateInit, DeterministicAccountStateInitV1,
    };
    use std::collections::BTreeMap;
    let owner = baseline::acct("s0global");
    let hash_user = baseline::acct("s1globalhash");
    let account_user = baseline::acct("s2globalacct");
    let left = baseline::acct("s0cacheleft");
    let right = baseline::acct("s0cacheright");
    let code = crate::d3contracts::TINY.to_vec();
    let hash_id = GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(&code));
    let account_id = GlobalContractIdentifier::AccountId(owner.clone());
    let absent_id =
        GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(b"absent global code"));
    let fc = |method: &str| {
        Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: method.into(),
            args: vec![step as u8],
            gas: Gas::from_teragas(20),
            deposit: Balance::ZERO,
        }))
    };
    let use_code = |id| {
        Action::UseGlobalContract(Box::new(UseGlobalContractAction {
            contract_identifier: id,
        }))
    };
    let deploy = |mode| {
        Action::DeployGlobalContract(DeployGlobalContractAction {
            code: code.clone().into(),
            deploy_mode: mode,
        })
    };
    let init = |id, deposit| {
        let state_init = DeterministicAccountStateInit::V1(DeterministicAccountStateInitV1 {
            code: id,
            data: BTreeMap::from([(
                b"owner".to_vec(),
                if step == 16 {
                    vec![7; 2048]
                } else {
                    b"third-party".to_vec()
                },
            )]),
        });
        let receiver = near_primitives::utils::derive_near_deterministic_account_id(&state_init);
        (
            receiver,
            Action::DeterministicStateInit(Box::new(DeterministicStateInitAction {
                state_init,
                deposit,
            })),
        )
    };
    let (label, signer, receiver, actions) = match step {
        0 => (
            "deploy-hash",
            owner.clone(),
            owner.clone(),
            vec![deploy(GlobalContractDeployMode::CodeHash)],
        ),
        1 => (
            "deploy-account",
            owner.clone(),
            owner.clone(),
            vec![deploy(GlobalContractDeployMode::AccountId)],
        ),
        2 => (
            "use-hash-call",
            hash_user.clone(),
            hash_user,
            vec![use_code(hash_id), fc("run")],
        ),
        3 => (
            "use-account-call",
            account_user.clone(),
            account_user,
            vec![use_code(account_id), fc("run")],
        ),
        4 => (
            "missing-global-action-failure",
            hash_user.clone(),
            hash_user,
            vec![use_code(absent_id), fc("run")],
        ),
        5 => (
            "use-rollback",
            hash_user.clone(),
            hash_user,
            vec![use_code(account_id), fc("absent_method")],
        ),
        6 | 7 | 8 | 16 => {
            let missing = step == 7;
            let deposit = if step == 16 {
                Balance::ZERO
            } else {
                Balance::from_near(1)
            };
            let (receiver, action) = init(if missing { absent_id } else { hash_id }, deposit);
            let label = match step {
                6 => "state-init-third-party",
                7 => "state-init-missing-code",
                8 => "state-init-existing-refund",
                _ => "state-init-zero-deposit",
            };
            let call = Action::FunctionCall(Box::new(FunctionCallAction {
                method_name: "run".into(),
                args: vec![step as u8],
                gas: Gas::from_teragas(20),
                deposit: Balance::from_near(1),
            }));
            (label, owner.clone(), receiver, vec![action, call])
        }
        9 => (
            "redeploy-account-nonce",
            owner.clone(),
            owner.clone(),
            vec![deploy(GlobalContractDeployMode::AccountId)],
        ),
        10 => (
            "local-deploy-call",
            left.clone(),
            left,
            vec![
                Action::DeployContract(DeployContractAction { code }),
                fc("run"),
            ],
        ),
        11 => (
            "local-deploy-rollback",
            left.clone(),
            left,
            vec![
                Action::DeployContract(DeployContractAction {
                    code: crate::d3contracts::RICH.to_vec(),
                }),
                fc("absent_method"),
            ],
        ),
        12 => ("call-after-rollback", left.clone(), left, vec![fc("run")]),
        13 => (
            "cross-account-deploy-rollback",
            right.clone(),
            right,
            vec![
                Action::DeployContract(DeployContractAction { code }),
                Action::CreateAccount(CreateAccountAction {}),
            ],
        ),
        14 => (
            "cross-account-prestate-call",
            left.clone(),
            left,
            vec![fc("run")],
        ),
        15 => (
            "account-global-post-distribution-call",
            owner.clone(),
            account_user,
            vec![fc("run")],
        ),
        _ => return None,
    };
    Some((
        format!("successor.global-cache.{step:02}.{label}"),
        signer,
        receiver,
        actions,
    ))
}

// ---------------------------------------------------------------------------------------------
// pipeline-race (W12)
// ---------------------------------------------------------------------------------------------

pub const RACE_OWNER: &str = "s1raceowner";
pub const RACE_GLOBAL_USER: &str = "s1raceglobal";
pub const RACE_ROUNDS: usize = 16;

pub fn race_target(k: usize) -> String {
    format!("s1racey{k:02}")
}

/// The code round `k` deploys: a distinct module per round, so no round's code is in another
/// chunk's witness, and never the global contract's code (which the global call reads).
pub fn race_codes() -> &'static Vec<Vec<u8>> {
    static CODES: std::sync::OnceLock<Vec<Vec<u8>>> = std::sync::OnceLock::new();
    CODES.get_or_init(|| {
        (0..RACE_ROUNDS)
            .map(|k| {
                wat::parse_str(format!(
                    r#"(module (memory 1) (data (i32.const 0) "race{k:02}") (func (export "run")))"#
                ))
                .expect("race wat")
            })
            .collect()
    })
}

/// One batch of the `pipeline-race` scenario: returns (next step, blocks to wait, transactions).
/// Step 0 deploys the global contract by hash, step 1 has `RACE_GLOBAL_USER` use it, and each
/// later step `2 + k` submits, at one height and on shard 1: two calls of the global-contract
/// account, then a deploy of `race_codes()[k]` to the fresh account `race_target(k)` and a call
/// of it in a second transaction (a later receipt of the same chunk when both are included).
fn race_round(
    step: usize,
    w: &mut crate::d2gen::World,
    s: &crate::chaingen::Setup,
    bh: &CryptoHash,
) -> (usize, u64, Vec<(String, SignedTransaction)>) {
    use near_primitives::action::{
        DeployContractAction, DeployGlobalContractAction, GlobalContractDeployMode,
        GlobalContractIdentifier, UseGlobalContractAction,
    };
    let owner = baseline::acct(RACE_OWNER);
    let user = baseline::acct(RACE_GLOBAL_USER);
    let tiny = crate::d3contracts::TINY.to_vec();
    let fc = |method: &str, arg: u8| {
        Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: method.into(),
            args: vec![arg],
            gas: Gas::from_teragas(20),
            deposit: Balance::ZERO,
        }))
    };
    let mut out = vec![];
    match step {
        0 => {
            let a = Action::DeployGlobalContract(DeployGlobalContractAction {
                code: tiny.clone().into(),
                deploy_mode: GlobalContractDeployMode::CodeHash,
            });
            if let Some(tx) = w.plain_tx(s, bh, &owner, &owner, vec![a]) {
                out.push(("successor.pipeline-race.00.deploy-global".into(), tx));
            }
            (1, 6, out)
        }
        1 => {
            let a = Action::UseGlobalContract(Box::new(UseGlobalContractAction {
                contract_identifier: GlobalContractIdentifier::CodeHash(CryptoHash::hash_bytes(&tiny)),
            }));
            if let Some(tx) = w.plain_tx(s, bh, &user, &user, vec![a]) {
                out.push(("successor.pipeline-race.01.use-global".into(), tx));
            }
            (2, 6, out)
        }
        n if n < 2 + RACE_ROUNDS => {
            let k = n - 2;
            let y = baseline::acct(&race_target(k));
            for j in 0..2 {
                if let Some(tx) = w.plain_tx(s, bh, &user, &user, vec![fc("run", (2 * k + j) as u8)]) {
                    out.push((format!("successor.pipeline-race.{n:02}.global-call-{j}"), tx));
                }
            }
            let deploy = Action::DeployContract(DeployContractAction { code: race_codes()[k].clone() });
            if let Some(tx) = w.plain_tx(s, bh, &y, &y, vec![deploy]) {
                out.push((format!("successor.pipeline-race.{n:02}.deploy"), tx));
            }
            if let Some(tx) = w.plain_tx(s, bh, &y, &y, vec![fc("run", k as u8)]) {
                out.push((format!("successor.pipeline-race.{n:02}.call"), tx));
            }
            (n + 1, 5, out)
        }
        _ => (step, 1000, out),
    }
}
