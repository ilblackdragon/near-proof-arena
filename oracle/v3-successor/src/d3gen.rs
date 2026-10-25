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
}
impl D3World {
    pub fn new(n_shards: usize) -> Self {
        Self {
            inner: baseline::D3World::new(n_shards),
            next_step: 0,
            next_height: 10004,
        }
    }
    pub fn one(
        &mut self,
        w: &mut crate::d2gen::World,
        s: &crate::chaingen::Setup,
        bh: &CryptoHash,
        height: u64,
        rng: &mut StdRng,
    ) -> Option<(String, SignedTransaction)> {
        if scenario_enabled() && height >= self.next_height {
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
    if scenario_enabled() {
        for name in [
            "s0global",
            "s1globalhash",
            "s2globalacct",
            "s0cacheleft",
            "s0cacheright",
        ] {
            let account_id = baseline::acct(name);
            let amount = Balance::from_near(1_000_000);
            let code = crate::d3contracts::TINY;
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
    if crate::keys::enabled() {
        let (extra, amount) = crate::keys::genesis_records();
        records.extend(extra);
        supply = supply.checked_add(amount).unwrap();
    }
    (records, supply)
}

/// The global-cache scenario; `keys` (src/keys.rs) is the other accepted value.
fn scenario_enabled() -> bool {
    match std::env::var("NEAR_SUCCESSOR_SCENARIO") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) if value == "global-cache" => true,
        Ok(value) if value == crate::keys::SCENARIO => false,
        other => panic!("unsupported NEAR_SUCCESSOR_SCENARIO: {other:?}"),
    }
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
