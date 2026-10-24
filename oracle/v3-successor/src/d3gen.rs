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
}
impl D3World {
    pub fn new(n_shards: usize) -> Self {
        Self { inner: baseline::D3World::new(n_shards) }
    }
    pub fn one(&mut self, w: &mut crate::d2gen::World, s: &crate::chaingen::Setup,
               bh: &CryptoHash, height: u64, rng: &mut StdRng) -> Option<(String, SignedTransaction)> {
        if std::env::var_os("NEAR_SUCCESSOR_CONTRACT").is_some() && rng.gen_bool(0.5) {
            let shard = rng.gen_range(0..s.accounts.len());
            let signer = &s.accounts[shard][rng.gen_range(0..crate::d2gen::HONEST)];
            let receiver = baseline::acct("s0fl");
            let args = (0..32).map(|_| rng.r#gen()).collect();
            let action = Action::FunctionCall(Box::new(FunctionCallAction {
                method_name: "run".into(), args, gas: Gas::from_teragas(20),
                deposit: Balance::from_yoctonear(rng.gen_range(0..1000)),
            }));
            return w.plain_tx(s, bh, signer, &receiver, vec![action])
                .map(|tx| ("successor.target_call".into(), tx));
        }
        self.inner.one(w, s, bh, height, rng)
    }
}
