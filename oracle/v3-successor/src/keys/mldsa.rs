//! The `mldsa` step table (`NEAR_SUCCESSOR_SCENARIO=mldsa`, labels `successor.mldsa.NN.name`).
//!
//! Accounts (genesis in `keys::genesis_records`): `s2kmldsa` (ML-DSA-65 key `main`), `s1kdeleg`
//! (ML-DSA delegate sender key `main`), `s1krelay` (relayer; also an ML-DSA key `main`),
//! `s2kmlpoor` (1 NEAR, ML-DSA key `main`; balance boundary) and `s2kmlpk` (the `kmlpk` contract,
//! whose `pk` method returns `signer_account_pk`). Gas costs for the boundary steps come from
//! nearcore's own `node_runtime::config::tx_cost` at PV86 with the tip's gas price; the ML-DSA
//! verification share is the cost difference against the same transaction with an ED25519 key.
//! Labels name what was submitted; outcomes are nearcore's (`keys-outcomes-NN.json`).
use super::*;
use crate::d2gen::view_account;
use near_crypto::MlDsa65Signature;

pub const N_STEPS_MLDSA: usize = 47;
/// Extra steps when `NEAR_MLDSA_BOUND_SIGNER` names the boundary signer (`tools/d3/mldsa65_bound.py`):
/// signatures whose `z` is exactly at, or one below, the norm bound `γ1 − β` (workplan item 10).
pub const N_STEPS_MLDSA_BOUND: usize = 6;

pub fn bound_signer() -> Option<String> {
    std::env::var("NEAR_MLDSA_BOUND_SIGNER").ok().filter(|v| !v.is_empty())
}

/// A signature of `msg` by the key of seed `seed` from the boundary signer, `mode` = at+ | at- | in+ | in-.
/// The signer's RNG is seeded with the message, so a step's signature is reproducible from its bytes.
fn bound_sig(seed: &str, msg: &[u8], mode: &str) -> Signature {
    let script = bound_signer().expect("NEAR_MLDSA_BOUND_SIGNER");
    let out = std::process::Command::new("python3")
        .args([script.as_str(), "sign", seed, &hex::encode(msg), mode, &format!("{mode}-{}", hex::encode(msg))])
        .output()
        .expect("boundary signer");
    assert!(out.status.success(), "boundary signer failed: {}", String::from_utf8_lossy(&out.stderr));
    eprintln!("mldsa bound signer {mode}: {}", String::from_utf8_lossy(&out.stderr).trim());
    ml_sig(hex::decode(String::from_utf8(out.stdout).unwrap().trim()).unwrap())
}

fn ml_bytes(sig: &Signature) -> Vec<u8> {
    match sig {
        Signature::MLDSA65(s) => s.0.to_vec(),
        _ => panic!("not an ML-DSA-65 signature"),
    }
}
fn ml_sig(b: Vec<u8>) -> Signature {
    Signature::MLDSA65(MlDsa65Signature(Box::new(b.try_into().unwrap())))
}

/// Byte edits of a valid ML-DSA-65 signature.
#[derive(Clone, Copy, Debug)]
enum MlEdit {
    /// one bit of `z` (a valid encoding, the challenge no longer matches)
    ZFlip,
    /// one bit of `c̃`
    CtFlip,
    /// two hint indices of one polynomial swapped: the same hint set, rejected by the ordering rule
    HintUnordered,
    /// an unused hint slot set non-zero: the same hint set, rejected by the padding rule
    HintPadding,
    /// the last running hint count set to ω + 1
    HintOverOmega,
    /// the first running count raised above the second
    HintDecreasing,
    /// all 3,309 bytes zero
    Zero,
}

fn edit_ml(sig: &Signature, e: MlEdit) -> Signature {
    let mut b = ml_bytes(sig);
    let muts = crate::mldsa_vectors::hint_mutations(&b);
    let pick = |name: &str| muts.iter().find(|(n, _)| *n == name).map(|(_, p)| p.clone());
    let patch: Vec<(usize, u8)> = match e {
        MlEdit::ZFlip => vec![(48 + 1000, b[48 + 1000] ^ 4)],
        MlEdit::CtFlip => vec![(0, b[0] ^ 1)],
        MlEdit::HintUnordered => pick("hint-unordered").or_else(|| pick("hint-padding-nonzero")).unwrap_or_default(),
        MlEdit::HintPadding => pick("hint-padding-nonzero").or_else(|| pick("hint-unordered")).unwrap_or_default(),
        MlEdit::HintOverOmega => pick("hint-count-over-omega").unwrap_or_default(),
        MlEdit::HintDecreasing => pick("hint-count-decreasing").or_else(|| pick("hint-count-255")).unwrap_or_default(),
        MlEdit::Zero => (0..b.len()).map(|i| (i, 0u8)).collect(),
    };
    for (o, v) in patch {
        b[o] = v;
    }
    ml_sig(b)
}

fn config86() -> std::sync::Arc<near_parameters::RuntimeConfig> {
    near_parameters::RuntimeConfigStore::new(None).get_config(86).clone()
}

/// `(gas_cost, verification share)` of `tx` in yoctoNEAR at the tip's gas price, by nearcore.
fn gas_cost(s: &Setup, bh: &CryptoHash, tx: &Transaction) -> Option<(u128, u128)> {
    let price = s.env.clients[0].chain.get_block_header(bh).ok()?.next_gas_price();
    let cfg = config86();
    let c = node_runtime::config::tx_cost(&cfg, tx, price).ok()?;
    let mut ed_tx = tx.clone();
    let edpk = InMemorySigner::test_signer(tx.signer_id()).public_key();
    match &mut ed_tx {
        Transaction::V0(t) => t.public_key = edpk,
        Transaction::V1(t) => t.public_key = edpk,
    }
    let c_ed = node_runtime::config::tx_cost(&cfg, &ed_tx, price).ok()?;
    Some((c.gas_cost.as_yoctonear(), c.gas_cost.as_yoctonear() - c_ed.gas_cost.as_yoctonear()))
}

impl KeysWorld {
    pub(super) fn step_mldsa(&mut self, i: usize, s: &Setup, bh: &CryptoHash) -> Option<(&'static str, Mode, usize, Vec<SignedTransaction>)> {
        use Mode::*;
        let bh = *bh;
        let (ma, da, ra, pa, ca) = (a_mldsa(), a_deleg(), a_relay(), a_poor(), a_mlpk());
        let ml1 = sk(&ma, "main", KeyType::MLDSA65);
        let ml2 = sk(&ma, "second", KeyType::MLDSA65);
        let ml3 = sk(&ma, "fc", KeyType::MLDSA65);
        let ml4 = sk(&ma, "fourth", KeyType::MLDSA65);
        let mlo = sk(&ma, "other", KeyType::MLDSA65);
        let mlg = sk(&ma, "gas", KeyType::MLDSA65);
        let secp = sk(&ma, "secp", KeyType::SECP256K1);
        let mp = sk(&pa, "main", KeyType::MLDSA65);
        let sd = sk(&da, "main", KeyType::MLDSA65);
        let sd2 = sk(&da, "second", KeyType::MLDSA65);
        let sdo = sk(&da, "other", KeyType::MLDSA65);
        let rm = sk(&ra, "main", KeyType::MLDSA65);
        let sink2 = acct("s2a00");
        let sink1 = acct("s1a00");
        let signed_with = |tx: &Transaction, k: &Signer| -> Signature { k.sign(tx.get_hash_and_size().0.as_ref()) };
        let ml_tx = |k: &Signer, n: u64, d: u128| v0_unsigned(k.public_key(), &ma, &sink2, n, vec![tr(d)], bh);
        // the planned gas-key transaction (nonce index 0); its gas cost does not depend on the nonce
        let gk_tx = |n: u64| v1_unsigned(mlg.public_key(), &ma, &sink2, TransactionNonce::from_nonce_and_index(n, 0), NonceMode::Monotonic, vec![tr(1)], bh);
        let nep = |d: &DelegateAction, k: &Signer| k.sign(d.get_nep461_hash().as_bytes());
        let delegate_action = |nonce: u64, inner: Vec<Action>, receiver: &AccountId, pk: PublicKey| DelegateAction {
            sender_id: da.clone(),
            receiver_id: receiver.clone(),
            actions: inner.into_iter().map(|a| NonDelegateAction::try_from(a).unwrap()).collect(),
            nonce,
            max_block_height: 10_000_000,
            public_key: pk,
        };
        let deleg = |this: &mut Self, nonce: u64, inner: Vec<Action>, pk: PublicKey, sig: &dyn Fn(&DelegateAction) -> Signature| -> Option<SignedTransaction> {
            let d = delegate_action(nonce, inner, &sink1, pk);
            let signature = sig(&d);
            this.ed_tx(s, &bh, &ra, &da, vec![Action::Delegate(Box::new(SignedDelegateAction { delegate_action: d, signature }))])
        };
        // an invalid signature does not consume the nonce
        let unuse = |this: &mut Self, a: &AccountId, k: &Signer, n: u64| {
            this.used.insert((a.clone(), k.public_key(), None), n - 1);
        };
        let x: (&'static str, Mode, usize, Vec<SignedTransaction>) = match i {
            // ---- ML-DSA-65 transaction signatures (s2kmldsa, shard index 2)
            0 => {
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                ("mldsa-tx-transfer", Pool, 2, vec![sign(ml_tx(&ml1, n, NEAR), &ml1)])
            }
            1..=7 => {
                let e = [MlEdit::ZFlip, MlEdit::CtFlip, MlEdit::HintUnordered, MlEdit::HintPadding, MlEdit::HintOverOmega, MlEdit::HintDecreasing, MlEdit::Zero][i - 1];
                let name = ["mldsa-tx-bad-z", "mldsa-tx-bad-ctilde", "mldsa-tx-hint-unordered", "mldsa-tx-hint-padding",
                    "mldsa-tx-hint-count-over-omega", "mldsa-tx-hint-count-decreasing", "mldsa-tx-zero-sig"][i - 1];
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                unuse(self, &ma, &ml1, n);
                let tx = ml_tx(&ml1, n, i as u128);
                let sig = edit_ml(&signed_with(&tx, &ml1), e);
                (name, Inject, 2, vec![with_sig(tx, sig)])
            }
            8 | 9 | 10 => {
                // ML-DSA key; signature by another ML-DSA key / the ED25519 test key / a secp key
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                unuse(self, &ma, &ml1, n);
                let tx = ml_tx(&ml1, n, i as u128);
                let sig = match i {
                    8 => signed_with(&tx, &mlo),
                    9 => signed_with(&tx, &ed(&ma)),
                    _ => signed_with(&tx, &secp),
                };
                (["mldsa-tx-wrong-key", "mldsa-key-ed25519-sig", "mldsa-key-secp-sig"][i - 8], Inject, 2, vec![with_sig(tx, sig)])
            }
            11 => {
                // ED25519 key, ML-DSA signature
                let k = ed(&ma);
                let n = self.cur(s, &bh, &ma, &k.public_key(), None)? + 1;
                let tx = v0_unsigned(k.public_key(), &ma, &sink2, n, vec![tr(11)], bh);
                let sig = signed_with(&tx, &ml1);
                ("ed25519-key-mldsa-sig", Inject, 2, vec![with_sig(tx, sig)])
            }
            12 => {
                let cur = self.cur(s, &bh, &ma, &ml1.public_key(), None)?;
                ("mldsa-tx-stale-nonce", Inject, 2, vec![sign(ml_tx(&ml1, cur, 12), &ml1)])
            }
            13 => {
                // nonce ≥ height · 10^6: `InvalidNonce` (nonce too large)
                let h = s.env.clients[0].chain.get_block_header(&bh).ok()?.height();
                ("mldsa-tx-nonce-too-large", Inject, 2, vec![sign(ml_tx(&ml1, (h + 3) * 1_000_000, 13), &ml1)])
            }
            // ---- ML-DSA keys added, then used
            14 => {
                let fcp = FunctionCallPermission { allowance: Some(Balance::from_near(1)), receiver_id: ca.to_string(), method_names: vec![] };
                let t = self.ed_tx(s, &bh, &ma, &ma, vec![
                    add_key(ml2.public_key(), AccessKeyPermission::FullAccess),
                    add_key(ml3.public_key(), AccessKeyPermission::FunctionCall(fcp)),
                ])?;
                ("mldsa-add-keys", Pool, 2, vec![t])
            }
            15 => {
                let n = self.next(s, &bh, &ma, &ml2.public_key(), None)?;
                let tx = v0_unsigned(ml2.public_key(), &ma, &sink2, n, vec![tr(15), tr(16)], bh);
                ("mldsa-new-key-multi-action", Pool, 2, vec![sign(tx, &ml2)])
            }
            16 => {
                let n = self.next(s, &bh, &ma, &ml3.public_key(), None)?;
                let tx = v0_unsigned(ml3.public_key(), &ma, &ca, n, vec![fc("pk", vec![], 5)], bh);
                ("mldsa-fc-key-call-signer-pk", Pool, 2, vec![sign(tx, &ml3)])
            }
            17 => {
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                let tx = v0_unsigned(ml1.public_key(), &ma, &ma, n, vec![add_key(ml4.public_key(), AccessKeyPermission::FullAccess)], bh);
                ("mldsa-signed-add-mldsa-key", Pool, 2, vec![sign(tx, &ml1)])
            }
            18 => {
                let n = self.next(s, &bh, &ma, &ml4.public_key(), None)?;
                ("mldsa-added-key-tx", Pool, 2, vec![sign(ml_tx(&ml4, n, 18), &ml4)])
            }
            19 => {
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                let tx = v0_unsigned(ml1.public_key(), &ma, &ma, n, vec![del_key(ml2.public_key())], bh);
                ("mldsa-signed-delete-key", Pool, 2, vec![sign(tx, &ml1)])
            }
            20 => {
                let n = self.used.get(&(ma.clone(), ml2.public_key(), None)).copied().unwrap_or(0) + 1;
                ("mldsa-deleted-key-tx", Inject, 2, vec![sign(ml_tx(&ml2, n, 20), &ml2)])
            }
            21 | 22 => {
                let cur = self.cur(s, &bh, &ma, &ml1.public_key(), None)?.max(self.used.get(&(ma.clone(), ml1.public_key(), None)).copied().unwrap_or(0));
                let n = if i == 21 { cur + 1 } else { cur + 2 };
                if i == 21 {
                    self.used.insert((ma.clone(), ml1.public_key(), None), n);
                }
                let tx = v1_unsigned(ml1.public_key(), &ma, &sink2, TransactionNonce::from_nonce(n), NonceMode::Strict, vec![tr(i as u128)], bh);
                (if i == 21 { "mldsa-v1-strict-nonce" } else { "mldsa-v1-strict-nonce-gap" }, if i == 21 { Pool } else { Inject }, 2, vec![sign(tx, &ml1)])
            }
            23 => {
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                let tx = v0_unsigned(ml1.public_key(), &ma, &ca, n, vec![fc("pk", vec![], 5)], bh);
                ("mldsa-full-key-call-signer-pk", Pool, 2, vec![sign(tx, &ml1)])
            }
            // ---- an ML-DSA gas key at the gas-key-balance boundary
            24 => {
                let (gc, vc) = gas_cost(s, &bh, &gk_tx(1))?;
                let a = Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: mlg.public_key(), deposit: Balance::from_yoctonear(gc.saturating_sub(vc)) }));
                ("mldsa-gas-key-add-fund-short-by-verify", Pool, 2, vec![self.ed_tx(s, &bh, &ma, &ma, vec![add_key(mlg.public_key(), gas_full(2)), a])?])
            }
            25 | 27 | 29 => {
                let n = self.cur(s, &bh, &ma, &mlg.public_key(), Some(0))? + 1;
                let name = match i {
                    25 => "mldsa-gas-key-tx-short-by-verify",
                    27 => "mldsa-gas-key-tx-short-by-one",
                    _ => "mldsa-gas-key-tx-exact",
                };
                (name, Inject, 2, vec![sign(gk_tx(n), &mlg)])
            }
            26 | 28 => {
                let (_, vc) = gas_cost(s, &bh, &gk_tx(1))?;
                // with a zero gas price every cost is 0 and the boundary steps degenerate (no underflow)
                let d = if i == 26 { vc.saturating_sub(1) } else { 1 };
                let a = Action::TransferToGasKey(Box::new(TransferToGasKeyAction { public_key: mlg.public_key(), deposit: Balance::from_yoctonear(d) }));
                (if i == 26 { "mldsa-gas-key-topup-verify-minus-one" } else { "mldsa-gas-key-topup-one" }, Pool, 2, vec![self.ed_tx(s, &bh, &ma, &ma, vec![a])?])
            }
            30 => {
                let n = self.cur(s, &bh, &ma, &mlg.public_key(), Some(1))? + 1;
                let tx = v1_unsigned(mlg.public_key(), &ma, &sink2, TransactionNonce::from_nonce_and_index(n, 1), NonceMode::Monotonic, vec![tr(30)], bh);
                let sig = edit_ml(&signed_with(&tx, &mlg), MlEdit::ZFlip);
                ("mldsa-gas-key-bad-sig", Inject, 2, vec![with_sig(tx, sig)])
            }
            // ---- account balance boundary at the verification cost (s2kmlpoor)
            31 | 32 | 33 => {
                let n = self.cur(s, &bh, &pa, &mp.public_key(), None)? + 1;
                let amount = view_account(s, &bh, &pa)?.amount().as_yoctonear();
                let probe = v0_unsigned(mp.public_key(), &pa, &sink2, n, vec![tr(0)], bh);
                let (gc, vc) = gas_cost(s, &bh, &probe)?;
                let (name, d) = match i {
                    31 => ("mldsa-balance-short-by-verify", (amount + vc).saturating_sub(gc)),
                    32 => ("mldsa-balance-short-by-one", (amount + 1).saturating_sub(gc)),
                    _ => ("mldsa-balance-exact", amount.saturating_sub(gc)),
                };
                let tx = v0_unsigned(mp.public_key(), &pa, &sink2, n, vec![tr(d)], bh);
                (name, Inject, 2, vec![sign(tx, &mp)])
            }
            // ---- delegates with an ML-DSA-65 inner signer (s1kdeleg, relayer s1krelay)
            34 => {
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                ("deleg-mldsa-valid", Pool, 1, vec![deleg(self, n, vec![tr(NEAR)], sd.public_key(), &|d| nep(d, &sd))?])
            }
            35..=37 => {
                let e = [MlEdit::ZFlip, MlEdit::HintUnordered, MlEdit::HintPadding][i - 35];
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                unuse(self, &da, &sd, n);
                let name = ["deleg-mldsa-bad-z", "deleg-mldsa-hint-unordered", "deleg-mldsa-hint-padding"][i - 35];
                (name, Pool, 1, vec![deleg(self, n, vec![tr(i as u128)], sd.public_key(), &|d| edit_ml(&nep(d, &sd), e))?])
            }
            38 => {
                let cur = self.cur(s, &bh, &da, &sd.public_key(), None)?;
                ("deleg-mldsa-stale-nonce", Pool, 1, vec![deleg(self, cur, vec![tr(38)], sd.public_key(), &|d| nep(d, &sd))?])
            }
            39 | 40 | 41 => {
                let edk = ed(&da);
                let (pk, signer): (PublicKey, &Signer) = match i {
                    39 => (sd.public_key(), &edk),
                    40 => (edk.public_key(), &sd),
                    _ => (sd.public_key(), &sdo),
                };
                let n = self.cur(s, &bh, &da, &pk, None)? + 1;
                let name = ["deleg-mldsa-key-ed25519-sig", "deleg-ed25519-key-mldsa-sig", "deleg-mldsa-wrong-key"][i - 39];
                (name, Pool, 1, vec![deleg(self, n, vec![tr(i as u128)], pk, &|d| nep(d, signer))?])
            }
            42 => {
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                let payload = VersionedDelegateActionPayload::V2(DelegateActionV2 {
                    sender_id: da.clone(),
                    receiver_id: sink1.clone(),
                    actions: vec![NonDelegateAction::try_from(tr(42)).unwrap()],
                    nonce: TransactionNonce::from_nonce(n),
                    max_block_height: 10_000_000,
                    public_key: sd.public_key(),
                });
                let a = Action::DelegateV2(Box::new(VersionedSignedDelegateAction::sign(&sd, payload)));
                ("deleg-v2-mldsa", Pool, 1, vec![self.ed_tx(s, &bh, &ra, &da, vec![a])?])
            }
            43 => {
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                let d = delegate_action(n, vec![add_key(sd2.public_key(), AccessKeyPermission::FullAccess), tr(43)], &da, sd.public_key());
                let signature = nep(&d, &sd);
                let t = self.ed_tx(s, &bh, &ra, &da, vec![Action::Delegate(Box::new(SignedDelegateAction { delegate_action: d, signature }))])?;
                ("deleg-mldsa-inner-add-mldsa-key", Pool, 1, vec![t])
            }
            44 => {
                let n = self.next(s, &bh, &da, &sd2.public_key(), None)?;
                ("deleg-mldsa-added-key", Pool, 1, vec![deleg(self, n, vec![tr(44)], sd2.public_key(), &|d| nep(d, &sd2))?])
            }
            45 => {
                // an ML-DSA relayer wrapping an ML-DSA delegate: two verification costs
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                let d = delegate_action(n, vec![tr(45)], &sink1, sd.public_key());
                let signature = nep(&d, &sd);
                let rn = self.next(s, &bh, &ra, &rm.public_key(), None)?;
                let tx = v0_unsigned(rm.public_key(), &ra, &da, rn, vec![Action::Delegate(Box::new(SignedDelegateAction { delegate_action: d, signature }))], bh);
                ("deleg-mldsa-relayer-mldsa", Pool, 1, vec![sign(tx, &rm)])
            }
            46 => {
                // a Stake action carrying an ML-DSA key: not a valid staking key
                let k = ed(&ma);
                let n = self.cur(s, &bh, &ma, &k.public_key(), None)? + 1;
                let a = Action::Stake(Box::new(near_primitives::action::StakeAction { stake: Balance::from_near(1), public_key: ml1.public_key() }));
                ("mldsa-stake-key", Inject, 2, vec![sign(v0_unsigned(k.public_key(), &ma, &ma, n, vec![a], bh), &k)])
            }
            // ---- `z` at the norm bound (NEAR_MLDSA_BOUND_SIGNER only)
            47..=50 => {
                let (mode, name, how) = [("at+", "mldsa-tx-z-at-bound", Inject), ("at-", "mldsa-tx-z-at-neg-bound", Inject),
                    ("in+", "mldsa-tx-z-bound-minus-one", Pool), ("in-", "mldsa-tx-z-neg-bound-minus-one", Pool)][i - 47];
                let n = self.next(s, &bh, &ma, &ml1.public_key(), None)?;
                if mode.starts_with("at") {
                    unuse(self, &ma, &ml1, n);
                }
                let tx = ml_tx(&ml1, n, i as u128);
                let sig = bound_sig(&format!("keys-main-{ma}"), tx.get_hash_and_size().0.as_ref(), mode);
                (name, how, 2, vec![with_sig(tx, sig)])
            }
            51 | 52 => {
                let (mode, name) = [("at+", "deleg-mldsa-z-at-bound"), ("in-", "deleg-mldsa-z-neg-bound-minus-one")][i - 51];
                let n = self.next(s, &bh, &da, &sd.public_key(), None)?;
                if mode.starts_with("at") {
                    unuse(self, &da, &sd, n);
                }
                let seed = format!("keys-main-{da}");
                (name, Pool, 1, vec![deleg(self, n, vec![tr(i as u128)], sd.public_key(), &|d| bound_sig(&seed, d.get_nep461_hash().as_bytes(), mode))?])
            }
            _ => return None,
        };
        Some(x)
    }
}
