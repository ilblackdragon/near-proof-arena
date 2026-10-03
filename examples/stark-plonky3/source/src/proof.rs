//! Proving, verification, proof framing and the public artifact.
//!
//! ```text
//! proof.bin  = bytes "np-stark-plonky3-proof-v1" ‖ postcard(BatchProof)
//! public.bin = bytes "np-stark-plonky3-public-v1" ‖ bytes statement_id
//!              ‖ hash sha256(params.bin) ‖ hash air_config_digest
//! ```
//!
//! `air_config_digest` = SHA-256 over a canonical description of the STARK
//! configuration (field, extension, hashes, FRI parameters, transcript
//! domain) and, per table in instance order, its name, widths, public-value
//! count, lookup budget, the preprocessed trace, and the `Debug` rendering of
//! every symbolic constraint and bus interaction. `prepare` writes it; `verify`
//! recomputes it from the AIRs compiled into the binary and rejects a
//! `public.bin` that names a different AIR.

use crate::air::fixed::{BYTE_LOG_HEIGHT, R12_LOG_HEIGHT};
use crate::air::{NpAir, all_airs};
use crate::config::*;
use crate::consts::*;
use crate::spec::*;
use crate::wire::{Reader, Writer};
use p3_air::BaseAir;
use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch, verify_batch};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use sha2::Digest;

pub const PROOF_FORMAT: &[u8] = b"np-stark-plonky3-proof-v1";
pub const PUBLIC_FORMAT: &[u8] = b"np-stark-plonky3-public-v1";
pub const MAX_PROOF_BYTES: usize = 8 * 1024 * 1024;

/// Allowed log2 trace heights per table (min, max), instance order.
pub const HEIGHT_BOUNDS: [(usize, usize); 9] = [
    (2, 18),                              // sha
    (2, 8),                               // rcpt (n <= 256)
    (2, 9),                               // mrk  (<= 263 rows)
    (2, 8),                               // sort
    (2, 8),                               // acct
    (2, 16),                              // node
    (2, 16),                              // path (<= 256 * 130 rows)
    (BYTE_LOG_HEIGHT, BYTE_LOG_HEIGHT),   // byte
    (R12_LOG_HEIGHT, R12_LOG_HEIGHT),     // r12
];

pub fn config_description() -> String {
    format!(
        "field=KoalaBear(2^31-2^24+1);ext=Binomial<8>;leaf=SerializingHasher<SHA-256>;\
         node=CompressionFunctionFromHasher<SHA-256,2,32>;challenger=SerializingChallenger32<HashChallenger<u8,SHA-256,32>>;\
         log_blowup={LOG_BLOWUP};num_queries={NUM_QUERIES};query_pow={QUERY_POW_BITS};commit_pow={COMMIT_POW_BITS};\
         batch_pow={BATCH_POW_BITS};max_log_arity={MAX_LOG_ARITY};log_final_poly_len={LOG_FINAL_POLY_LEN};\
         cap_height={CAP_HEIGHT};domain={};plonky3=3acc8b70e68d6c2afc03930700c26540bd47458d",
        String::from_utf8_lossy(TRANSCRIPT_DOMAIN)
    )
}

/// Deterministic digest of the configuration and of every AIR (see module
/// docs and `fingerprint.rs`).
pub fn air_config_digest() -> [u8; 32] {
    let mut h = sha2::Sha256::new();
    h.update(config_description().as_bytes());
    for air in all_airs() {
        let pre = BaseAir::<Val>::preprocessed_trace(&air);
        h.update(
            format!(
                "\ntable {} width={} pre={} pv={} budget={} next={}\n",
                air.name(),
                BaseAir::<Val>::width(&air),
                BaseAir::<Val>::preprocessed_width(&air),
                air.num_pv(),
                air.lookup_budget(),
                air.uses_next()
            )
            .as_bytes(),
        );
        if let Some(pre) = pre {
            for x in pre.values {
                h.update(x.as_canonical_u32().to_le_bytes());
            }
        }
        h.update(crate::fingerprint::fingerprint(&air));
    }
    h.finalize().into()
}

pub fn public_bin(params: &[u8], digest: &[u8; 32]) -> Vec<u8> {
    let mut w = Writer::with_capacity(160);
    w.bytes(PUBLIC_FORMAT).bytes(STATEMENT_ID).raw(&crate::sha256(params)).raw(digest);
    w.0
}

/// Strictly parse `public.bin`: (params digest, AIR/config digest).
pub fn parse_public(b: &[u8]) -> Result<([u8; 32], [u8; 32]), String> {
    let mut r = Reader::new(b);
    r.expect_tag(PUBLIC_FORMAT, "public format").map_err(|e| e.to_string())?;
    r.expect_tag(STATEMENT_ID, "statement id").map_err(|e| e.to_string())?;
    let p = r.hash("params digest").map_err(|e| e.to_string())?;
    let d = r.hash("air digest").map_err(|e| e.to_string())?;
    r.finish().map_err(|e| e.to_string())?;
    Ok((p, d))
}

/// Validate approved params (`near-arena-params-v1` for this statement).
pub fn params_valid(b: &[u8]) -> bool {
    let mut r = Reader::new(b);
    (|| -> Option<bool> {
        let ok = r.bytes("f").ok()? == PARAMS_FORMAT
            && r.bytes("s").ok()? == STATEMENT_ID
            && r.u32("pv").ok()? == PROTOCOL_VERSION
            && r.bytes("c").ok()? == CHAIN_ID;
        r.hash("digest").ok()?;
        Some(ok && r.is_empty())
    })()
    .unwrap_or(false)
}

pub struct ProveStats {
    pub heights: Vec<usize>,
    pub witness_ms: u128,
    pub trace_ms: u128,
    pub prove_ms: u128,
}

fn budgets(airs: &[NpAir]) -> Vec<usize> {
    airs.iter().map(|a| a.lookup_budget()).collect()
}

/// Honest prover. `selfcheck` re-evaluates every constraint and bus natively
/// before proving (slow; for tests).
pub fn prove(
    request: &[u8],
    witness: &[u8],
    selfcheck: bool,
) -> Result<(Vec<u8>, Vec<u8>, ProveStats), String> {
    let t0 = std::time::Instant::now();
    let wit = crate::witness::build(request, witness)?;
    let t1 = std::time::Instant::now();
    let airs = all_airs();
    let mut traces = crate::trace::all_traces(&airs, &wit);
    let pvs = crate::trace::pv_vals(&wit.pv);
    crate::trace::fill_multiplicities(&airs, &mut traces, &pvs);
    let heights: Vec<usize> = traces.iter().map(|t| t.height()).collect();
    for (i, h) in heights.iter().enumerate() {
        let lg = h.trailing_zeros() as usize;
        if lg < HEIGHT_BOUNDS[i].0 || lg > HEIGHT_BOUNDS[i].1 {
            return Err(format!("table {} height 2^{lg} outside supported bounds", airs[i].name()));
        }
    }
    if selfcheck {
        let rep = crate::eval::check_all(&airs, &traces, &pvs, 20);
        if !rep.ok() {
            return Err(format!(
                "selfcheck failed: constraints {:?} buses {:?}",
                rep.constraint_failures, rep.bus_problems
            ));
        }
    }
    let t2 = std::time::Instant::now();
    let config = make_config();
    let degrees: Vec<usize> = heights.iter().map(|h| h.trailing_zeros() as usize).collect();
    let pd = ProverData::from_airs_and_degrees_with_lookup_budgets(
        &config,
        &airs,
        &degrees,
        &budgets(&airs),
        LOG_BLOWUP,
    )
    .map_err(|e| format!("prover data: {e:?}"))?;
    let instances: Vec<StarkInstance<'_, MyConfig, NpAir>> = airs
        .iter()
        .zip(traces.iter())
        .map(|(a, t)| StarkInstance {
            air: a,
            trace: t,
            public_values: if a.num_pv() > 0 { pvs.clone() } else { vec![] },
        })
        .collect();
    let proof = prove_batch(&config, &instances, &pd).map_err(|e| format!("prove: {e:?}"))?;
    let t3 = std::time::Instant::now();
    let body = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    let mut w = Writer::with_capacity(body.len() + 64);
    w.bytes(PROOF_FORMAT).raw(&body);
    let stats = ProveStats {
        heights,
        witness_ms: (t1 - t0).as_millis(),
        trace_ms: (t2 - t1).as_millis(),
        prove_ms: (t3 - t2).as_millis(),
    };
    Ok((wit.claim_bytes, w.0, stats))
}

/// The verifier. `Ok(())` = accept; `Err(reason)` = reject.
pub fn verify(claim: &[u8], proof: &[u8]) -> Result<(), String> {
    // ---- claim: strict decode + static domain ----
    let c = Claim::decode(claim).map_err(|e| format!("claim: {e}"))?;
    if c.protocol_version != PROTOCOL_VERSION || c.chain_id != CHAIN_ID {
        return Err("claim: out of domain (protocol version / chain)".into());
    }
    let n = c.receipt_count as u64;
    if !(1..=MAX_BATCH as u64).contains(&n) {
        return Err("claim: batch size out of domain".into());
    }
    if (n as u128 - 1) * G as u128 >= c.gas_limit as u128 {
        return Err("claim: compute limit out of domain".into());
    }
    if c.gas_burnt_total as u128 != n as u128 * G as u128 {
        return Err("claim: gas_burnt_total != n*G".into());
    }
    if c.refund_count as u64 > n {
        return Err("claim: refund_count > n".into());
    }
    let pv: Vec<Val> = claim[claim.len() - NUM_PV..].iter().map(|&b| Val::from_u8(b)).collect();
    // ---- proof framing ----
    if proof.len() > MAX_PROOF_BYTES {
        return Err("proof too large".into());
    }
    let mut r = Reader::new(proof);
    r.expect_tag(PROOF_FORMAT, "proof format").map_err(|e| e.to_string())?;
    let body = &proof[r.pos..];
    let (p, rest): (BatchProof<MyConfig>, &[u8]) =
        postcard::take_from_bytes(body).map_err(|e| format!("proof decode: {e}"))?;
    if !rest.is_empty() {
        return Err("proof: trailing bytes".into());
    }
    let airs = all_airs();
    if p.degree_bits.len() != airs.len() {
        return Err("proof: instance count".into());
    }
    for (i, &db) in p.degree_bits.iter().enumerate() {
        if db < HEIGHT_BOUNDS[i].0 || db > HEIGHT_BOUNDS[i].1 {
            return Err(format!("proof: table {} height out of bounds", airs[i].name()));
        }
    }
    let config = make_config();
    let tv = std::time::Instant::now();
    let pd = ProverData::from_airs_and_degrees_with_lookup_budgets(
        &config,
        &airs,
        &p.degree_bits,
        &budgets(&airs),
        LOG_BLOWUP,
    )
    .map_err(|e| format!("common data: {e:?}"))?;
    let pvs: Vec<Vec<Val>> =
        airs.iter().map(|a| if a.num_pv() > 0 { pv.clone() } else { vec![] }).collect();
    if std::env::var("NP_TIMING").is_ok() {
        eprintln!("verify: common data {:?}", tv.elapsed());
    }
    let tv = std::time::Instant::now();
    let res = verify_batch(&config, &airs, &p, &pvs, &pd.common).map_err(|e| format!("stark: {e:?}"));
    if std::env::var("NP_TIMING").is_ok() {
        eprintln!("verify: verify_batch {:?}", tv.elapsed());
    }
    res
}
