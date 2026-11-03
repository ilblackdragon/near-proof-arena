//! The D0a public statement recomputed from the claim and the transmitted hint, without a
//! witness (the `statepublic` example's logic, callable in-process by a verifier).
use p3_field::PrimeField32;

use crate::{airpub::AirPublic, v3, verifier};

/// Public statement of one chunk: the public inputs and the public messages (bus, send, record),
/// as canonical u32 field elements. These are exactly what `statepublic` writes to `pubs.bin` and
/// `pubmsgs.json`.
pub struct Statement {
    pub pubs: Vec<u32>,
    pub msgs: Vec<(usize, bool, Vec<u32>)>,
}

/// Recompute the public statement from the AIR's public view, the claim bytes and the encoded
/// hint. Any claim/hint the D0a preparation rejects, or whose public tape does not fit the AIR's
/// public segments, is an error.
pub fn public_statement(air: &AirPublic, claim: &[u8], hint: &[u8]) -> Result<Statement, String> {
    if air.num_tables != 25 {
        return Err(format!("AIR has {} tables, expected 25", air.num_tables));
    }
    let hint = v3::prep::Hint::decode(hint).map_err(|e| format!("hint decode: {e}"))?;
    let prep = v3::d0::prep(claim, &hint).map_err(|e| format!("claim/hint preparation: {e}"))?;
    let tape = v3::public::prepared_bytes(&prep, 0);
    // `verifier::{pub_fit, public_inputs, pub_msgs}` read only numPub / pubSegs / maxPub.
    let air = &air.air;
    if !verifier::pub_fit(air, &tape) {
        return Err("public tape does not fit the AIR's public segments".into());
    }
    let pubs = verifier::public_inputs(air, &tape)
        .iter()
        .map(|x| x.as_canonical_u32())
        .collect();
    let msgs = verifier::pub_msgs(air, &tape)
        .into_iter()
        .map(|(b, s, m)| (b, s, m.iter().map(|x| x.as_canonical_u32()).collect()))
        .collect();
    Ok(Statement { pubs, msgs })
}
