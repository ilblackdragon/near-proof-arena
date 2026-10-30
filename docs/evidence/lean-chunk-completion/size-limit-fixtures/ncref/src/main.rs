//! W02 size-limit fixtures: nearcore 2.13.4's own codecs and caps, built without `test_features`.
//!
//! The fixture generator links nearcore with `test_features` (through `integration-tests`), and that
//! feature raises `MAX_COMPRESSED_STATE_WITNESS_SIZE` and the two `MAX_UNCOMPRESSED_*` caps to
//! 512 MiB (`partial_witness.rs:18-19`, `state_witness.rs:19-20`, `contract_distribution.rs:372-373`).
//! This tool links only `near-primitives` with production features, so the caps are 48 / 64 / 64 MiB.
//!
//!   ncref witness <in-the-clear witness.bin> <out-dir>
//!       Borsh-decode the `ChunkStateWitness`, encode it with `EncodedChunkStateWitness::encode`
//!       (nearcore's producer codec: zstd level 1, 4 workers), write `<out-dir>/enc.zst`, and for each
//!       padded variant (the encoding followed by one zstd skippable frame of zeros, total length
//!       exactly `target`) report: the partial-witness size check
//!       (`encoded_length > MAX_COMPRESSED_STATE_WITNESS_SIZE`, `validate.rs:82-88`) and the result of
//!       `EncodedChunkStateWitness::decode` (`identical` when it re-serializes to the input bytes).
//!   ncref codes <in-the-clear witness.bin>
//!       The appended contract codes as one `ContractCodeResponse` (PV86: the signed V2 variant), sent
//!       through borsh and `decompress_contracts` (`MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE`).
//!   ncref caps
//!       Print the three caps as compiled here.
//! Output is one JSON object on stdout.
use borsh::BorshDeserialize;
use near_primitives::stateless_validation::ChunkProductionKey;
use near_primitives::stateless_validation::contract_distribution::{
    CodeBytes, ContractCodeResponse, MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE,
};
use near_primitives::stateless_validation::partial_witness::MAX_COMPRESSED_STATE_WITNESS_SIZE;
use near_primitives::stateless_validation::state_witness::{
    ChunkStateWitness, EncodedChunkStateWitness, MAX_UNCOMPRESSED_STATE_WITNESS_SIZE,
};
use near_primitives::types::{EpochId, ShardId};
use near_primitives::utils::compression::CompressedData;
use near_primitives::validator_signer::EmptyValidatorSigner;
use sha2::{Digest, Sha256};
use std::sync::Arc;

const TAG: &[u8] = b"near-arena-witness-v3";
/// The zstd skippable-frame magic used for padding (RFC 8878 §3.1.2: 0x184D2A5?).
const SKIP_MAGIC: u32 = 0x184D2A50;

fn sha(b: &[u8]) -> String {
    hex::encode(Sha256::digest(b))
}

fn read_u32(b: &[u8], off: &mut usize) -> usize {
    let v = u32::from_le_bytes(b[*off..*off + 4].try_into().unwrap()) as usize;
    *off += 4;
    v
}

/// (state_witness bytes, codes) of an in-the-clear `witness.bin`.
fn parse_witness_bin(raw: &[u8]) -> (Vec<u8>, Vec<Vec<u8>>) {
    let mut off = 0;
    let tl = read_u32(raw, &mut off);
    assert_eq!(&raw[off..off + tl], TAG, "not an in-the-clear witness.bin");
    off += tl;
    let sl = read_u32(raw, &mut off);
    let sw = raw[off..off + sl].to_vec();
    off += sl;
    let n = read_u32(raw, &mut off);
    let mut codes = Vec::with_capacity(n);
    for _ in 0..n {
        let l = read_u32(raw, &mut off);
        codes.push(raw[off..off + l].to_vec());
        off += l;
    }
    assert_eq!(off, raw.len(), "trailing bytes in witness.bin");
    (sw, codes)
}

/// `enc` followed by one skippable frame of zeros so that the total length is `target`.
pub fn pad(enc: &[u8], target: usize) -> Option<Vec<u8>> {
    if target < enc.len() + 8 {
        return None;
    }
    let body = target - enc.len() - 8;
    let mut out = Vec::with_capacity(target);
    out.extend_from_slice(enc);
    out.extend_from_slice(&SKIP_MAGIC.to_le_bytes());
    out.extend_from_slice(&(u32::try_from(body).ok()?).to_le_bytes());
    out.resize(target, 0);
    Some(out)
}

fn decode_check(bytes: Vec<u8>, sw: &[u8]) -> String {
    let e = EncodedChunkStateWitness::from(bytes.into_boxed_slice());
    match e.decode() {
        Ok((w, n)) => {
            let again = borsh::to_vec(&w).unwrap();
            if again == sw && n == sw.len() { "identical".into() } else { format!("different({n})") }
        }
        Err(err) => format!("error: {err}"),
    }
}

fn cmd_witness(path: &str, out: &str) {
    let raw = std::fs::read(path).unwrap();
    let (sw, _codes) = parse_witness_bin(&raw);
    let cap = MAX_COMPRESSED_STATE_WITNESS_SIZE.as_u64() as usize;
    let w = match ChunkStateWitness::try_from_slice(&sw) {
        Ok(w) => w,
        Err(e) => {
            println!("{{\"sw_len\":{},\"undecodable\":{:?}}}", sw.len(), e.to_string());
            return;
        }
    };
    let canonical = borsh::to_vec(&w).unwrap() == sw;
    let (enc, raw_len) = EncodedChunkStateWitness::encode(&w).unwrap();
    let enc = enc.as_slice().to_vec();
    std::fs::create_dir_all(out).unwrap();
    std::fs::write(format!("{out}/enc.zst"), &enc).unwrap();
    let plain = decode_check(enc.clone(), &sw);
    let mut vars = Vec::new();
    for (name, target) in [("under48", cap - 1), ("at48", cap), ("over48", cap + 1)] {
        let Some(p) = pad(&enc, target) else { continue };
        let digest = sha(&p);
        let cap_rejects = p.len() > cap;
        let dec = decode_check(p, &sw);
        vars.push(format!(
            "\"{name}\":{{\"len\":{target},\"sha256\":\"{digest}\",\"cap_rejects\":{cap_rejects},\"decode\":{dec:?}}}"
        ));
    }
    println!(
        "{{\"sw_len\":{},\"raw_len\":{raw_len},\"canonical\":{canonical},\"enc_len\":{},\"enc_sha256\":\"{}\",\"cap\":{cap},\"plain\":{{\"decode\":{plain:?}}},\"variants\":{{{}}}}}",
        sw.len(), enc.len(), sha(&enc), vars.join(",")
    );
}

fn cmd_codes(path: &str) {
    let raw = std::fs::read(path).unwrap();
    let (_sw, codes) = parse_witness_bin(&raw);
    let cb: Vec<CodeBytes> = codes.iter().map(|c| CodeBytes(Arc::from(c.as_slice()))).collect();
    let borsh_len = borsh::to_vec(&cb).unwrap().len();
    let key = ChunkProductionKey { shard_id: ShardId::new(0), epoch_id: EpochId::default(), height_created: 1 };
    let signer = EmptyValidatorSigner::new("responder".parse().unwrap());
    let resp = ContractCodeResponse::encode(key, &cb, &signer, 86).unwrap();
    // as received from the network
    let resp = ContractCodeResponse::try_from_slice(&borsh::to_vec(&resp).unwrap()).unwrap();
    let variant = match resp { ContractCodeResponse::V1(_) => "V1", ContractCodeResponse::V2(_) => "V2" };
    let dec = match resp.decompress_contracts() {
        Ok(v) => {
            let same = v.len() == cb.len() && v.iter().zip(&cb).all(|(a, b)| a.0 == b.0);
            if same { "ok".to_string() } else { "different".to_string() }
        }
        Err(e) => format!("error: {e}"),
    };
    println!(
        "{{\"n_codes\":{},\"code_bytes\":{},\"borsh_len\":{borsh_len},\"cap\":{MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE},\"response\":\"{variant}\",\"decompress\":{dec:?}}}",
        cb.len(), codes.iter().map(|c| c.len()).sum::<usize>()
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("witness") => cmd_witness(&args[2], &args[3]),
        Some("codes") => cmd_codes(&args[2]),
        Some("caps") => println!(
            "{{\"MAX_COMPRESSED_STATE_WITNESS_SIZE\":{},\"MAX_UNCOMPRESSED_STATE_WITNESS_SIZE\":{},\"MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE\":{}}}",
            MAX_COMPRESSED_STATE_WITNESS_SIZE.as_u64(), MAX_UNCOMPRESSED_STATE_WITNESS_SIZE, MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE
        ),
        _ => {
            eprintln!("usage: ncref witness <witness.bin> <out-dir> | ncref codes <witness.bin> | ncref caps");
            std::process::exit(2);
        }
    }
}
