//! claim-v3 / witness-v3 encoders (spec/claim-v3.md). Plain byte writers; the
//! layout here is the specification's, field by field.

pub struct W(pub Vec<u8>);

impl W {
    pub fn new() -> Self {
        W(Vec::new())
    }
    pub fn u8(&mut self, v: u8) {
        self.0.push(v)
    }
    pub fn u16(&mut self, v: u16) {
        self.0.extend_from_slice(&v.to_le_bytes())
    }
    pub fn u32(&mut self, v: u32) {
        self.0.extend_from_slice(&v.to_le_bytes())
    }
    pub fn u64(&mut self, v: u64) {
        self.0.extend_from_slice(&v.to_le_bytes())
    }
    pub fn u128(&mut self, v: u128) {
        self.0.extend_from_slice(&v.to_le_bytes())
    }
    pub fn hash(&mut self, h: &[u8; 32]) {
        self.0.extend_from_slice(h)
    }
    pub fn bytes(&mut self, b: &[u8]) {
        self.u32(b.len() as u32);
        self.0.extend_from_slice(b)
    }
}

pub const CLAIM_TAG: &str = "near-arena-claim-v3";
pub const WITNESS_TAG: &str = "near-arena-witness-v3";
pub const STATEMENT_ID: &str = "near/pv86/chunk-validation/v0";

#[derive(Clone)]
pub struct ChunkSlot {
    pub inner: Vec<u8>,
    pub height_included: u64,
}

#[derive(Clone)]
pub struct BlockRec {
    pub header_version: u8,
    pub prev_hash: [u8; 32],
    pub inner_lite: Vec<u8>,
    pub inner_rest: Vec<u8>,
    pub slots: Vec<ChunkSlot>,
}

#[derive(Clone)]
pub struct EpochRec {
    pub epoch_id: [u8; 32],
    pub protocol_version: u32,
    pub epoch_height: u64,
    pub shard_layout: Vec<u8>,
    pub validators: Vec<(String, u128)>,
}

#[derive(Clone)]
pub struct ValidatorUpdateFacts {
    pub stake_info: Vec<(String, u128)>,
    pub validator_rewards: Vec<(String, u128)>,
    pub protocol_treasury_account: Option<String>,
}

#[derive(Clone)]
pub struct SplitGate {
    pub memory_usage_threshold: u64,
    pub min_child_memory_usage: u64,
    pub max_number_of_shards: u64,
    pub force_split_shards: Vec<u64>,
    pub block_split_shards: Vec<u64>,
}

#[derive(Clone)]
pub struct ApplyFacts {
    pub validator_update: Option<ValidatorUpdateFacts>,
    pub minimum_stake: u128,
    pub split_gate: Option<SplitGate>,
}

#[derive(Clone)]
pub struct Claim {
    pub protocol_version: u32,
    pub chain_id: String,
    pub epoch_id: [u8; 32],
    pub chunk_inner: Vec<u8>,
    pub blocks: Vec<BlockRec>,
    pub rs_data_parts: u16,
    pub rs_total_parts: u16,
    pub epochs: Vec<EpochRec>,
    pub epoch_start_after: Vec<u8>,
    pub apply_facts: Vec<ApplyFacts>,
    pub tx_valid: Vec<u8>,
    pub genesis_chunk_extra: Option<Vec<u8>>,
}

fn acct_list(w: &mut W, v: &[(String, u128)]) {
    w.u32(v.len() as u32);
    for (a, s) in v {
        w.bytes(a.as_bytes());
        w.u128(*s);
    }
}

impl Claim {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = W::new();
        w.bytes(CLAIM_TAG.as_bytes());
        w.bytes(STATEMENT_ID.as_bytes());
        w.u32(self.protocol_version);
        w.bytes(self.chain_id.as_bytes());
        w.hash(&self.epoch_id);
        w.bytes(&self.chunk_inner);
        w.u32(self.blocks.len() as u32);
        for b in &self.blocks {
            w.u8(b.header_version);
            w.hash(&b.prev_hash);
            w.bytes(&b.inner_lite);
            w.bytes(&b.inner_rest);
            w.u32(b.slots.len() as u32);
            for s in &b.slots {
                w.bytes(&s.inner);
                w.u64(s.height_included);
            }
        }
        w.u16(self.rs_data_parts);
        w.u16(self.rs_total_parts);
        w.u32(self.epochs.len() as u32);
        for e in &self.epochs {
            w.hash(&e.epoch_id);
            w.u32(e.protocol_version);
            w.u64(e.epoch_height);
            w.bytes(&e.shard_layout);
            acct_list(&mut w, &e.validators);
        }
        w.bytes(&self.epoch_start_after);
        w.u32(self.apply_facts.len() as u32);
        for f in &self.apply_facts {
            match &f.validator_update {
                None => w.u8(0),
                Some(v) => {
                    w.u8(1);
                    acct_list(&mut w, &v.stake_info);
                    acct_list(&mut w, &v.validator_rewards);
                    match &v.protocol_treasury_account {
                        None => w.u8(0),
                        Some(a) => {
                            w.u8(1);
                            w.bytes(a.as_bytes());
                        }
                    }
                }
            }
            w.u128(f.minimum_stake);
            match &f.split_gate {
                None => w.u8(0),
                Some(g) => {
                    w.u8(1);
                    w.u64(g.memory_usage_threshold);
                    w.u64(g.min_child_memory_usage);
                    w.u64(g.max_number_of_shards);
                    w.u32(g.force_split_shards.len() as u32);
                    for s in &g.force_split_shards {
                        w.u64(*s);
                    }
                    w.u32(g.block_split_shards.len() as u32);
                    for s in &g.block_split_shards {
                        w.u64(*s);
                    }
                }
            }
        }
        w.bytes(&self.tx_valid);
        match &self.genesis_chunk_extra {
            None => w.u8(0),
            Some(b) => {
                w.u8(1);
                w.bytes(b);
            }
        }
        w.0
    }
}

pub fn encode_witness(state_witness: &[u8], codes: &[Vec<u8>]) -> Vec<u8> {
    let mut w = W::new();
    w.bytes(WITNESS_TAG.as_bytes());
    w.bytes(state_witness);
    w.u32(codes.len() as u32);
    for c in codes {
        w.bytes(c);
    }
    w.0
}

pub fn sha256(b: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    sha2::Sha256::digest(b).into()
}

/// block_hash(r) = SHA256(SHA256(SHA256(lite) ‖ SHA256(rest)) ‖ prev_hash)
pub fn block_hash(r: &BlockRec) -> [u8; 32] {
    let mut a = sha256(&r.inner_lite).to_vec();
    a.extend_from_slice(&sha256(&r.inner_rest));
    let mut b = sha256(&a).to_vec();
    b.extend_from_slice(&r.prev_hash);
    sha256(&b)
}
