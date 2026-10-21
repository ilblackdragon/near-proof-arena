//! SHA-384 / BabyBear-Ext12 STARK protocol configuration (NEAR PQ native profile).
//!
//! Byte-for-byte the configuration of
//! `research/near-compression/airbender/direct-wasm/native_sha384_config.rs`
//! (transcript framing, rejection sampling, Merkle leaf/node formats, digest codec),
//! extended with the hash-level levers of `native_sha384_levers_config.rs`
//! (lane/pq-whir-levers): digest width 48 / 42 bytes, coset-as-one-message leaves (tag 6),
//! proof-of-work by hashing (tag 7, one or two witness elements).  The levers are
//! process-global (env `NEARPROOF_DIGEST_BYTES`, `NEARPROOF_COSET_LEAF`), because the codec
//! traits are static.  With every lever at its default this is byte-for-byte the native
//! profile (framing "nearproof-native-sha384-ext12-v4"); proofs with zero PoW bits are
//! identical.  `tests::native_*` cross-check against the native file and its recorded vectors.
use std::io::{self, Read, Write};

use openvm_cpu_backend::{CpuBackend, CpuDevice};
use openvm_stark_backend::{
    codec::{
        decode_extension_field32, decode_prime_field32, encode_extension_field32,
        encode_prime_field32, DecodableConfig, EncodableConfig,
    },
    hasher::MerkleHasher,
    prover::{Coordinator, CpuColMajorBackend, ReferenceDevice},
    FiatShamirTranscript, StarkEngine, StarkProtocolConfig, SystemParams, TranscriptHistory,
};
use p3_field::{extension::BinomialExtensionField, PrimeCharacteristicRing, PrimeField32};
use sha2::{Digest as _, Sha384};

pub type F = p3_baby_bear::BabyBear;
pub type EF = BinomialExtensionField<F, 12>;
pub const D_EF: usize = 12;
/// Native digest: SHA-384 output bytes read as six little-endian u64 words.
pub type Digest = [u64; 6];
/// In-circuit digest: the six SHA-512 state words H0..H5, four 16-bit limbs each, low first.
pub const DIGEST_SIZE: usize = 24;
/// Row packing of InitialOpenedValuesAir: opened-row values per row (not a hash parameter).
pub const CHUNK: usize = 8;
pub const PREFIX: &[u8; 32] = b"nearproof-native-sha384-ext12-v4";
pub const NODE_PREFIX: &[u8; 8] = b"NPQ4NODE";
pub const TAG_LEAF: u8 = 0;
pub const TAG_INIT: u8 = 2;
pub const TAG_FLUSH: u8 = 3;
pub const TAG_COMMIT: u8 = 4;
pub const TAG_SQUEEZE: u8 = 5;
pub const TAG_COSET_LEAF: u8 = 6;
pub const TAG_POW: u8 = 7;
/// Statement digest (NV level 1 hashes the app proof's public values; final-soundness G1)
pub const TAG_STATEMENT: u8 = 8;

/// The statement message of an app proof's public values: [num_airs, len_0, .., len_{m-1},
/// pv_0.., pv_1.., ..] (per-AIR lengths make it injective).
pub fn statement_values(pvs: &[Vec<F>]) -> Vec<F> {
    let mut v = vec![F::from_usize(pvs.len())];
    v.extend(pvs.iter().map(|p| F::from_usize(p.len())));
    v.extend(pvs.iter().flatten().copied());
    v
}
/// Statement digest = SHA-384(prefix, tag 8, statement_values) (truncated like Merkle digests).
pub fn statement_digest(pvs: &[Vec<F>]) -> Digest {
    digest_from_bytes(truncate_digest(hash_parts(TAG_STATEMENT, &[&felt_bytes(&statement_values(pvs))])))
}
/// [agg] Segment-range statement digest (aggregation tree; results/pq-base-aggregation):
/// D = SHA-384(prefix, tag 9, range_values(..)), truncated like Merkle digests (42 B under the
/// lever; narrow-leaf oracle class with tags 0 and 6).
pub const TAG_RANGE: u8 = 9;

/// [agg] Range statement message [n_ctx, n_state, ctx.., a, e, s_a.., s_e..]: segments
/// [a, e) of the chunk named by ctx, from boundary state s_a to boundary state s_e.
pub fn range_values(ctx: &[F], a: F, e: F, s_a: &[F], s_e: &[F]) -> Vec<F> {
    assert_eq!(s_a.len(), s_e.len());
    let mut v = vec![F::from_usize(ctx.len()), F::from_usize(s_a.len())];
    v.extend_from_slice(ctx);
    v.push(a);
    v.push(e);
    v.extend_from_slice(s_a);
    v.extend_from_slice(s_e);
    v
}
/// [agg] Range statement digest (what V_d compares with the claimed chunk statement).
pub fn range_digest(ctx: &[F], a: F, e: F, s_a: &[F], s_e: &[F]) -> Digest {
    digest_from_bytes(truncate_digest(hash_parts(TAG_RANGE, &[&felt_bytes(&range_values(ctx, a, e, s_a, s_e))])))
}

/// Hash-level levers (process-global; read once from the environment).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShaLevers {
    /// Merkle digest width in bytes: 48 (SHA-384) or 42 (SHA-384 truncated to 336 bits).
    pub digest_bytes: usize,
    /// Hash each WHIR leaf (all 2^k rows of a fold coset) as one SHA-384 message (tag 6).
    pub coset_leaf: bool,
    /// T* transcript (final-soundness T*-1, T*-2): counter-mode squeezing
    /// B_j = H(5, kappa || le32(j)) from the post-absorb key kappa, and PoW blocks
    /// B_j = H(7, sigma || w || le32(j)) with the PoW on the first z bits of B_1 and the following
    /// challenges from B_1's remaining 64-bit words, then B_2, ...; a zero witness when z = 0.
    pub tstar: bool,
}
impl ShaLevers {
    pub const DEFAULT: ShaLevers = ShaLevers { digest_bytes: 48, coset_leaf: false, tstar: false };
    pub fn is_default(&self) -> bool {
        *self == Self::DEFAULT
    }
    /// 32-byte framing prefix of every `hash_parts` message.
    pub fn prefix(&self) -> [u8; 32] {
        let s = if self.is_default() {
            "nearproof-native-sha384-ext12-v4".to_string()
        } else {
            format!("nearproof-sha384-ext12-v{}-w{:02}-c{}", if self.tstar { 6 } else { 5 }, self.digest_bytes, self.coset_leaf as u8)
        };
        s.as_bytes().try_into().expect("32-byte prefix")
    }
    /// 8-byte node-compression prefix.
    pub fn node_prefix(&self) -> [u8; 8] {
        if self.is_default() {
            *b"NPQ4NODE"
        } else {
            [b'N', b'P', b'Q', b'5', self.digest_bytes as u8, self.coset_leaf as u8, b'N', b'D']
        }
    }
}
/// The process's hash levers (env NEARPROOF_DIGEST_BYTES = 48 | 42, NEARPROOF_COSET_LEAF = 0 | 1,
/// NEARPROOF_TSTAR = 1 (default) | 0; 0 = the legacy v4/v5 chained squeeze, kept for the native
/// vector and differential tests).
pub fn sha_levers() -> ShaLevers {
    static L: std::sync::OnceLock<ShaLevers> = std::sync::OnceLock::new();
    *L.get_or_init(|| {
        let get = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
        let l = ShaLevers {
            digest_bytes: get("NEARPROOF_DIGEST_BYTES", 48),
            coset_leaf: get("NEARPROOF_COSET_LEAF", 0) == 1,
            tstar: get("NEARPROOF_TSTAR", 1) == 1,
        };
        assert!(l.digest_bytes == 48 || l.digest_bytes == 42, "digest width must be 48 or 42 bytes");
        l
    })
}
/// Zero the bytes beyond the digest width.
pub fn truncate_digest(mut d: [u8; 48]) -> [u8; 48] {
    let w = sha_levers().digest_bytes;
    for b in &mut d[w..] {
        *b = 0;
    }
    d
}
/// Wire / absorbed form of a digest: its first `digest_bytes` bytes.
pub fn digest_wire(d: Digest) -> Vec<u8> {
    let mut b = digest_bytes(d).to_vec();
    b.truncate(sha_levers().digest_bytes);
    b
}
/// `sample()` accepts a little-endian state word n iff n < SAMPLE_BOUND (= 2p).
pub const SAMPLE_BOUND: u64 = 4026531842;
pub const BABYBEAR_P: u64 = 2013265921;

pub fn digest_bytes(d: Digest) -> [u8; 48] {
    let mut out = [0u8; 48];
    for (i, w) in d.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    out
}
pub fn digest_from_bytes(b: [u8; 48]) -> Digest {
    std::array::from_fn(|i| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap()))
}
/// SHA-512 state words H0..H5 of a native digest (big-endian reading of the digest bytes).
pub fn digest_words(d: Digest) -> [u64; 6] {
    d.map(u64::swap_bytes)
}
pub fn digest_from_words(h: [u64; 6]) -> Digest {
    h.map(u64::swap_bytes)
}
pub fn word_limbs(w: u64) -> [u32; 4] {
    std::array::from_fn(|k| ((w >> (16 * k)) & 0xffff) as u32)
}
pub fn limbs_word(l: &[u32]) -> u64 {
    (0..4).fold(0u64, |acc, k| acc | ((l[k] as u64) << (16 * k)))
}
/// In-circuit representation of a digest (24 limbs, H0 limb 0 first).
pub fn digest_to_limbs(d: Digest) -> [F; DIGEST_SIZE] {
    let h = digest_words(d);
    std::array::from_fn(|i| F::from_u32(word_limbs(h[i / 4])[i % 4]))
}
pub fn limbs_to_digest(l: &[F]) -> Digest {
    let u: Vec<u32> = l.iter().map(|x| x.as_canonical_u32()).collect();
    digest_from_words(std::array::from_fn(|i| limbs_word(&u[4 * i..4 * i + 4])))
}

/// The framed message hashed by `hash_parts` (prefix, tag, then length-prefixed parts).
pub fn hash_parts_message(tag: u8, parts: &[&[u8]]) -> Vec<u8> {
    let mut m = Vec::with_capacity(33 + parts.iter().map(|p| 8 + p.len()).sum::<usize>());
    m.extend_from_slice(&sha_levers().prefix());
    m.push(tag);
    for p in parts {
        m.extend_from_slice(&(p.len() as u64).to_le_bytes());
        m.extend_from_slice(p);
    }
    m
}
pub fn hash_parts(tag: u8, parts: &[&[u8]]) -> [u8; 48] {
    let mut h = Sha384::new();
    h.update(sha_levers().prefix());
    h.update([tag]);
    for p in parts {
        h.update((p.len() as u64).to_le_bytes());
        h.update(p);
    }
    h.finalize().into()
}
/// Node message `node_prefix || left_w || right_w` (8 + 2w <= 104 bytes, one compression).
pub fn node_message(left: Digest, right: Digest) -> Vec<u8> {
    let mut m = sha_levers().node_prefix().to_vec();
    m.extend(digest_wire(left));
    m.extend(digest_wire(right));
    m
}
pub fn felt_bytes(values: &[F]) -> Vec<u8> {
    values
        .iter()
        .flat_map(|x| x.as_canonical_u32().to_le_bytes())
        .collect()
}

/// Merkle hasher. `final_layer` (user decision U-12): the final recursive layer (verified
/// natively by V_d) uses its own node framing (node prefix byte 7 = 'F'), distinct from inner
/// layers; with the transcript init flag this separates the final layer's hash domain.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ShaHasher {
    pub final_layer: bool,
}
/// The inner-layer hasher (kept as a value so `ShaHasher.hash_slice(..)` reads as before).
#[allow(non_upper_case_globals)]
pub const ShaHasher: ShaHasher = ShaHasher { final_layer: false };
/// Final-layer node prefix: the inner prefix with its last byte replaced by 'F'.
pub fn node_prefix_layer(final_layer: bool) -> [u8; 8] {
    let mut p = sha_levers().node_prefix();
    if final_layer {
        p[7] = b'F';
    }
    p
}
/// Transcript initial state: H(2, []) for inner layers, H(2, [0x46]) for the final layer.
pub fn initial_state_layer(final_layer: bool) -> [u8; 48] {
    if final_layer {
        hash_parts(TAG_INIT, &[&[b'F']])
    } else {
        initial_state()
    }
}
impl MerkleHasher for ShaHasher {
    type F = F;
    type Digest = Digest;
    fn hash_slice(&self, values: &[F]) -> Digest {
        digest_from_bytes(truncate_digest(hash_parts(TAG_LEAF, &[&felt_bytes(values)])))
    }
    fn compress(&self, left: Digest, right: Digest) -> Digest {
        let mut m = node_message(left, right);
        m[..8].copy_from_slice(&node_prefix_layer(self.final_layer));
        digest_from_bytes(truncate_digest(Sha384::digest(m).into()))
    }
    fn hash_coset(&self, rows: &[Vec<F>]) -> Digest {
        if !sha_levers().coset_leaf {
            return self.tree_compress(rows.iter().map(|row| self.hash_slice(row)).collect());
        }
        // One message: rows t = 0..2^k in coset order, each row's canonical u32 LE words.
        let bytes: Vec<u8> = rows.iter().flat_map(|r| felt_bytes(r)).collect();
        digest_from_bytes(truncate_digest(hash_parts(TAG_COSET_LEAF, &[&bytes])))
    }
    /// [pq-cpu-prover] multi-buffer SHA-384 over the leaves (same messages as `hash_coset`).
    fn hash_coset_batch(&self, leaves: &[Vec<Vec<F>>]) -> Vec<Digest> {
        if !crate::sha384::mb::mb_enabled() {
            return leaves.iter().map(|r| self.hash_coset(r)).collect();
        }
        if sha_levers().coset_leaf {
            let msgs: Vec<Vec<u8>> = leaves
                .iter()
                .map(|rows| {
                    let bytes: Vec<u8> = rows.iter().flat_map(|r| felt_bytes(r)).collect();
                    hash_parts_message(TAG_COSET_LEAF, &[&bytes])
                })
                .collect();
            let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
            crate::sha384::mb::sha384_many(&refs)
                .into_iter()
                .map(|h| digest_from_bytes(truncate_digest(h)))
                .collect()
        } else {
            // row hashes of every leaf, then each leaf's binary subtree, level by level
            let msgs: Vec<Vec<u8>> = leaves
                .iter()
                .flat_map(|rows| rows.iter().map(|r| hash_parts_message(TAG_LEAF, &[&felt_bytes(r)])))
                .collect();
            let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
            let mut level: Vec<Digest> = crate::sha384::mb::sha384_many(&refs)
                .into_iter()
                .map(|h| digest_from_bytes(truncate_digest(h)))
                .collect();
            let per = leaves.first().map_or(1, |r| r.len());
            assert!(leaves.iter().all(|r| r.len() == per) && per.is_power_of_two());
            let mut w = per;
            while w > 1 {
                level = self.compress_pairs(&level);
                w /= 2;
            }
            level
        }
    }
    /// [pq-cpu-prover] leaves straight from a flat buffer: one byte arena, no per-row vectors.
    fn hash_leaves_flat(&self, data: &[F], row_len: usize, rows_per_leaf: usize) -> Vec<Digest> {
        let per = row_len * rows_per_leaf;
        if !crate::sha384::mb::mb_enabled() || per == 0 {
            let leaves: Vec<Vec<Vec<F>>> = data
                .chunks_exact(per.max(1))
                .map(|leaf| leaf.chunks_exact(row_len.max(1)).map(|r| r.to_vec()).collect())
                .collect();
            return self.hash_coset_batch(&leaves);
        }
        let n = data.len() / per;
        // message = prefix(32) || tag || le64(len) || parts; one part per message
        let (tag, part_len, parts_per_leaf) = if sha_levers().coset_leaf {
            (TAG_COSET_LEAF, 4 * per, 1)
        } else {
            (TAG_LEAF, 4 * row_len, rows_per_leaf)
        };
        let prefix = sha_levers().prefix();
        let mlen = 32 + 1 + 8 + part_len;
        let nmsg = n * parts_per_leaf;
        let mut arena = vec![0u8; nmsg * mlen];
        for (mi, m) in arena.chunks_exact_mut(mlen).enumerate() {
            m[..32].copy_from_slice(&prefix);
            m[32] = tag;
            m[33..41].copy_from_slice(&(part_len as u64).to_le_bytes());
            let vals = &data[mi * (part_len / 4)..(mi + 1) * (part_len / 4)];
            for (o, v) in m[41..].chunks_exact_mut(4).zip(vals) {
                o.copy_from_slice(&v.as_canonical_u32().to_le_bytes());
            }
        }
        let refs: Vec<&[u8]> = arena.chunks_exact(mlen).collect();
        let mut level: Vec<Digest> = crate::sha384::mb::sha384_many(&refs)
            .into_iter()
            .map(|h| digest_from_bytes(truncate_digest(h)))
            .collect();
        if parts_per_leaf > 1 {
            assert!(rows_per_leaf.is_power_of_two());
            let mut w = rows_per_leaf;
            while w > 1 {
                level = self.compress_pairs(&level);
                w /= 2;
            }
        }
        level
    }
    /// [pq-cpu-prover] multi-buffer node compression.
    fn compress_pairs(&self, inputs: &[Digest]) -> Vec<Digest> {
        if !crate::sha384::mb::mb_enabled() {
            return inputs.chunks_exact(2).map(|p| self.compress(p[0], p[1])).collect();
        }
        // one arena of `prefix || wire(l) || wire(r)` messages (no per-pair vectors)
        let prefix = node_prefix_layer(self.final_layer);
        let wb = sha_levers().digest_bytes;
        let mlen = 8 + 2 * wb;
        let np = inputs.len() / 2;
        let mut arena = vec![0u8; np * mlen];
        for (m, p) in arena.chunks_exact_mut(mlen).zip(inputs.chunks_exact(2)) {
            m[..8].copy_from_slice(&prefix);
            m[8..8 + wb].copy_from_slice(&digest_bytes(p[0])[..wb]);
            m[8 + wb..].copy_from_slice(&digest_bytes(p[1])[..wb]);
        }
        let refs: Vec<&[u8]> = arena.chunks_exact(mlen).collect();
        crate::sha384::mb::sha384_many(&refs).into_iter().map(|h| digest_from_bytes(truncate_digest(h))).collect()
    }
}

#[derive(Clone, Debug)]
pub struct Sha384Config {
    params: SystemParams,
    hasher: ShaHasher,
}
impl Sha384Config {
    pub fn new(params: SystemParams) -> Self {
        Self {
            params,
            hasher: ShaHasher,
        }
    }
    /// Final recursive layer (U-12): own transcript init and node framing.
    pub fn new_final(params: SystemParams) -> Self {
        Self {
            params,
            hasher: ShaHasher { final_layer: true },
        }
    }
}
impl StarkProtocolConfig for Sha384Config {
    type F = F;
    type EF = EF;
    type Digest = Digest;
    type Hasher = ShaHasher;
    fn params(&self) -> &SystemParams {
        &self.params
    }
    fn hasher(&self) -> &ShaHasher {
        &self.hasher
    }
}
impl EncodableConfig for Sha384Config {
    fn encode_base_field<W: Write>(v: &F, w: &mut W) -> io::Result<()> {
        encode_prime_field32(v, w)
    }
    fn encode_extension_field<W: Write>(v: &EF, w: &mut W) -> io::Result<()> {
        encode_extension_field32::<F, _, _>(v, w)
    }
    fn encode_digest<W: Write>(v: &Digest, w: &mut W) -> io::Result<()> {
        w.write_all(&digest_wire(*v))
    }
}
impl DecodableConfig for Sha384Config {
    fn decode_base_field<R: Read>(r: &mut R) -> io::Result<F> {
        decode_prime_field32(r)
    }
    fn decode_extension_field<R: Read>(r: &mut R) -> io::Result<EF> {
        decode_extension_field32::<F, _, _>(r)
    }
    fn decode_digest<R: Read>(r: &mut R) -> io::Result<Digest> {
        let mut b = [0; 48];
        r.read_exact(&mut b[..sha_levers().digest_bytes])?;
        Ok(digest_from_bytes(b))
    }
}

/// Initial transcript state `hash_parts(2, [])`.
pub fn initial_state() -> [u8; 48] {
    hash_parts(TAG_INIT, &[])
}

/// Squeeze source under T*: the post-absorb key (tag 5) or a PoW run (tag 7, sigma and the
/// witness bytes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SqueezeSrc {
    Key([u8; 48]),
    Pow([u8; 48], Vec<u8>),
}
impl SqueezeSrc {
    /// Block j (T*): H(5, kappa || le32(j)) or H(7, sigma || w || le32(j)).
    pub fn block(&self, j: u32) -> [u8; 48] {
        match self {
            SqueezeSrc::Key(k) => hash_parts(TAG_SQUEEZE, &[k, &j.to_le_bytes()]),
            SqueezeSrc::Pow(s, w) => {
                let mut m = w.clone();
                m.extend_from_slice(&j.to_le_bytes());
                hash_parts(TAG_POW, &[s, &m])
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct ShaTranscript {
    /// last absorbed key or last block consumed (the state the next absorb starts from)
    pub state: [u8; 48],
    pub next_word: usize,
    pub pending: Vec<u8>,
    /// T*: squeeze source and the index of the last block taken from it
    pub src: SqueezeSrc,
    pub ctr: u32,
}
impl Default for ShaTranscript {
    fn default() -> Self {
        Self {
            state: initial_state(),
            next_word: 12,
            pending: Vec::new(),
            src: SqueezeSrc::Key(initial_state()),
            ctr: 0,
        }
    }
}
/// First candidate (u32 index into a block) available to challenges after a PoW on `bits` bits:
/// the PoW bits occupy the first ceil(bits / 64) 64-bit words of B_1.
pub fn pow_skip_words(bits: usize) -> usize {
    assert!(bits <= 64, "T* PoW uses at most the first 64-bit word");
    2 * bits.div_ceil(64)
}
fn leading_zero_bits(s: &[u8; 48]) -> usize {
    let mut n = 0;
    for &b in s {
        if b == 0 {
            n += 8;
        } else {
            n += b.leading_zeros() as usize;
            break;
        }
    }
    n
}
/// PoW step (levers spec): state' = H(tag 7, state || witness words LE32); valid iff the first
/// `bits` bits of state' (byte 0 first, MSB first) are zero.
/// Under T*: B_1 = H(7, state || witness LE32 || le32(1)).
pub fn pow_step(state: &[u8; 48], witness: &[u32], bits: usize) -> ([u8; 48], bool) {
    let w: Vec<u8> = witness.iter().flat_map(|x| x.to_le_bytes()).collect();
    let s = if sha_levers().tstar {
        SqueezeSrc::Pow(*state, w).block(1)
    } else {
        hash_parts(TAG_POW, &[state, &w])
    };
    (s, leading_zero_bits(&s) >= bits)
}
/// [pq-cpu-prover] PoW message for witness words `w` (the preimage `pow_step` hashes).
pub fn pow_message(state: &[u8; 48], witness: &[u32]) -> Vec<u8> {
    let mut w: Vec<u8> = witness.iter().flat_map(|x| x.to_le_bytes()).collect();
    if sha_levers().tstar {
        w.extend_from_slice(&1u32.to_le_bytes());
    }
    hash_parts_message(TAG_POW, &[state, &w])
}

/// [pq-cpu-prover] `grind_n` with the 8-lane SHA-384: the same smallest witness (chunks of 2^16
/// candidates in order, the first valid candidate of the first chunk that has one).
pub fn grind_mb(base: &[u8; 48], bits: usize, wide: bool) -> Vec<u32> {
    use p3_maybe_rayon::prelude::*;
    // 2^22 candidates per parallel region (the smallest valid one is still returned); the
    // original 2^16-candidate regions stall on synchronisation once hashing is 10x faster.
    const CH: u32 = 1 << 22;
    let mut w0 = 0u32;
    let wit = |w0: u32, w: u32| if wide { vec![w0, w] } else { vec![w] };
    loop {
        let tmpl = pow_message(base, &wit(w0, 0));
        // byte offset of the searched witness word in the message
        let off = 32 + 1 + 8 + 48 + 8 + if wide { 4 } else { 0 };
        // the original searches w < (p / 2^16) * 2^16 in order; same range here
        let limit = (2013265921u32 / (1 << 16)) * (1 << 16);
        for chunk in 0..limit.div_ceil(CH) {
            let lo = chunk * CH;
            let ngroups = (CH.min(limit - lo)) / 8;
            // groups of 16 candidates (two interleaved 8-lane SHA-384 compressions); the
            // message words before the witness are shared, so their rounds run once
            let n = tmpl.len();
            assert!(n + 17 <= 128, "PoW message is one block");
            let mut blk0 = [0u8; 128];
            blk0[..n].copy_from_slice(&tmpl);
            blk0[n] = 0x80;
            blk0[112..].copy_from_slice(&((n as u128) * 8).to_be_bytes());
            let k_shared = off / 8;
            let s_k = crate::sha384::mb::state_after_rounds(&blk0, k_shared);
            let hit = (0..ngroups / 2).into_par_iter().find_map_first(|g| {
                let mut msgs = [blk0; 16];
                for (l, m) in msgs.iter_mut().enumerate() {
                    m[off..off + 4].copy_from_slice(&(lo + 16 * g + l as u32).to_le_bytes());
                }
                #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
                let hs = crate::sha384::mb::sha384_x16_blocks_from(&s_k, k_shared, &msgs);
                #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
                let refs: [&[u8]; 16] = core::array::from_fn(|l| &msgs[l][..n]);
                #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
                let hs: [[u8; 48]; 16] = core::array::from_fn(|l| Sha384::digest(refs[l]).into());
                (0..16).find(|&l| leading_zero_bits(&hs[l]) >= bits).map(|l| lo + 16 * g + l as u32)
            });
            if let Some(w) = hit {
                return wit(w0, w);
            }
        }
        assert!(wide, "no PoW witness");
        w0 += 1;
    }
}

impl ShaTranscript {
    /// Fresh transcript of the inner or the final layer (U-12).
    pub fn new_layer(final_layer: bool) -> Self {
        let s = initial_state_layer(final_layer);
        Self { state: s, src: SqueezeSrc::Key(s), ..Self::default() }
    }
    /// Smallest valid witness (lexicographic (w0, w1) when wide), searched in parallel chunks.
    fn grind_n(&mut self, bits: usize, wide: bool) -> Vec<u32> {
        use p3_maybe_rayon::prelude::*;
        self.flush();
        let base = self.state;
        if crate::sha384::mb::mb_enabled() {
            return grind_mb(&base, bits, wide);
        }
        const CH: u32 = 1 << 16;
        let mut w0 = 0u32;
        loop {
            for chunk in 0..(2013265921u32 / CH) {
                let lo = chunk * CH;
                let hit = (lo..lo + CH).into_par_iter().find_first(|&w| {
                    if wide {
                        pow_step(&base, &[w0, w], bits).1
                    } else {
                        pow_step(&base, &[w], bits).1
                    }
                });
                if let Some(w) = hit {
                    return if wide { vec![w0, w] } else { vec![w] };
                }
            }
            assert!(wide, "no PoW witness");
            w0 += 1;
        }
    }
    pub fn flush(&mut self) {
        if !self.pending.is_empty() {
            let k = hash_parts(TAG_FLUSH, &[&self.state, &self.pending]);
            self.pending.clear();
            self.absorbed(k);
        }
    }
    /// New post-absorb key kappa: state = kappa, squeeze counter reset.
    fn absorbed(&mut self, k: [u8; 48]) {
        self.state = k;
        self.next_word = 12;
        self.src = SqueezeSrc::Key(k);
        self.ctr = 0;
    }
    /// PoW (both widths): flush, then B_1 from (state, witness); T* keeps the run's source so
    /// later challenges read B_1's remaining words, then B_2, ...
    fn pow_apply(&mut self, bits: usize, w: &[u32]) -> bool {
        if bits == 0 {
            // G-11 (T*): no PoW, the witness must be zero
            return !sha_levers().tstar || w.iter().all(|&x| x == 0);
        }
        self.flush();
        let (s, ok) = pow_step(&self.state, w, bits);
        if sha_levers().tstar {
            self.src = SqueezeSrc::Pow(self.state, w.iter().flat_map(|x| x.to_le_bytes()).collect());
            self.ctr = 1;
            self.state = s;
            self.next_word = pow_skip_words(bits);
        } else {
            self.state = s;
            self.next_word = 12;
        }
        ok
    }
}
impl FiatShamirTranscript<Sha384Config> for ShaTranscript {
    fn observe(&mut self, v: F) {
        self.pending
            .extend_from_slice(&v.as_canonical_u32().to_le_bytes());
        self.next_word = 12;
    }
    fn observe_commit(&mut self, d: Digest) {
        self.flush();
        let k = hash_parts(TAG_COMMIT, &[&self.state, &digest_wire(d)]);
        self.absorbed(k);
    }
    fn check_witness(&mut self, bits: usize, witness: F) -> bool {
        self.pow_apply(bits, &[witness.as_canonical_u32()])
    }
    fn grind(&mut self, bits: usize) -> F {
        if bits == 0 {
            return F::ZERO;
        }
        assert!(bits <= 28, "grinding above 28 bits needs the wide witness");
        let w = F::from_u32(self.grind_n(bits, false)[0]);
        assert!(self.check_witness(bits, w));
        w
    }
    fn check_witness_wide(&mut self, bits: usize, w: [F; 2]) -> bool {
        self.pow_apply(bits, &[w[0].as_canonical_u32(), w[1].as_canonical_u32()])
    }
    fn grind_wide(&mut self, bits: usize) -> [F; 2] {
        if bits == 0 {
            return [F::ZERO; 2];
        }
        let v = self.grind_n(bits, true);
        let w = [F::from_u32(v[0]), F::from_u32(v[1])];
        assert!(self.check_witness_wide(bits, w));
        w
    }
    fn sample(&mut self) -> F {
        self.flush();
        loop {
            if self.next_word == 12 {
                self.state = if sha_levers().tstar {
                    self.ctr += 1;
                    self.src.block(self.ctr)
                } else {
                    hash_parts(TAG_SQUEEZE, &[&self.state])
                };
                self.next_word = 0;
            }
            let start = 4 * self.next_word;
            self.next_word += 1;
            let n = u32::from_le_bytes(self.state[start..start + 4].try_into().unwrap());
            if (n as u64) < SAMPLE_BOUND {
                return F::from_u32(n % (BABYBEAR_P as u32));
            }
        }
    }
}

/// Transcript event kinds as carried on the in-circuit transcript bus (`is_sample` field).
pub const KIND_OBSERVE: u32 = 0;
pub const KIND_SAMPLE: u32 = 1;
pub const KIND_COMMIT: u32 = 2;
/// PoW witness element (first) / continuation element (wide witness) in NV transcript logs.
pub const KIND_POW: u32 = 3;
pub const KIND_POW_CONT: u32 = 4;

/// Records every observe/sample/commit-limb (commit = DIGEST_SIZE limb events), so the
/// in-circuit transcript index (tidx) of each event equals its position in the log.
#[derive(Clone, Debug, Default)]
pub struct ShaTranscriptRecorder {
    pub inner: ShaTranscript,
    pub values: Vec<F>,
    pub kinds: Vec<u32>,
}
impl ShaTranscriptRecorder {
    pub fn into_log(self) -> ShaTranscriptLog {
        ShaTranscriptLog {
            values: self.values,
            kinds: self.kinds,
        }
    }
}
impl FiatShamirTranscript<Sha384Config> for ShaTranscriptRecorder {
    fn observe(&mut self, v: F) {
        self.inner.observe(v);
        self.values.push(v);
        self.kinds.push(KIND_OBSERVE);
    }
    fn observe_commit(&mut self, d: Digest) {
        self.inner.observe_commit(d);
        self.values.extend(digest_to_limbs(d));
        self.kinds.extend([KIND_COMMIT; DIGEST_SIZE]);
    }
    fn sample(&mut self) -> F {
        let s = self.inner.sample();
        self.values.push(s);
        self.kinds.push(KIND_SAMPLE);
        s
    }
}
impl TranscriptHistory for ShaTranscriptRecorder {
    type F = F;
    type State = ();
    fn len(&self) -> usize {
        self.values.len()
    }
    fn into_log(self) -> openvm_stark_backend::TranscriptLog<F, ()> {
        let samples = self.kinds.iter().map(|&k| k == KIND_SAMPLE).collect();
        openvm_stark_backend::TranscriptLog::new(self.values, samples)
    }
}

#[derive(Clone, Debug, Default)]
pub struct ShaTranscriptLog {
    pub values: Vec<F>,
    pub kinds: Vec<u32>,
}
impl ShaTranscriptLog {
    pub fn len(&self) -> usize {
        self.values.len()
    }
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
    pub fn values(&self) -> &[F] {
        &self.values
    }
    pub fn samples(&self) -> Vec<bool> {
        self.kinds.iter().map(|&k| k == KIND_SAMPLE).collect()
    }
}

/// Replays a recorded log (positions = tidx); used by tracegen to re-derive challenges.
#[derive(Clone, Debug)]
pub struct ShaReadOnlyTranscript<'a> {
    log: &'a ShaTranscriptLog,
    pub position: usize,
}
impl<'a> ShaReadOnlyTranscript<'a> {
    pub fn new(log: &'a ShaTranscriptLog, start: usize) -> Self {
        Self { log, position: start }
    }
}
impl FiatShamirTranscript<Sha384Config> for ShaReadOnlyTranscript<'_> {
    fn observe(&mut self, v: F) {
        debug_assert_eq!(self.log.kinds[self.position], KIND_OBSERVE);
        debug_assert_eq!(self.log.values[self.position], v);
        self.position += 1;
    }
    fn observe_commit(&mut self, d: Digest) {
        debug_assert!(self.log.kinds[self.position..self.position + DIGEST_SIZE]
            .iter()
            .all(|&k| k == KIND_COMMIT));
        debug_assert_eq!(
            &self.log.values[self.position..self.position + DIGEST_SIZE],
            &digest_to_limbs(d)
        );
        self.position += DIGEST_SIZE;
    }
    fn sample(&mut self) -> F {
        debug_assert_eq!(self.log.kinds[self.position], KIND_SAMPLE);
        let v = self.log.values[self.position];
        self.position += 1;
        v
    }
}
impl TranscriptHistory for ShaReadOnlyTranscript<'_> {
    type F = F;
    type State = ();
    fn len(&self) -> usize {
        self.position
    }
    fn into_log(self) -> openvm_stark_backend::TranscriptLog<F, ()> {
        let samples = self.log.samples();
        openvm_stark_backend::TranscriptLog::new(self.log.values.clone(), samples)
    }
}

/// Row-major CPU engine (optimized backend) with the SHA-384/Ext12 config.
pub struct Sha384CpuEngine {
    device: CpuDevice<Sha384Config>,
}
impl Sha384CpuEngine {
    /// Engine of the final recursive layer (U-12: own hash domain).
    pub fn new_final(params: SystemParams) -> Self {
        Self { device: CpuDevice::new(Sha384Config::new_final(params)) }
    }
}
impl StarkEngine for Sha384CpuEngine {
    type SC = Sha384Config;
    type PB = CpuBackend<Sha384Config>;
    type PD = CpuDevice<Sha384Config>;
    type TS = ShaTranscript;
    fn new(params: SystemParams) -> Self {
        Self {
            device: CpuDevice::new(Sha384Config::new(params)),
        }
    }
    fn config(&self) -> &Sha384Config {
        self.device.config()
    }
    fn device(&self) -> &Self::PD {
        &self.device
    }
    fn initial_transcript(&self) -> ShaTranscript {
        ShaTranscript::new_layer(self.device.config().hasher.final_layer)
    }
    fn prover_from_transcript(
        &self,
        t: ShaTranscript,
    ) -> Coordinator<Sha384Config, Self::PB, Self::PD, ShaTranscript> {
        Coordinator::new(CpuBackend::new(), self.device.clone(), t)
    }
}

/// Reference (column-major) engine, as used by the native prover.
pub struct Sha384RefEngine {
    device: ReferenceDevice<Sha384Config>,
}
impl StarkEngine for Sha384RefEngine {
    type SC = Sha384Config;
    type PB = CpuColMajorBackend<Sha384Config>;
    type PD = ReferenceDevice<Sha384Config>;
    type TS = ShaTranscript;
    fn new(params: SystemParams) -> Self {
        Self {
            device: ReferenceDevice::new(Sha384Config::new(params)),
        }
    }
    fn config(&self) -> &Sha384Config {
        self.device.config()
    }
    fn device(&self) -> &Self::PD {
        &self.device
    }
    fn initial_transcript(&self) -> ShaTranscript {
        ShaTranscript::default()
    }
    fn prover_from_transcript(
        &self,
        t: ShaTranscript,
    ) -> Coordinator<Sha384Config, Self::PB, Self::PD, ShaTranscript> {
        Coordinator::new(CpuColMajorBackend::new(), self.device.clone(), t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Recorded native vectors (native-sha384-vectors.log, `transcript_vectors()`).
    const VECTOR_LEAF: [u8; 48] = [
        132, 195, 186, 242, 36, 215, 229, 184, 74, 98, 110, 56, 170, 97, 126, 104, 91, 197, 59,
        194, 137, 145, 72, 49, 20, 252, 168, 183, 154, 5, 107, 155, 191, 94, 44, 52, 255, 182, 4,
        220, 228, 126, 96, 218, 47, 131, 214, 56,
    ];
    const VECTOR_NODE: [u8; 48] = [
        153, 17, 204, 192, 30, 99, 77, 120, 106, 149, 215, 85, 185, 102, 183, 199, 253, 61, 61,
        112, 126, 162, 127, 238, 30, 122, 0, 66, 166, 17, 215, 174, 71, 182, 108, 81, 221, 243,
        108, 124, 249, 143, 249, 130, 166, 114, 249, 232,
    ];
    const VECTOR_STATE: [u8; 48] = [
        106, 63, 165, 178, 94, 213, 241, 68, 47, 36, 181, 153, 40, 230, 130, 152, 103, 69, 70, 148,
        20, 31, 125, 4, 114, 96, 229, 160, 100, 153, 91, 243, 7, 158, 69, 82, 114, 118, 171, 41,
        208, 0, 155, 144, 139, 123, 109, 251,
    ];
    const VECTOR_SAMPLES_HEAD: [u32; 8] = [
        1967261542, 1061900723, 1055807374, 798275237, 1378380172, 17371861, 513262727, 1748498260,
    ];

    #[test]
    fn native_transcript_vectors() {
        if sha_levers().tstar {
            eprintln!("skipped: recorded vectors are the legacy chained squeeze (NEARPROOF_TSTAR=0)");
            return;
        }
        let hasher = ShaHasher;
        let leaf = hasher.hash_slice(&[F::ZERO, F::ONE, F::from_u32(2013265920)]);
        let empty = hasher.hash_slice(&[]);
        let node = hasher.compress(leaf, empty);
        assert_eq!(digest_bytes(leaf), VECTOR_LEAF);
        assert_eq!(digest_bytes(node), VECTOR_NODE);
        let mut t = ShaTranscript::default();
        for n in [123, 124, 0, 2013265920] {
            t.observe(F::from_u32(n));
        }
        t.observe_commit(node);
        let samples: Vec<u32> = (0..96)
            .map(|i| {
                if i >= 32 && (i - 32) % 7 == 0 {
                    t.observe(F::from_u32(i));
                    t.observe(F::from_u32(i + 1));
                }
                t.sample().as_canonical_u32()
            })
            .collect();
        assert_eq!(&samples[..8], &VECTOR_SAMPLES_HEAD);
        assert_eq!(t.state, VECTOR_STATE);
        assert_eq!(t.next_word, 1);
    }

    /// T*-1: counter-mode squeeze from the post-absorb key; the state after a squeeze run is the
    /// last block consumed; a wrong counter gives different challenges.
    #[test]
    fn tstar_counter_mode() {
        if !sha_levers().tstar {
            return;
        }
        let mut t = ShaTranscript::default();
        t.observe(F::from_u32(7));
        t.observe(F::from_u32(9));
        let kappa = hash_parts(TAG_FLUSH, &[&initial_state(), &felt_bytes(&[F::from_u32(7), F::from_u32(9)])]);
        let cand = |b: &[u8; 48], i: usize| u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap());
        let accept = |n: u32| (n as u64) < SAMPLE_BOUND;
        // expected: candidates of B_1, B_2, ... (rejections skipped)
        let mut exp = vec![];
        let mut last = [0u8; 48];
        for j in 1..=3u32 {
            let b = hash_parts(TAG_SQUEEZE, &[&kappa, &j.to_le_bytes()]);
            last = b;
            for i in 0..12 {
                if accept(cand(&b, i)) {
                    exp.push(cand(&b, i) % (BABYBEAR_P as u32));
                }
            }
        }
        let n = exp.len();
        let got: Vec<u32> = (0..n).map(|_| t.sample().as_canonical_u32()).collect();
        assert_eq!(got, exp);
        assert_eq!(t.state, last, "state = last block consumed");
        assert_eq!(t.ctr, 3);
        // wrong counter (j + 1) or the old chain H(5, kappa) gives different challenges
        let wrong = hash_parts(TAG_SQUEEZE, &[&kappa, &2u32.to_le_bytes()]);
        let chain = hash_parts(TAG_SQUEEZE, &[&kappa]);
        let first = hash_parts(TAG_SQUEEZE, &[&kappa, &1u32.to_le_bytes()]);
        assert_ne!(wrong, first);
        assert_ne!(chain, first);
        // the next absorb starts from the last block consumed
        t.observe(F::ONE);
        t.flush();
        assert_eq!(t.state, hash_parts(TAG_FLUSH, &[&last, &felt_bytes(&[F::ONE])]));
    }

    /// T*-2: PoW on the first z bits of B_1 = H(7, sigma || w || le32(1)); a witness ground on the
    /// old chain (H(7, sigma || w)) is rejected; challenges start at B_1's next 64-bit word (never
    /// the PoW bits), then B_2 = H(7, sigma || w || le32(2)); z = 0 needs a zero witness.
    #[test]
    fn tstar_pow() {
        if !sha_levers().tstar {
            return;
        }
        let bits = 12;
        let mut t = ShaTranscript::default();
        t.observe(F::from_u32(5));
        t.flush();
        let sigma = t.state;
        // honest grind (T*) and verification
        let mut g = t.clone();
        let w = FiatShamirTranscript::<Sha384Config>::grind(&mut g, bits);
        let mut v = t.clone();
        assert!(FiatShamirTranscript::<Sha384Config>::check_witness(&mut v, bits, w));
        let wb = w.as_canonical_u32().to_le_bytes().to_vec();
        let b1 = SqueezeSrc::Pow(sigma, wb.clone()).block(1);
        assert!(leading_zero_bits(&b1) >= bits);
        // challenges: B_1 from word pow_skip_words(bits), then B_2
        let cand = |b: &[u8; 48], i: usize| u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap());
        let mut exp = vec![];
        for i in pow_skip_words(bits)..12 {
            if (cand(&b1, i) as u64) < SAMPLE_BOUND {
                exp.push(cand(&b1, i) % (BABYBEAR_P as u32));
            }
        }
        let b2 = SqueezeSrc::Pow(sigma, wb).block(2);
        for i in 0..12 {
            if (cand(&b2, i) as u64) < SAMPLE_BOUND {
                exp.push(cand(&b2, i) % (BABYBEAR_P as u32));
            }
        }
        let got: Vec<u32> = (0..exp.len()).map(|_| v.sample().as_canonical_u32()).collect();
        assert_eq!(got, exp);
        // indices taken from B_1's PoW bits (word 0) would be the zero-heavy candidate: not used
        assert_ne!(got[0], cand(&b1, 0) % (BABYBEAR_P as u32));
        // a witness valid on the old chain but not under T* is rejected
        let old_ok = |x: u32| leading_zero_bits(&hash_parts(TAG_POW, &[&sigma, &x.to_le_bytes()])) >= bits;
        let new_ok = |x: u32| leading_zero_bits(&SqueezeSrc::Pow(sigma, x.to_le_bytes().to_vec()).block(1)) >= bits;
        let old_w = (0u32..).find(|&x| old_ok(x) && !new_ok(x)).unwrap();
        let mut r = t.clone();
        assert!(!FiatShamirTranscript::<Sha384Config>::check_witness(&mut r, bits, F::from_u32(old_w)));
        // G-11: zero bits needs a zero witness
        let mut z = t.clone();
        assert!(FiatShamirTranscript::<Sha384Config>::check_witness(&mut z, 0, F::ZERO));
        assert!(!FiatShamirTranscript::<Sha384Config>::check_witness(&mut z, 0, F::ONE));
        assert!(!FiatShamirTranscript::<Sha384Config>::check_witness_wide(&mut z, 0, [F::ZERO, F::ONE]));
    }

    #[test]
    fn digest_limb_roundtrip() {
        let d: Digest = std::array::from_fn(|i| 0x0123456789abcdefu64.rotate_left(7 * i as u32));
        assert_eq!(limbs_to_digest(&digest_to_limbs(d)), d);
        // H0 is the big-endian reading of the first 8 digest bytes.
        let b = digest_bytes(d);
        assert_eq!(digest_words(d)[0], u64::from_be_bytes(b[..8].try_into().unwrap()));
    }
}

/// Differential test against the native configuration file itself (`native_ref.rs` is a
/// verbatim copy of `airbender/direct-wasm/native_sha384_config.rs`; setup checks it).
#[cfg(test)]
#[allow(dead_code, unused_imports, clippy::all)]
mod native_diff {
    mod native {
        use openvm_stark_backend::{prover::CpuColMajorBackend, StarkEngine, SystemParams};
        use p3_field::PrimeCharacteristicRing;
        include!("native_ref.rs");
        pub type NF = F;
        pub fn leaf(v: &[F]) -> [u8; 48] {
            digest_bytes(ShaHasher.hash_slice(v)).try_into().unwrap()
        }
        pub fn node(l: [u8; 48], r: [u8; 48]) -> [u8; 48] {
            digest_bytes(ShaHasher.compress(words(l), words(r))).try_into().unwrap()
        }
        pub struct T(Transcript);
        impl T {
            pub fn new() -> Self {
                T(Transcript::new())
            }
            pub fn observe(&mut self, v: F) {
                FiatShamirTranscript::<SC>::observe(&mut self.0, v)
            }
            pub fn commit(&mut self, d: [u8; 48]) {
                FiatShamirTranscript::<SC>::observe_commit(&mut self.0, words(d))
            }
            pub fn sample(&mut self) -> F {
                FiatShamirTranscript::<SC>::sample(&mut self.0)
            }
            pub fn state(&self) -> [u8; 48] {
                self.0.state
            }
        }
    }
    use super::*;

    #[test]
    fn native_differential() {
        if sha_levers().tstar {
            eprintln!("skipped: the native reference is the legacy chained squeeze (NEARPROOF_TSTAR=0)");
            return;
        }
        let mut x = 0x9e3779b97f4a7c15u64;
        let mut rnd = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for len in [0usize, 1, 7, 8, 12, 21, 22, 23, 32, 53, 54, 85, 200] {
            let v: Vec<F> = (0..len).map(|_| F::from_u32((rnd() % BABYBEAR_P) as u32)).collect();
            assert_eq!(native::leaf(&v), digest_bytes(ShaHasher.hash_slice(&v)));
        }
        for _ in 0..16 {
            let l: Digest = std::array::from_fn(|_| rnd());
            let r: Digest = std::array::from_fn(|_| rnd());
            assert_eq!(
                native::node(digest_bytes(l), digest_bytes(r)),
                digest_bytes(ShaHasher.compress(l, r))
            );
        }
        let mut a = native::T::new();
        let mut b = ShaTranscript::default();
        for _ in 0..4000 {
            match rnd() % 7 {
                0..=2 => {
                    let v = F::from_u32((rnd() % BABYBEAR_P) as u32);
                    a.observe(v);
                    b.observe(v);
                }
                3 => {
                    let d: Digest = std::array::from_fn(|_| rnd());
                    a.commit(digest_bytes(d));
                    b.observe_commit(d);
                }
                _ => assert_eq!(a.sample(), b.sample()),
            }
        }
        assert_eq!(a.state(), b.state);
    }
}
