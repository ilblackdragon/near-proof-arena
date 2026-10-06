//! Hostile proof generation for `ADVERSARIAL_PROOFS`.
//!
//! A [`ProofMutator`] turns honest `(claim, proof)` pairs into hostile pairs
//! that a sound verifier must reject. This module ships a generic,
//! format-agnostic set; the adversarial lane registers format-aware
//! mutators through [`MutatorRegistry::register`].
//!
//! Any hostile pair byte-identical to an honest pair is discarded by the
//! registry (it would be a valid proof, not a hostile one).

use arena_measure::stats::SplitMix64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HonestPair {
    pub case_id: String,
    pub claim: Vec<u8>,
    pub proof: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostileInput {
    /// `<mutator>/<variant>` plus the source case id when relevant.
    pub label: String,
    pub claim: Vec<u8>,
    pub proof: Vec<u8>,
}

pub struct MutationCtx<'a> {
    pub honest: &'a [HonestPair],
    pub max_proof_bytes: u64,
}

pub trait ProofMutator: Send + Sync {
    fn name(&self) -> &str;
    fn mutate(&self, ctx: &MutationCtx<'_>, rng: &mut SplitMix64) -> Vec<HostileInput>;
}

fn h(label: String, claim: &[u8], proof: Vec<u8>) -> HostileInput {
    HostileInput {
        label,
        claim: claim.to_vec(),
        proof,
    }
}

/// Proof truncated to `len-1`, `len/2`, and 1 byte.
pub struct Truncate;
impl ProofMutator for Truncate {
    fn name(&self) -> &str {
        "truncate"
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, _: &mut SplitMix64) -> Vec<HostileInput> {
        let mut out = vec![];
        for p in ctx.honest {
            let n = p.proof.len();
            let mut lens = vec![n.saturating_sub(1), n / 2, 1];
            lens.retain(|&l| l > 0 && l < n);
            lens.dedup();
            for l in lens {
                out.push(h(
                    format!("truncate/{l}of{n}/{}", p.case_id),
                    &p.claim,
                    p.proof[..l].to_vec(),
                ));
            }
        }
        out
    }
}

/// Single-bit flips at the first byte, last byte, and 3 random positions.
pub struct BitFlip;
impl ProofMutator for BitFlip {
    fn name(&self) -> &str {
        "bitflip"
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, rng: &mut SplitMix64) -> Vec<HostileInput> {
        let mut out = vec![];
        for p in ctx.honest {
            let n = p.proof.len() as u64;
            if n == 0 {
                continue;
            }
            let mut positions = vec![0, n - 1];
            for _ in 0..3 {
                positions.push(rng.below(n));
            }
            positions.sort_unstable();
            positions.dedup();
            for pos in positions {
                let bit = rng.below(8) as u8;
                let mut q = p.proof.clone();
                q[pos as usize] ^= 1 << bit;
                out.push(h(format!("bitflip/{pos}.{bit}/{}", p.case_id), &p.claim, q));
            }
        }
        out
    }
}

/// Empty proof.
pub struct Empty;
impl ProofMutator for Empty {
    fn name(&self) -> &str {
        "empty"
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, _: &mut SplitMix64) -> Vec<HostileInput> {
        ctx.honest
            .iter()
            .take(1)
            .map(|p| h(format!("empty/{}", p.case_id), &p.claim, vec![]))
            .collect()
    }
}

/// A proof of `max_proof_bytes + 1` bytes: the honest proof repeated, then
/// random padding. Skipped when the cap exceeds 256 MiB.
pub struct Oversize;
impl ProofMutator for Oversize {
    fn name(&self) -> &str {
        "oversize"
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, rng: &mut SplitMix64) -> Vec<HostileInput> {
        let Some(p) = ctx.honest.first() else {
            return vec![];
        };
        if ctx.max_proof_bytes >= 256 << 20 {
            return vec![];
        }
        let n = ctx.max_proof_bytes as usize + 1;
        let mut q = Vec::with_capacity(n);
        while q.len() + p.proof.len() <= n && !p.proof.is_empty() {
            q.extend_from_slice(&p.proof);
        }
        while q.len() < n {
            q.push(rng.next_u64() as u8);
        }
        vec![h(format!("oversize/{n}/{}", p.case_id), &p.claim, q)]
    }
}

/// Claim of case `i` with the proof of case `j` (claims differ).
pub struct SwapClaimProof;
impl ProofMutator for SwapClaimProof {
    fn name(&self) -> &str {
        "swap"
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, _: &mut SplitMix64) -> Vec<HostileInput> {
        let hs = ctx.honest;
        let mut out = vec![];
        for i in 0..hs.len() {
            // Pair with the next case whose claim differs (cyclic).
            if let Some(j) = (1..hs.len())
                .map(|d| (i + d) % hs.len())
                .find(|&j| hs[j].claim != hs[i].claim)
            {
                out.push(h(
                    format!("swap/{}<-{}", hs[i].case_id, hs[j].case_id),
                    &hs[i].claim,
                    hs[j].proof.clone(),
                ));
            }
        }
        out
    }
}

/// Honest proof with trailing garbage (1 zero byte; 32 random bytes).
pub struct AppendGarbage;
impl ProofMutator for AppendGarbage {
    fn name(&self) -> &str {
        "append"
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, rng: &mut SplitMix64) -> Vec<HostileInput> {
        let mut out = vec![];
        for p in ctx.honest {
            let mut a = p.proof.clone();
            a.push(0);
            out.push(h(format!("append/zero/{}", p.case_id), &p.claim, a));
            let mut b = p.proof.clone();
            b.extend((0..32).map(|_| rng.next_u64() as u8));
            out.push(h(format!("append/random32/{}", p.case_id), &p.claim, b));
        }
        out
    }
}

/// Structure-aware mutations of the bytes nearcore's chunk validator never
/// reads (v3, `near-arena-witness-v3` proofs). When an honest proof *is* a
/// witness file, flip one bit of the chunk header's `height_included`, of its
/// signature, and of every `ChunkStateTransition.block_hash`. A verifier that
/// accepts any of them accepts two different proof byte strings for one proof
/// slot (malleability): deterministic `HOSTILE_PROOF_ACCEPTED`, not left to
/// the random `bitflip` positions. Proofs in any other format produce nothing.
pub struct V3IgnoredFields;

/// Offsets (in the witness *file*) of the validator-ignored fields of a
/// `near-arena-witness-v3` proof, or `None` if the bytes are not one in the
/// D0 layout this walker knows (`NearSpecV3.decodeStateWitness`).
pub fn v3_ignored_offsets(file: &[u8]) -> Option<Vec<(String, usize)>> {
    struct R<'a> {
        b: &'a [u8],
        p: usize,
    }
    impl<'a> R<'a> {
        fn take(&mut self, n: usize) -> Option<&'a [u8]> {
            let s = self.b.get(self.p..self.p.checked_add(n)?)?;
            self.p += n;
            Some(s)
        }
        fn u8(&mut self) -> Option<u8> {
            Some(self.take(1)?[0])
        }
        fn u32(&mut self) -> Option<u32> {
            Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
        }
        fn bytes(&mut self) -> Option<&'a [u8]> {
            let n = self.u32()? as usize;
            self.take(n)
        }
        fn pk(&mut self) -> Option<()> {
            let n = match self.u8()? { 0 => 32, 1 => 64, 2 => 1952, _ => return None };
            self.take(n).map(|_| ())
        }
        fn transition(&mut self) -> Option<usize> {
            let at = self.p;
            self.take(32)?;
            (self.u8()? == 0).then_some(())?;
            for _ in 0..self.u32()? {
                self.bytes()?;
            }
            self.take(32)?;
            Some(at)
        }
    }
    let tag = b"near-arena-witness-v3";
    let mut f = R { b: file, p: 0 };
    (f.bytes()? == tag).then_some(())?;
    let n = f.u32()? as usize;
    let base = f.p;
    let sw = f.take(n)?;
    let mut r = R { b: sw, p: 0 };
    (r.u8()? == 1).then_some(())?;
    r.take(32)?;
    (r.u8()? == 2).then_some(())?;
    let itag = r.u8()?;
    (itag == 3 || itag == 4).then_some(())?;
    r.take(4 * 32 + 5 * 8 + 16 + 2 * 32)?;
    for _ in 0..r.u32()? {
        (r.u8()? == 0).then_some(())?;
        r.bytes()?;
        r.pk()?;
        r.take(16)?;
    }
    (r.u8()? == 0).then_some(())?;
    r.take(42)?;
    (r.u8()? == 0).then_some(())?;
    for _ in 0..r.u32()? {
        r.take(7)?;
    }
    if itag == 4 {
        match r.u8()? {
            0 => {}
            1 => {
                r.bytes()?;
                r.take(16)?;
            }
            _ => return None,
        }
    }
    let mut out = vec![("height_included".to_string(), base + r.p)];
    r.take(8)?;
    let sig_tag = r.u8()?;
    out.push(("signature".to_string(), base + r.p));
    r.take(match sig_tag { 0 => 64, 1 => 65, 2 => 3309, _ => return None })?;
    out.push(("block_hash.main".to_string(), base + r.transition()?));
    for _ in 0..r.u32()? {
        r.take(32)?;
        for _ in 0..r.u32()? {
            r.bytes()?;
            r.bytes()?;
            r.take(32)?;
            (r.u8()? == 0).then_some(())?;
            r.bytes()?;
            r.pk()?;
            r.take(16)?;
            (r.u32()? == 0 && r.u32()? == 0 && r.u32()? == 1 && r.u8()? == 3).then_some(())?;
            r.take(16)?;
        }
        r.take(16)?;
        for _ in 0..r.u32()? {
            r.take(33)?;
        }
    }
    r.take(32)?;
    (r.u32()? == 0).then_some(())?;
    for i in 0..r.u32()? {
        out.push((format!("block_hash.implicit{i}"), base + r.transition()?));
    }
    Some(out)
}

impl ProofMutator for V3IgnoredFields {
    fn name(&self) -> &str {
        "v3-ignored-fields"
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, _: &mut SplitMix64) -> Vec<HostileInput> {
        let mut out = vec![];
        for p in ctx.honest {
            let Some(offs) = v3_ignored_offsets(&p.proof) else {
                continue;
            };
            for (field, at) in offs {
                let mut q = p.proof.clone();
                q[at] ^= 1;
                out.push(h(format!("v3-ignored-fields/{field}/{}", p.case_id), &p.claim, q));
            }
        }
        out
    }
}

/// Adapter for a structure-aware mutator from the adversarial lane
/// (`adversarial/proof-mutators`). Registered under `adv:<name>`. Each honest
/// pair is mutated with the next pair (cyclically) as the foreign
/// claim/proof for binding and substitution mutants.
pub struct LaneMutator {
    name: String,
    /// Index into `proof_mutators::registry()` (its boxes are not `Send`,
    /// so the mutator is re-instantiated per use; they are stateless).
    index: usize,
}

impl ProofMutator for LaneMutator {
    fn name(&self) -> &str {
        &self.name
    }
    fn mutate(&self, ctx: &MutationCtx<'_>, rng: &mut SplitMix64) -> Vec<HostileInput> {
        let hs = ctx.honest;
        let mut out = vec![];
        for (i, p) in hs.iter().enumerate() {
            let foreign = (hs.len() > 1).then(|| &hs[(i + 1) % hs.len()]);
            let mctx = proof_mutators::MutationCtx {
                hints: proof_mutators::FormatHints::default(),
                foreign_claim: foreign.map(|f| f.claim.as_slice()),
                foreign_proof: foreign.map(|f| f.proof.as_slice()),
                claimed_formal_digest: None,
            };
            let mut lane_rng = proof_mutators::Rng::new(rng.next_u64());
            let inner = proof_mutators::registry().swap_remove(self.index);
            for m in inner.mutate(&p.proof, &p.claim, &mctx, &mut lane_rng) {
                if m.bytes.len() as u64 > ctx.max_proof_bytes.saturating_mul(4).max(1 << 20) {
                    continue;
                }
                out.push(HostileInput {
                    label: format!("{}/{:?}:{}/{}", self.name, m.kill, m.label, p.case_id),
                    claim: m.claim_override.unwrap_or_else(|| p.claim.clone()),
                    proof: m.bytes,
                });
            }
        }
        out
    }
}

pub struct MutatorRegistry {
    mutators: Vec<Box<dyn ProofMutator>>,
}

impl Default for MutatorRegistry {
    fn default() -> Self {
        Self::generic()
    }
}

impl MutatorRegistry {
    pub fn empty() -> Self {
        MutatorRegistry { mutators: vec![] }
    }
    /// truncate, bitflip, empty, oversize, swap, append, v3-ignored-fields.
    pub fn generic() -> Self {
        MutatorRegistry {
            mutators: vec![
                Box::new(Truncate),
                Box::new(BitFlip),
                Box::new(Empty),
                Box::new(Oversize),
                Box::new(SwapClaimProof),
                Box::new(AppendGarbage),
                Box::new(V3IgnoredFields),
            ],
        }
    }
    /// The generic set plus every mutator shipped by the adversarial lane
    /// (as `adv:<name>`).
    pub fn with_adversarial_lane() -> Self {
        let mut r = Self::generic();
        for (index, m) in proof_mutators::registry().iter().enumerate() {
            r.register(Box::new(LaneMutator {
                name: format!("adv:{}", m.name()),
                index,
            }));
        }
        r
    }

    pub fn register(&mut self, m: Box<dyn ProofMutator>) {
        self.mutators.push(m);
    }
    pub fn names(&self) -> Vec<String> {
        self.mutators.iter().map(|m| m.name().to_string()).collect()
    }

    /// Run the selected mutators (all if `select` is empty) with one seeded
    /// RNG stream in registry order. Unknown names are an error.
    pub fn generate(
        &self,
        select: &[String],
        ctx: &MutationCtx<'_>,
        seed: u64,
    ) -> Result<Vec<HostileInput>, String> {
        for s in select {
            if !self.mutators.iter().any(|m| m.name() == s) {
                return Err(format!("unknown mutator {s:?}"));
            }
        }
        let mut rng = SplitMix64::new(seed);
        let mut out = vec![];
        for m in &self.mutators {
            if !select.is_empty() && !select.iter().any(|s| s == m.name()) {
                continue;
            }
            for x in m.mutate(ctx, &mut rng) {
                let is_honest = ctx
                    .honest
                    .iter()
                    .any(|p| p.claim == x.claim && p.proof == x.proof);
                if !is_honest {
                    out.push(x);
                }
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn pairs() -> Vec<HonestPair> {
        vec![
            HonestPair {
                case_id: "a".into(),
                claim: b"ca".to_vec(),
                proof: b"proof-a".to_vec(),
            },
            HonestPair {
                case_id: "b".into(),
                claim: b"cb".to_vec(),
                proof: b"proof-b".to_vec(),
            },
        ]
    }
    #[test]
    fn generic_set_is_hostile_and_deterministic() {
        let hp = pairs();
        let ctx = MutationCtx {
            honest: &hp,
            max_proof_bytes: 100,
        };
        let r = MutatorRegistry::generic();
        let a = r.generate(&[], &ctx, 9).unwrap();
        let b = r.generate(&[], &ctx, 9).unwrap();
        assert_eq!(a, b);
        assert!(a
            .iter()
            .all(|x| !hp.iter().any(|p| p.claim == x.claim && p.proof == x.proof)));
        for name in ["truncate", "bitflip", "empty", "oversize", "swap", "append"] {
            assert!(a.iter().any(|x| x.label.starts_with(name)), "{name}");
        }
        assert!(a.iter().any(|x| x.proof.len() == 101));
        assert!(a.iter().any(|x| x.claim == b"ca" && x.proof == b"proof-b"));
        assert!(r.generate(&["nope".into()], &ctx, 1).is_err());
        let only = r.generate(&["empty".into()], &ctx, 1).unwrap();
        assert_eq!(only.len(), 1);
    }
    #[test]
    fn adversarial_lane_mutators_plug_in() {
        let hp = pairs();
        let r = MutatorRegistry::with_adversarial_lane();
        assert!(r.names().iter().any(|n| n.starts_with("adv:")));
        let ctx = MutationCtx {
            honest: &hp,
            max_proof_bytes: 100,
        };
        let a = r.generate(&[], &ctx, 5).unwrap();
        assert_eq!(a, r.generate(&[], &ctx, 5).unwrap());
        assert!(a.iter().any(|x| x.label.starts_with("adv:")));
        assert!(a
            .iter()
            .all(|x| !hp.iter().any(|p| p.claim == x.claim && p.proof == x.proof)));
    }

    #[test]
    fn custom_mutator_registers() {
        struct Zero;
        impl ProofMutator for Zero {
            fn name(&self) -> &str {
                "zero"
            }
            fn mutate(&self, ctx: &MutationCtx<'_>, _: &mut SplitMix64) -> Vec<HostileInput> {
                ctx.honest
                    .iter()
                    .map(|p| HostileInput {
                        label: "zero".into(),
                        claim: p.claim.clone(),
                        proof: vec![0; p.proof.len()],
                    })
                    .collect()
            }
        }
        let mut r = MutatorRegistry::empty();
        r.register(Box::new(Zero));
        let hp = pairs();
        assert_eq!(
            r.generate(
                &[],
                &MutationCtx {
                    honest: &hp,
                    max_proof_bytes: 10
                },
                0
            )
            .unwrap()
            .len(),
            2
        );
    }

    /// The v3 structure-aware mutator hits exactly the validator-ignored
    /// fields of a real witness (offsets from the exhaustive bit-flip map of
    /// `00-h10004-s3`: height_included at 365, signature body at 374, main
    /// transition block_hash at 438) and nothing for other formats.
    #[test]
    fn v3_ignored_fields_targets_the_validator_ignored_bytes() {
        let w = std::fs::read(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../oracle/fixtures/v3/arena-public/cases/00-h10004-s3/witness.bin"),
        )
        .unwrap();
        let offs = v3_ignored_offsets(&w).unwrap();
        let get = |f: &str| offs.iter().find(|(n, _)| n == f).unwrap().1;
        assert_eq!(get("height_included"), 365);
        assert_eq!(get("signature"), 374);
        assert_eq!(get("block_hash.main"), 438);
        let hp = vec![HonestPair { case_id: "c".into(), claim: b"claim".to_vec(), proof: w.clone() }];
        let ctx = MutationCtx { honest: &hp, max_proof_bytes: 1 << 26 };
        let m = V3IgnoredFields.mutate(&ctx, &mut SplitMix64::new(1));
        assert_eq!(m.len(), offs.len());
        assert!(m.iter().all(|x| x.proof.len() == w.len() && x.proof != w));
        // a witness with an implicit transition gets one more mutant
        let w2 = std::fs::read(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../oracle/fixtures/v3/arena-public/cases/00-h10024-s0/witness.bin"),
        )
        .unwrap();
        assert!(v3_ignored_offsets(&w2).unwrap().iter().any(|(n, _)| n == "block_hash.implicit0"));
        assert!(v3_ignored_offsets(b"proof-a").is_none());
    }
}
