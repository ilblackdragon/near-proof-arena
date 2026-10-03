//! The hostile mutator registry.
//!
//! Each mutator targets a specific attack family. Mutators are pure functions
//! of `(honest, claim, ctx, rng)` and are deterministic given a seed. They
//! classify every mutant ([`crate::KillKind`]) and attach explain-evidence.

use crate::hints::FormatHints;
use crate::{KillKind, MutatedProof, MutationCtx, Mutator, Rng};

/// All hostile mutators, in a stable order.
pub fn all() -> Vec<Box<dyn Mutator>> {
    vec![
        Box::new(Empty),
        Box::new(Truncate),
        Box::new(ExtendTrailing),
        Box::new(BitFlip),
        Box::new(MalformedLength),
        Box::new(NoncanonicalEncoding),
        Box::new(AlteredCommitment),
        Box::new(TruncatedMerklePath),
        Box::new(SwappedSiblings),
        Box::new(DuplicatedNode),
        Box::new(NodeTypeConfusion),
        Box::new(TranscriptTamper),
        Box::new(DomainSeparation),
        Box::new(MismatchedContext),
        Box::new(RecursiveSubstitution),
    ]
}

// ---- helpers ---------------------------------------------------------------

fn write_len(buf: &mut [u8], offset: usize, width: usize, value: u64) {
    let bytes = value.to_le_bytes();
    for k in 0..width {
        if offset + k < buf.len() {
            buf[offset + k] = bytes[k];
        }
    }
}

// ---- generic / packaging ---------------------------------------------------

/// Empty proof. A verifier that accepts an empty proof trivially accepts
/// everything (degenerate always-accept). Packaging/soundness boundary.
struct Empty;
impl Mutator for Empty {
    fn name(&self) -> &str {
        "empty"
    }
    fn describe(&self) -> &str {
        "zero-length proof"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        _ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        if honest.is_empty() {
            return vec![];
        }
        vec![MutatedProof::new(
            self.name(),
            "zero-bytes",
            KillKind::Packaging,
            vec![],
            "An empty proof carries no argument; accepting it means the verifier \
             does not read the proof at all (degenerate always-accept).",
        )]
    }
}

/// Truncated proof at several cut points. Catches verifiers that read a prefix
/// and ignore the tail, or that index past end without bounds checks.
struct Truncate;
impl Mutator for Truncate {
    fn name(&self) -> &str {
        "truncate"
    }
    fn describe(&self) -> &str {
        "proof cut short at several points"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        _ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let n = honest.len();
        if n < 2 {
            return vec![];
        }
        [n / 2, n - 1, 1, n.saturating_sub(32)]
            .into_iter()
            .filter(|&k| k > 0 && k < n)
            .map(|k| {
                MutatedProof::new(
                    self.name(),
                    format!("keep-{k}"),
                    KillKind::Packaging,
                    honest[..k].to_vec(),
                    format!(
                        "First {k} of {n} bytes only: a truncated proof is malformed; \
                         accepting it means the verifier does not require the whole argument."
                    ),
                )
            })
            .collect()
    }
}

/// Append trailing garbage. A length-robust format must reject unexpected
/// trailing bytes (noncanonical / ambiguous encoding).
struct ExtendTrailing;
impl Mutator for ExtendTrailing {
    fn name(&self) -> &str {
        "extend-trailing"
    }
    fn describe(&self) -> &str {
        "honest proof followed by extra bytes"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        _ctx: &MutationCtx,
        r: &mut Rng,
    ) -> Vec<MutatedProof> {
        if honest.is_empty() {
            return vec![];
        }
        let mut bytes = honest.to_vec();
        bytes.extend((0..16).map(|_| r.byte()));
        vec![MutatedProof::new(
            self.name(),
            "plus-16",
            KillKind::Packaging,
            bytes,
            "Honest proof plus 16 trailing bytes: a canonical format rejects \
             trailing data; accepting it admits a malleable, ambiguous encoding.",
        )]
    }
}

/// Single-bit and single-byte flips at a spread of positions. Pure fuzz: any
/// accepted flip is a soundness red flag. Classified Semantic because an
/// accepted non-identity proof means the verifier is not checking contents.
struct BitFlip;
impl Mutator for BitFlip {
    fn name(&self) -> &str {
        "bitflip"
    }
    fn describe(&self) -> &str {
        "single bit/byte flips across the proof"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        _ctx: &MutationCtx,
        r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let n = honest.len();
        if n == 0 {
            return vec![];
        }
        let mut out = Vec::new();
        let positions = [0usize, n / 3, (2 * n) / 3, n - 1];
        for (i, &p) in positions.iter().enumerate() {
            let mut b = honest.to_vec();
            b[p] ^= 1 << (r.below(8));
            out.push(MutatedProof::new(
                self.name(),
                format!("bit@{p}#{i}"),
                KillKind::Semantic,
                b,
                format!(
                    "One bit flipped at byte {p}: the proof no longer matches its own \
                     commitments; a sound verifier rejects it."
                ),
            ));
        }
        // one whole-byte random replacement
        let p = r.below(n);
        let mut b = honest.to_vec();
        b[p] = b[p].wrapping_add(r.flip_delta());
        out.push(MutatedProof::new(
            self.name(),
            format!("byte@{p}"),
            KillKind::Semantic,
            b,
            format!("Byte {p} altered: corrupts the argument; must not verify."),
        ));
        out
    }
}

/// Corrupt embedded length prefixes: set them huge, zero, or off-by-one.
struct MalformedLength;
impl Mutator for MalformedLength {
    fn name(&self) -> &str {
        "malformed-length"
    }
    fn describe(&self) -> &str {
        "embedded length prefixes set huge / zero / off-by-one"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let hints = ctx.hints.effective(honest);
        let mut out = Vec::new();
        for lf in hints.lengths.iter().take(6) {
            for (tag, val) in [
                ("huge", u64::MAX),
                ("zero", 0),
                ("plus1", {
                    // read current then +1
                    let mut v = 0u64;
                    for k in 0..lf.width {
                        if lf.offset + k < honest.len() {
                            v |= (honest[lf.offset + k] as u64) << (8 * k);
                        }
                    }
                    v.wrapping_add(1)
                }),
            ] {
                let mut b = honest.to_vec();
                write_len(&mut b, lf.offset, lf.width, val);
                out.push(MutatedProof::new(
                    self.name(),
                    format!("{}-{tag}", lf.label),
                    KillKind::Packaging,
                    b,
                    format!(
                        "Length field '{}' (offset {}, {}B) set to {tag}: a parser must \
                         bound-check it and reject rather than over-read or trust it.",
                        lf.label, lf.offset, lf.width
                    ),
                ));
            }
        }
        out
    }
}

/// Noncanonical encodings: leading-zero padding of a length, alternate but
/// equal-value byte patterns. A canonical format must reject these even though
/// a naive parser would accept them as the same value.
struct NoncanonicalEncoding;
impl Mutator for NoncanonicalEncoding {
    fn name(&self) -> &str {
        "noncanonical"
    }
    fn describe(&self) -> &str {
        "value-preserving re-encodings that a canonical format must reject"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let hints = ctx.hints.effective(honest);
        let mut out = Vec::new();
        // Widen a u32 length field's high byte with a redundant representation
        // by also appending a byte — ambiguous framing.
        if let Some(lf) = hints.lengths.first() {
            let mut b = honest.to_vec();
            // flip high-order unused bits of the length to a noncanonical but
            // numerically-larger-in-padding form is not possible for fixed LE,
            // so emulate "overlong" by inserting a redundant zero word.
            if lf.offset + lf.width <= b.len() {
                let mut nb = b.clone();
                nb.splice(lf.offset + lf.width..lf.offset + lf.width, [0, 0, 0, 0]);
                out.push(MutatedProof::new(
                    self.name(),
                    "redundant-zero-word",
                    KillKind::Packaging,
                    nb,
                    "A redundant zero word inserted after a length prefix: a canonical \
                     (RFC-8785-style / fixed-width) encoding has one byte string per value; \
                     a verifier accepting this admits encoding malleability.",
                ));
            }
            let _ = &mut b;
        }
        if out.is_empty() && honest.len() >= 32 {
            // Fallback: reorder two 32-byte words — a multiset-preserving but
            // order-changing re-encoding.
            let mut b = honest.to_vec();
            let (a, c) = (0usize, 32usize);
            if c + 32 <= b.len() {
                for k in 0..32 {
                    b.swap(a + k, c + k);
                }
                out.push(MutatedProof::new(
                    self.name(),
                    "word-reorder",
                    KillKind::Packaging,
                    b,
                    "First two 32-byte words swapped: order-sensitive formats must reject; \
                     if accepted the encoding is ambiguous.",
                ));
            }
        }
        out
    }
}

/// Flip bits inside embedded commitments (state roots, Merkle roots, hashes).
/// An accepted mutant means the verifier does not actually bind the proof to
/// the committed root — a genuine soundness break.
struct AlteredCommitment;
impl Mutator for AlteredCommitment {
    fn name(&self) -> &str {
        "altered-commitment"
    }
    fn describe(&self) -> &str {
        "bit flips inside embedded roots/hashes"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let hints = ctx.hints.effective(honest);
        let mut out = Vec::new();
        for region in hints.commitments.iter().take(8) {
            if region.offset + region.len > honest.len() || region.len == 0 {
                continue;
            }
            let mut b = honest.to_vec();
            let p = region.offset + r.below(region.len);
            b[p] ^= r.flip_delta();
            out.push(MutatedProof::new(
                self.name(),
                format!("flip-{}", region.label),
                KillKind::Semantic,
                b,
                format!(
                    "A byte flipped inside commitment '{}' (offset {}): the proof now claims a \
                     different root/hash than it argues for; a sound verifier rejects.",
                    region.label, region.offset
                ),
            ));
        }
        out
    }
}

// ---- NEAR trie witness structure ------------------------------------------

/// Drop the last trie-witness node(s): a truncated Merkle/trie path cannot
/// reconstruct the root. Semantic kill.
struct TruncatedMerklePath;
impl Mutator for TruncatedMerklePath {
    fn name(&self) -> &str {
        "truncated-merkle-path"
    }
    fn describe(&self) -> &str {
        "drop trailing trie-witness nodes so the path no longer reaches the root"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let nodes = &ctx.hints.trie_nodes;
        if nodes.len() < 2 {
            return vec![];
        }
        let drop_from = nodes[nodes.len() - 1].offset;
        vec![MutatedProof::new(
            self.name(),
            "drop-last",
            KillKind::Semantic,
            honest[..drop_from.min(honest.len())].to_vec(),
            "Last trie-witness node removed: the root→leaf path is incomplete, so the \
             committed state root cannot be recomputed; a sound verifier rejects.",
        )]
    }
}

/// Swap two sibling nodes in the witness. Sibling order is fixed by the trie's
/// child index; swapping yields a different (wrong) parent hash.
struct SwappedSiblings;
impl Mutator for SwappedSiblings {
    fn name(&self) -> &str {
        "swapped-siblings"
    }
    fn describe(&self) -> &str {
        "swap two sibling trie-witness nodes"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let nodes = &ctx.hints.trie_nodes;
        if nodes.len() < 2 {
            return vec![];
        }
        let (a, b) = (&nodes[0], &nodes[1]);
        let (first, second) = if a.offset <= b.offset { (a, b) } else { (b, a) };
        // Hints are untrusted input: overlapping (e.g. nested parent/child)
        // regions cannot be swapped.
        if first.offset + first.len > honest.len()
            || second.offset + second.len > honest.len()
            || first.offset + first.len > second.offset
        {
            return vec![];
        }
        let mut out = honest[..first.offset].to_vec();
        out.extend_from_slice(&honest[second.offset..second.offset + second.len]);
        out.extend_from_slice(&honest[first.offset + first.len..second.offset]);
        out.extend_from_slice(&honest[first.offset..first.offset + first.len]);
        out.extend_from_slice(&honest[second.offset + second.len..]);
        vec![MutatedProof::new(
            self.name(),
            "swap-0-1",
            KillKind::Semantic,
            out,
            "Two sibling witness nodes transposed: child order in a NEAR branch node is \
             fixed by nibble index, so the parent hash changes and the root no longer \
             verifies.",
        )]
    }
}

/// Duplicate a witness node. A duplicated node either breaks ordering or
/// supplies a node the real path never references.
struct DuplicatedNode;
impl Mutator for DuplicatedNode {
    fn name(&self) -> &str {
        "duplicated-node"
    }
    fn describe(&self) -> &str {
        "duplicate a trie-witness node"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let nodes = &ctx.hints.trie_nodes;
        let Some(first) = nodes.first() else {
            return vec![];
        };
        if first.offset + first.len > honest.len() || first.len == 0 {
            return vec![];
        }
        let mut b = honest.to_vec();
        let dup = honest[first.offset..first.offset + first.len].to_vec();
        b.splice(first.offset..first.offset, dup);
        vec![MutatedProof::new(
            self.name(),
            "dup-0",
            KillKind::Semantic,
            b,
            "A witness node duplicated: the witness is a set of nodes keyed by hash; a \
             duplicate is either rejected as malformed or ignored, and either way must \
             not let a wrong state verify.",
        )]
    }
}

/// Extension/branch node-type confusion: flip the leading node-type byte of a
/// witness node (`0x00` Leaf / `0x01` BranchNoValue / `0x02` BranchWithValue /
/// `0x03` Extension, per first-slice §3.4). The node then hashes differently
/// and mis-parses.
struct NodeTypeConfusion;
impl Mutator for NodeTypeConfusion {
    fn name(&self) -> &str {
        "node-type-confusion"
    }
    fn describe(&self) -> &str {
        "flip a NEAR trie node's type tag (leaf/extension/branch)"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let nodes = &ctx.hints.trie_nodes;
        let mut out = Vec::new();
        for (i, node) in nodes.iter().enumerate().take(4) {
            if node.offset >= honest.len() {
                continue;
            }
            let orig = honest[node.offset];
            // cycle 0<->3 (leaf<->extension) and 1<->2 (branch variants)
            let swapped = match orig {
                0x00 => 0x03,
                0x03 => 0x00,
                0x01 => 0x02,
                0x02 => 0x01,
                other => other ^ 0x01,
            };
            if swapped == orig {
                continue;
            }
            let mut b = honest.to_vec();
            b[node.offset] = swapped;
            out.push(MutatedProof::new(
                self.name(),
                format!("node-{i}-tag-{orig:#04x}->{swapped:#04x}"),
                KillKind::Semantic,
                b,
                format!(
                    "Trie node {i}'s type tag changed {orig:#04x}->{swapped:#04x}: the node body \
                     is parsed under the wrong variant and its hash changes, so the committed \
                     root cannot be reproduced."
                ),
            ));
        }
        out
    }
}

// ---- transcript / domain separation ---------------------------------------

/// Tamper with a Fiat-Shamir transcript / challenge region. A sound verifier
/// recomputes the challenge from the transcript, so an altered challenge is
/// rejected.
struct TranscriptTamper;
impl Mutator for TranscriptTamper {
    fn name(&self) -> &str {
        "transcript-tamper"
    }
    fn describe(&self) -> &str {
        "alter a transcript / Fiat-Shamir challenge region"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let mut out = Vec::new();
        for (i, region) in ctx.hints.transcript.iter().enumerate().take(4) {
            if region.offset + region.len > honest.len() || region.len == 0 {
                continue;
            }
            let mut b = honest.to_vec();
            let p = region.offset + r.below(region.len);
            b[p] ^= r.flip_delta();
            out.push(MutatedProof::new(
                self.name(),
                format!("transcript-{i}"),
                KillKind::Semantic,
                b,
                "A transcript/challenge byte altered: a Fiat-Shamir verifier recomputes the \
                 challenge from the transcript, so a mismatching challenge is rejected; \
                 acceptance would enable challenge grinding.",
            ));
        }
        out
    }
}

/// Domain-separation attack: overwrite or strip the domain tag so a proof made
/// under one context is replayed under another. Binding kill.
struct DomainSeparation;
impl Mutator for DomainSeparation {
    fn name(&self) -> &str {
        "domain-separation"
    }
    fn describe(&self) -> &str {
        "corrupt the domain-separation tag to force cross-context replay"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let Some(tag) = &ctx.hints.domain_tag else {
            return vec![];
        };
        if tag.offset + tag.len > honest.len() || tag.len == 0 {
            return vec![];
        }
        let mut b = honest.to_vec();
        for k in 0..tag.len {
            b[tag.offset + k] = r.byte();
        }
        vec![MutatedProof::new(
            self.name(),
            "clobber-tag",
            KillKind::Binding,
            b,
            "Domain-separation tag overwritten: if the verifier does not bind the proof to \
             the exact context/challenge, a proof from another domain could be replayed here.",
        )]
    }
}

// ---- binding / foreign artifacts ------------------------------------------

/// Mismatched context: keep the honest proof but drive verification with a
/// foreign claim (a claim for a *different* transition). The judge also
/// independently recomputes the expected claim, so this must fail with either
/// a verifier reject or `CLAIM_MISMATCH`.
struct MismatchedContext;
impl Mutator for MismatchedContext {
    fn name(&self) -> &str {
        "mismatched-context"
    }
    fn describe(&self) -> &str {
        "honest proof paired with a foreign claim (wrong public inputs)"
    }
    fn mutate(
        &self,
        honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let Some(other) = ctx.foreign_claim else {
            return vec![];
        };
        vec![MutatedProof::new(
            self.name(),
            "foreign-claim",
            KillKind::Binding,
            honest.to_vec(),
            "Honest proof presented against a different claim: a proof of transition A must \
             not verify for claim B. The judge also recomputes the expected claim from the \
             request, so a valid proof of the wrong transition fails (CLAIM_MISMATCH).",
        )
        .with_claim(other.to_vec())]
    }
}

/// Recursive proof substitution: a complete honest proof from a *different*
/// challenge case, offered against this case's claim. Binding kill.
struct RecursiveSubstitution;
impl Mutator for RecursiveSubstitution {
    fn name(&self) -> &str {
        "recursive-substitution"
    }
    fn describe(&self) -> &str {
        "a valid proof from another challenge, offered for this claim"
    }
    fn mutate(
        &self,
        _honest: &[u8],
        _c: &[u8],
        ctx: &MutationCtx,
        _r: &mut Rng,
    ) -> Vec<MutatedProof> {
        let Some(other) = ctx.foreign_proof else {
            return vec![];
        };
        vec![MutatedProof::new(
            self.name(),
            "foreign-proof",
            KillKind::Binding,
            other.to_vec(),
            "A genuine proof from another challenge/case substituted here: it is internally \
             valid but bound to different public inputs, so it must not verify against this \
             claim.",
        )]
    }
}

/// Convenience: expose the inferred/explicit hints a mutator would use, for
/// tests and the dump binary.
pub fn effective_hints(proof: &[u8], hints: &FormatHints) -> FormatHints {
    hints.effective(proof)
}
