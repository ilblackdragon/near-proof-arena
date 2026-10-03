//! Structure hints over an otherwise opaque proof byte format.
//!
//! The arena does not standardize a proof encoding — each backend family has
//! its own. To mutate meaningfully without parsing, a challenge (or a backend
//! author, via the SDK) may describe *where* interesting structure lives:
//! embedded 32-byte commitments/roots, little-endian length prefixes, and
//! NEAR trie-witness node boundaries. When no hints are given, mutators fall
//! back to heuristics (see [`FormatHints::infer`]).
//!
//! The hints are advisory only: the judge never trusts them to decide a kill.
//! Their sole purpose is to steer mutation so the hostile-proof gate exercises
//! the parts of the format that matter (commitments, lengths, Merkle paths).

use serde::{Deserialize, Serialize};

/// A labelled byte range within the proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Region {
    pub label: String,
    pub offset: usize,
    pub len: usize,
}

/// A little-endian length field embedded in the proof (`width` bytes at
/// `offset`) that governs a following variable segment. Used by malformed-
/// length and truncation mutators.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LenField {
    pub label: String,
    pub offset: usize,
    /// 1, 2, 4 or 8.
    pub width: usize,
}

/// Advisory structure of a proof's bytes.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FormatHints {
    /// Byte offsets of embedded 32-byte commitments (state roots, Merkle
    /// roots, hashes). Flipping a bit here must be a *semantic* kill.
    #[serde(default)]
    pub commitments: Vec<Region>,
    /// Length-prefixed variable segments.
    #[serde(default)]
    pub lengths: Vec<LenField>,
    /// NEAR trie-witness node boundaries (each a `RawTrieNodeWithSize` blob).
    /// Enables sibling-swap, truncation, duplication and node-type confusion
    /// against the witness format described in `docs/research/first-slice.md`.
    #[serde(default)]
    pub trie_nodes: Vec<Region>,
    /// Transcript / Fiat-Shamir challenge regions (domain separation).
    #[serde(default)]
    pub transcript: Vec<Region>,
    /// A tag/prefix the format uses for domain separation (e.g. a context or
    /// challenge id mixed into the transcript), if any.
    #[serde(default)]
    pub domain_tag: Option<Region>,
}

impl FormatHints {
    pub fn is_empty(&self) -> bool {
        self.commitments.is_empty()
            && self.lengths.is_empty()
            && self.trie_nodes.is_empty()
            && self.transcript.is_empty()
            && self.domain_tag.is_none()
    }

    /// Heuristic hints for a format we have no description of. Treats the proof
    /// as a sequence of 32-byte words (the NEAR witness is sha256-addressed, so
    /// 32-byte aligned regions are a good guess for commitments) and flags
    /// plausible u32 length prefixes (a small value followed by that many
    /// bytes remaining). This is best-effort: wrong guesses only cost a few
    /// extra mutants, never a false kill.
    pub fn infer(proof: &[u8]) -> FormatHints {
        let mut h = FormatHints::default();
        // Candidate 32-byte commitment windows at 32-byte alignment.
        let mut off = 0;
        while off + 32 <= proof.len() {
            h.commitments.push(Region {
                label: format!("word@{off}"),
                offset: off,
                len: 32,
            });
            off += 32;
        }
        // Candidate u32-LE length prefixes.
        let mut i = 0;
        while i + 4 <= proof.len() {
            let v =
                u32::from_le_bytes([proof[i], proof[i + 1], proof[i + 2], proof[i + 3]]) as usize;
            let remaining = proof.len() - (i + 4);
            if v > 0 && v <= remaining && v <= 1 << 20 {
                h.lengths.push(LenField {
                    label: format!("len@{i}"),
                    offset: i,
                    width: 4,
                });
            }
            i += 4;
        }
        h
    }

    /// The hints to actually use: the supplied ones if any, else inferred.
    pub fn effective(&self, proof: &[u8]) -> FormatHints {
        if self.is_empty() {
            FormatHints::infer(proof)
        } else {
            self.clone()
        }
    }
}
