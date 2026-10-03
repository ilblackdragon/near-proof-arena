//! Hostile proof-byte generators for NEAR Proof Arena (adversarial lane).
//!
//! These are *beyond* the generic mutators a runner applies by default. They
//! target the structure of a validity proof and its public-input binding: a
//! correct verifier must reject every mutant produced here while still
//! accepting the honest proof. The [`ADVERSARIAL_PROOFS`] gate feeds each
//! mutant to the candidate's `verify` and fails the submission if any mutant
//! is accepted (reason code `HOSTILE_PROOF_ACCEPTED`).
//!
//! The generators are *generic over an opaque byte format* using
//! [`FormatHints`]: when the challenge provides offsets of embedded
//! commitments, length-prefixed segments or trie-witness nodes they are used
//! precisely; otherwise byte-level heuristics are applied so the suite still
//! produces useful mutants against a format it has never seen.
//!
//! Every mutant carries a [`Kill`] classification. The arena never conflates
//! kinds: a *packaging* kill (e.g. a stale formal digest, a wrong-length blob)
//! says nothing about semantic soundness, and the report must not present it
//! as if it did. See [`KillKind`].
//!
//! [`ADVERSARIAL_PROOFS`]: arena_types::ObligationId::AdversarialProofs

pub mod expect;
pub mod hints;
pub mod mutators;
pub mod rng;
pub mod suite;

pub use hints::{FormatHints, LenField, Region};
pub use rng::Rng;

/// What a mutant, if *accepted* by a verifier, would prove was broken — and
/// therefore how an arena report is allowed to describe the kill.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum KillKind {
    /// Rejection is about *form*: lengths, encodings, truncation, canonicality,
    /// digests of the wrong artifact. A packaging kill demonstrates input
    /// validation, NOT cryptographic/semantic soundness, and must never be
    /// reported as "the proof system is sound".
    Packaging,
    /// Rejection is about *binding*: the proof is well-formed and may even be a
    /// real proof, but it is bound to a different claim / context / challenge
    /// than the one under test (public-input binding, domain separation,
    /// transcript, recursive substitution). A binding kill shows the verifier
    /// refuses to let a valid proof of X pass as a proof of Y.
    Binding,
    /// Rejection must come from the *soundness* of the argument: the committed
    /// values are internally inconsistent (flipped root bit, swapped Merkle
    /// siblings, forged transcript challenge). Only a semantic kill speaks to
    /// the verifier actually checking the relation.
    Semantic,
}

impl KillKind {
    pub fn is_semantic(self) -> bool {
        matches!(self, KillKind::Semantic)
    }
}

/// One generated hostile proof.
#[derive(Clone, Debug)]
pub struct MutatedProof {
    /// Mutant bytes to hand to `verify` (with the honest claim, unless
    /// `claim_override` is set).
    pub bytes: Vec<u8>,
    /// Name of the [`Mutator`] that produced it.
    pub mutator: String,
    /// Short, unique-within-mutator label for this specific mutant.
    pub label: String,
    /// Classification of the kill this mutant is meant to force.
    pub kill: KillKind,
    /// If set, the arena should drive `verify` with THIS claim instead of the
    /// honest one (used for binding/context mutants that only make sense paired
    /// with a foreign claim).
    pub claim_override: Option<Vec<u8>>,
    /// Human-readable evidence explaining *why* a correct verifier rejects this
    /// mutant, and what an acceptance would reveal. Surfaced in gate evidence.
    pub explain: String,
}

impl MutatedProof {
    pub fn new(
        mutator: &str,
        label: impl Into<String>,
        kill: KillKind,
        bytes: Vec<u8>,
        explain: impl Into<String>,
    ) -> Self {
        MutatedProof {
            bytes,
            mutator: mutator.to_string(),
            label: label.into(),
            kill,
            claim_override: None,
            explain: explain.into(),
        }
    }
    pub fn with_claim(mut self, claim: Vec<u8>) -> Self {
        self.claim_override = Some(claim);
        self
    }
}

/// Context handed to every mutator. Holds structure hints and, when available,
/// foreign artifacts (a proof/claim from another challenge case) used by
/// binding and recursive-substitution mutants.
#[derive(Clone, Debug, Default)]
pub struct MutationCtx<'a> {
    pub hints: FormatHints,
    /// A claim from a *different* case/challenge, for mismatched-context tests.
    pub foreign_claim: Option<&'a [u8]>,
    /// An honest proof from a *different* case/challenge, for recursive
    /// proof-substitution tests.
    pub foreign_proof: Option<&'a [u8]>,
    /// Formal digests claimed by the package manifest, for stale-digest
    /// packaging mutants (opaque to the verifier; checked by the judge).
    pub claimed_formal_digest: Option<&'a str>,
}

/// A hostile proof-byte generator.
pub trait Mutator {
    /// Stable identifier, used in gate evidence and the mutants report.
    fn name(&self) -> &str;
    /// One-line description of the attack family.
    fn describe(&self) -> &str;
    /// Produce zero or more mutants from an honest `(honest, claim)` pair.
    /// May return empty when the mutant does not apply to the given bytes
    /// (e.g. no foreign proof available, witness too short) — the arena treats
    /// an empty result as "not applicable", never as a pass.
    fn mutate(
        &self,
        honest: &[u8],
        claim: &[u8],
        ctx: &MutationCtx,
        rng: &mut Rng,
    ) -> Vec<MutatedProof>;
}

/// The full registry of hostile mutators this lane ships.
pub fn registry() -> Vec<Box<dyn Mutator>> {
    mutators::all()
}

/// Run every registered mutator against an honest pair and collect the mutants.
pub fn generate_all(
    honest: &[u8],
    claim: &[u8],
    ctx: &MutationCtx,
    seed: u64,
) -> Vec<MutatedProof> {
    let mut rng = Rng::new(seed);
    let mut out = Vec::new();
    for m in registry() {
        out.extend(m.mutate(honest, claim, ctx, &mut rng));
    }
    out
}
