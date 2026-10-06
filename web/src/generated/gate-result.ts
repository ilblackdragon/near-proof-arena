/* eslint-disable */
/**
 * GENERATED from common/schemas/gate-result.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * `sha256:<64 lowercase hex>`
 *
 * This interface was referenced by `GateResult`'s JSON-Schema
 * via the `definition` "Digest".
 */
export type Digest = string;
/**
 * This interface was referenced by `GateResult`'s JSON-Schema
 * via the `definition` "ObligationId".
 */
export type ObligationId =
  | 'PKG_WELLFORMED'
  | 'BUILD_REPRODUCIBLE'
  | 'ARTIFACT_BINDING'
  | 'FORMAL_SEMANTIC_SOUNDNESS'
  | 'FORMAL_SEMANTIC_COMPLETENESS'
  | 'FORMAL_CRYPTO_SOUNDNESS'
  | 'FORMAL_IMPL_CONNECTION'
  | 'FORMAL_ZK'
  | 'AXIOM_AUDIT'
  | 'CONFORMANCE_DIFFERENTIAL'
  | 'ADVERSARIAL_PROOFS'
  | 'PROVER_RELIABILITY'
  | 'RESOURCE_LIMITS'
  | 'BENCHMARK';
/**
 * This interface was referenced by `GateResult`'s JSON-Schema
 * via the `definition` "ReasonCode".
 */
export type ReasonCode =
  | (
      | 'MANIFEST_INVALID'
      | 'ARCHIVE_UNSAFE'
      | 'CHALLENGE_UNKNOWN'
      | 'PROFILE_NOT_ALLOWED'
      | 'BUILD_FAILED'
      | 'BUILD_NOT_REPRODUCIBLE'
      | 'CERTIFICATE_MISSING'
      | 'THEOREM_TYPE_MISMATCH'
      | 'UNAPPROVED_ASSUMPTION'
      | 'FORBIDDEN_AXIOM'
      | 'SORRY_FOUND'
      | 'NATIVE_EVAL_FOUND'
      | 'SHADOWED_DEFINITION'
      | 'RECHECK_FAILED'
      | 'ARTIFACT_BINDING_FAILED'
      | 'CLAIM_MISMATCH'
      | 'COUNTEREXAMPLE_FOUND'
      | 'HOSTILE_PROOF_ACCEPTED'
      | 'VERIFIER_NONDETERMINISTIC'
      | 'PROVER_FAILED'
      | 'RESOURCE_LIMIT'
      | 'TIMEOUT'
      | 'SANDBOX_VIOLATION'
      | 'SECURITY_BOUND_INSUFFICIENT'
      | 'OBLIGATION_UNDISCHARGED'
      | 'DEMO_ONLY'
      | 'INFRA_ERROR'
      | 'CANCELLED'
    )
  | 'COVERAGE_GAP_IN_TIER';
/**
 * This interface was referenced by `GateResult`'s JSON-Schema
 * via the `definition` "GateStatus".
 */
export type GateStatus = 'PASS' | 'FAIL' | 'UNKNOWN' | 'NOT_APPLICABLE';

export interface GateResult {
  evidence: EvidenceRef[];
  finished_at?: string | null;
  /**
   * Gate id; equals the obligation id for obligation gates.
   */
  gate: ObligationId;
  mandatory: boolean;
  reason_codes: ReasonCode[];
  /**
   * Set when the result was reused from a parent via the content-addressed cache.
   */
  reused_from?: string | null;
  started_at?: string | null;
  status: GateStatus;
  /**
   * Bounded, sanitized, plain text (never HTML).
   */
  summary: string;
}
/**
 * This interface was referenced by `GateResult`'s JSON-Schema
 * via the `definition` "EvidenceRef".
 */
export interface EvidenceRef {
  digest: Digest;
  label: string;
  /**
   * Whether this artifact may be shown publicly (held-out data must not).
   */
  public: boolean;
}
