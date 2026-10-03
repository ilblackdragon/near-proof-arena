/* eslint-disable */
/**
 * GENERATED from common/schemas/submission.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * `sha256:<64 lowercase hex>`
 *
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "Digest".
 */
export type Digest = string;
/**
 * Change classification, computed by the judge (never trusted from the agent).
 *
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "ChangeClass".
 */
export type ChangeClass = 'NO_PARENT' | 'PROVER_ONLY' | 'VERIFIER_OR_PROTOCOL';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "Decision".
 */
export type Decision = 'ADMITTED' | 'REJECTED' | 'INCONCLUSIVE' | 'INFRA_ERROR' | 'CANCELLED';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "EdgeStatus".
 */
export type EdgeStatus = 'checked' | 'trusted' | 'tested' | 'missing';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "NodeKind".
 */
export type NodeKind =
  | 'nearcore_source'
  | 'formal_semantics'
  | 'backend_semantics'
  | 'theorem'
  | 'assumption'
  | 'artifact'
  | 'tcb_component'
  | 'test_suite'
  | 'measurement';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
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
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "ReasonCode".
 */
export type ReasonCode =
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
  | 'CANCELLED';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "GateStatus".
 */
export type GateStatus = 'PASS' | 'FAIL' | 'UNKNOWN' | 'NOT_APPLICABLE';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "Stage".
 */
export type Stage =
  'RECEIVED' | 'VALIDATED' | 'BUILT' | 'FORMAL_CHECKED' | 'CONFORMANCE_CHECKED' | 'BENCHMARKED' | 'DECIDED';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "Tier".
 */
export type Tier = 'formal' | 'experimental' | 'demo';
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "VerifyRoute".
 */
export type VerifyRoute = 'native' | 'npai-v1' | 'native-lean';

/**
 * Public view of a submission (API `GET /v1/submissions/{id}`).
 */
export interface SubmissionView {
  /**
   * `null` while pending; `true` only if every mandatory gate passed.
   */
  accepted?: boolean | null;
  agent: string;
  /**
   * Public artifacts produced by the judge for this run.
   */
  artifacts?: ArtifactRef[];
  /**
   * Assumptions the admission may rely on (the challenge's security profile).
   */
  assumptions?: AssumptionRef[];
  backend_family: string;
  benchmark?: BenchmarkResult | null;
  build?: BuildInfo | null;
  candidate_name: string;
  challenge_id: string;
  change_class?: ChangeClass | null;
  created_at: string;
  decision?: Decision | null;
  evidence_graph?: EvidenceGraph | null;
  gates: GateResult[];
  id: string;
  /**
   * Bounded, sanitized plain-text log excerpts (never HTML).
   */
  logs?: LogExcerpt[];
  package_digest: Digest;
  parent?: string | null;
  reason_codes: ReasonCode[];
  revocation_history?: RevocationEvent[];
  revoked?: Revocation | null;
  score_milli?: number | null;
  stage: Stage;
  tier: Tier;
  /**
   * Trusted computing base entries the result depends on.
   */
  trusted_base?: TrustedBaseEntry[];
  updated_at: string;
  /**
   * Verified-surface digests (set once the judge build completed).
   */
  verified_surface?: VerifiedSurface | null;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "ArtifactRef".
 */
export interface ArtifactRef {
  digest: Digest;
  label: string;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "AssumptionRef".
 */
export interface AssumptionRef {
  description?: string | null;
  id: string;
  lean_decl?: string | null;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "BenchmarkResult".
 */
export interface BenchmarkResult {
  classes: ClassMeasurement[];
  hardware_profile: string;
  measured_by: string;
  prepare_ns: number;
  public_artifact_bytes: number;
  /**
   * Half-width of a bootstrap 95% interval, milli units.
   */
  score_ci_milli?: number | null;
  /**
   * Score * 1000 as integer (e.g. 100000 == 100.000).
   */
  score_milli?: number | null;
  suite_revision: string;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "ClassMeasurement".
 */
export interface ClassMeasurement {
  baseline_ns: number;
  class_id: string;
  cold_ns?: number | null;
  mad_ns: number;
  median_ns: number;
  peak_rss_bytes: number;
  proof_bytes_max: number;
  runs_ns: number[];
  verify_median_ns: number;
  weight_ppm: number;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "BuildInfo".
 */
export interface BuildInfo {
  build_ns?: number | null;
  /**
   * `BUILD_REPRODUCIBLE` passed (two judge builds bit-identical).
   */
  reproducible: boolean;
  /**
   * Build sandbox image/rootfs digest or id, if reported.
   */
  toolchain_image?: string | null;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "EvidenceGraph".
 */
export interface EvidenceGraph {
  edges: EvidenceEdge[];
  nodes: EvidenceNode[];
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "EvidenceEdge".
 */
export interface EvidenceEdge {
  evidence: Digest[];
  from: string;
  /**
   * e.g. `refines`, `binds`, `assumes`, `built_from`, `tested_against`.
   */
  kind: string;
  note: string;
  status: EdgeStatus;
  to: string;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "EvidenceNode".
 */
export interface EvidenceNode {
  digest?: Digest | null;
  id: string;
  kind: NodeKind;
  label: string;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "GateResult".
 */
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
 * This interface was referenced by `SubmissionView`'s JSON-Schema
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
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "LogExcerpt".
 */
export interface LogExcerpt {
  /**
   * Log name, e.g. `BUILD` or `BUILD/error`.
   */
  name: string;
  /**
   * Pipeline stage / job kind the log belongs to.
   */
  stage: string;
  text: string;
  truncated: boolean;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "RevocationEvent".
 */
export interface RevocationEvent {
  /**
   * `revoked` (v1 has no un-revoke).
   */
  action: string;
  at: string;
  by: string;
  reason: string;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "Revocation".
 */
export interface Revocation {
  reason: string;
  revoked_at: string;
  revoked_by: string;
}
/**
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "TrustedBaseEntry".
 */
export interface TrustedBaseEntry {
  digest?: Digest | null;
  id: string;
  label: string;
}
/**
 * The digests that define the *verified* surface. If all are equal between a child and its parent, formal results may be reused (`ProverOnly`).
 *
 * This interface was referenced by `SubmissionView`'s JSON-Schema
 * via the `definition` "VerifiedSurface".
 */
export interface VerifiedSurface {
  certificate_decl: string;
  challenge_id: string;
  checker_image: Digest;
  formal_tree: Digest;
  prepare_artifact: Digest;
  public_artifacts: Digest;
  /**
   * `npai-v1`: SHA-256 digest of the built verifier bytecode image.
   */
  verifier_bytecode?: Digest | null;
  /**
   * `native-lean`: `[formal] verifier_model`.
   */
  verifier_model?: string | null;
  /**
   * `native-lean`: `[formal] verifier_model_module`.
   */
  verifier_model_module?: string | null;
  verify_artifact: Digest;
  /**
   * Effective verify route (`native` when the manifest omits it).
   */
  verify_route?: VerifyRoute | null;
}
