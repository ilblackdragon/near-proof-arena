/* eslint-disable */
/**
 * GENERATED from server/openapi.json (StoredChallenge, EventPayload) by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

export interface ArenaApiTypes {
  StoredChallenge?: StoredChallenge;
  EventPayload?: EventPayload;
}
export interface StoredChallenge {
  definition: ChallengeDefinition;
  /**
   * `sha256:<64 lowercase hex>`
   */
  digest: string;
  /**
   * Hex ed25519 governance key that signed the definition.
   */
  governance_key: string;
  id: string;
  open: boolean;
  registered_at: string;
  registered_by: string;
  /**
   * Hex signature over the JCS bytes of `definition`.
   */
  signature: string;
  tier: 'formal' | 'experimental' | 'demo';
}
export interface ChallengeDefinition {
  chain_id: string;
  claim_encoding: ClaimEncoding;
  created_at: string;
  hardware_profile: HardwareProfile;
  measurement: MeasurementProcedure;
  name: string;
  nearcore: NearcorePin;
  /**
   * Gates that may be `NOT_APPLICABLE` under this challenge (e.g. FORMAL_ZK for validity-only profiles).
   */
  not_applicable_gates: (
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
    | 'BENCHMARK'
  )[];
  protocol_version: number;
  required_obligations: (
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
    | 'BENCHMARK'
  )[];
  resource_limits: ResourceLimits;
  /**
   * `sha256:<64 lowercase hex>`
   */
  runtime_config_digest: string;
  schema: string;
  season: string;
  security_profile: SecurityProfile;
  semantic_scope: SemanticScope;
  supersedes?: string | null;
  tier: 'formal' | 'experimental' | 'demo';
  toolchain_policy: ToolchainPolicy;
  workload_suite: WorkloadSuite;
}
export interface ClaimEncoding {
  format: string;
  max_claim_bytes: number;
  max_request_bytes: number;
  max_witness_bytes: number;
  /**
   * `sha256:<64 lowercase hex>`
   */
  spec_digest: string;
}
export interface HardwareProfile {
  cpu_model: string;
  gpu?: string | null;
  id: string;
  ram_bytes: number;
  vcpus: number;
}
export interface MeasurementProcedure {
  /**
   * `median` only in v1.
   */
  aggregation: string;
  cold_runs: number;
  concurrency: number;
  measured_runs: number;
  /**
   * Runs farther than this many MADs from the median are flagged (not dropped).
   */
  outlier_mad_k: number;
  per_run_timeout_ms: number;
  warmup_runs: number;
}
export interface NearcorePin {
  commit: string;
  repo: string;
  tag: string;
}
export interface ResourceLimits {
  max_build_ms: number;
  max_prepare_ms: number;
  max_proof_bytes: number;
  max_prove_ms: number;
  max_public_artifact_bytes: number;
  max_ram_bytes: number;
  max_verify_ms: number;
  max_vram_bytes: number;
}
/**
 * Governed security profile (`security/profiles/<id>.json`).
 */
export interface SecurityProfile {
  adversary: 'classical';
  /**
   * Ids into `security/assumptions/*.json`; each pins an exact Lean declaration.
   */
  allowed_assumptions: string[];
  deployment_proofs_log2: number;
  id: string;
  max_aggregation_depth: number;
  max_hash_queries_log2: number;
  max_prover_queries_log2: number;
  model: 'standard' | 'random_oracle';
  privacy: 'validity_only' | 'zero_knowledge';
  setup_model: 'none' | 'transparent' | 'approved_ceremony';
  target_bits: number;
}
export interface SemanticScope {
  /**
   * Properties explicitly NOT established by an admitted proof.
   */
  excludes: string[];
  formal_spec: FormalSpecRef;
  /**
   * e.g. `single_action_receipt_transition`, `chunk_transition`.
   */
  granularity: string;
  kind: 'full_chunk_transition' | 'subset';
  name: string;
  restrictions: Restriction[];
  /**
   * `sha256:<64 lowercase hex>`
   */
  spec_doc_digest: string;
}
export interface FormalSpecRef {
  /**
   * Lean toolchain, e.g. `leanprover/lean4:v4.x.y`.
   */
  lean_toolchain: string;
  /**
   * Fully qualified Lean name of the relation, e.g. `NearSpec.TransferV1.NearRelation`.
   */
  relation_decl: string;
  /**
   * Lean module that defines `NearRelation` for this challenge.
   */
  relation_module: string;
  /**
   * `sha256:<64 lowercase hex>`
   */
  tree_digest: string;
}
export interface Restriction {
  id: string;
  text: string;
}
export interface ToolchainPolicy {
  /**
   * Allowed Lean package imports: name -> pinned git commit.
   */
  allowed_packages: [string, string][];
  /**
   * Exact logical axioms permitted (fully qualified names).
   */
  axiom_allowlist: string[];
  /**
   * `sha256:<64 lowercase hex>`
   */
  checker_image: string;
  lean_toolchain: string;
  /**
   * Independent kernel recheckers that must all accept, e.g. `lean4checker`, `nanoda`.
   */
  recheckers: string[];
}
export interface WorkloadSuite {
  baseline_ns: [string, number][];
  /**
   * Baseline candidate submission id and per-class baseline medians (ns).
   */
  baseline_submission?: string | null;
  classes: WorkloadClass[];
  /**
   * `sha256:<64 lowercase hex>`
   */
  heldout_commitment: string;
  /**
   * `sha256:<64 lowercase hex>`
   */
  public_fixtures: string;
  revision: string;
}
export interface WorkloadClass {
  /**
   * Number of requests per measured batch.
   */
  batch_size: number;
  description: string;
  /**
   * `sha256:<64 lowercase hex>`
   */
  generator: string;
  id: string;
  /**
   * Weight in parts-per-million; all weights in a suite sum to 1_000_000.
   */
  weight_ppm: number;
}
/**
 * Data of one SSE event (`id:` = event id, `event:` = kind).
 */
export interface EventPayload {
  /**
   * Raw audit action, e.g. `run.stage`, `gate.result`, `run.decided`.
   */
  action: string;
  at: string;
  data: unknown;
  id: number;
  run_id?: string | null;
}
