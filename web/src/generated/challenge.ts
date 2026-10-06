/* eslint-disable */
/**
 * GENERATED from common/schemas/challenge.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * `sha256:<64 lowercase hex>`
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "Digest".
 */
export type Digest = string;
/**
 * Sandbox-instance granularity of steady-state benchmark runs.
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "InvocationMode".
 */
export type InvocationMode = 'vm_per_invocation' | 'vm_per_batch';
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
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
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "ScoringKind".
 */
export type ScoringKind = 'speed' | 'cost_v1';
/**
 * How the per-run verify totals of a class are aggregated into the `V` component of the cost (docs/BENCHMARK_SPEC.md §14.3; contracts v1.6).
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "VerifyStatistic".
 */
export type VerifyStatistic = 'median' | 'lower_quartile';
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "AdversaryClass".
 */
export type AdversaryClass = 'classical';
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "SecurityModel".
 */
export type SecurityModel = 'standard' | 'random_oracle';
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "Privacy".
 */
export type Privacy = 'validity_only' | 'zero_knowledge';
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "SetupModel".
 */
export type SetupModel = 'none' | 'transparent' | 'approved_ceremony';
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "ScopeKind".
 */
export type ScopeKind = 'full_chunk_transition' | 'subset';
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "Tier".
 */
export type Tier = 'formal' | 'experimental' | 'demo';

export interface ChallengeDefinition {
  chain_id: string;
  claim_encoding: ClaimEncoding;
  created_at: string;
  /**
   * Formal admission-statement parameters (v1.2, additive; absent ⇒ not serialized, so existing challenge ids are unchanged).
   */
  formal_params?: FormalParams | null;
  hardware_profile: HardwareProfile;
  measurement: MeasurementProcedure;
  name: string;
  nearcore: NearcorePin;
  /**
   * Gates that may be `NOT_APPLICABLE` under this challenge (e.g. FORMAL_ZK for validity-only profiles).
   */
  not_applicable_gates: ObligationId[];
  protocol_version: number;
  required_obligations: ObligationId[];
  resource_limits: ResourceLimits;
  runtime_config_digest: Digest;
  schema: string;
  /**
   * Scoring kind and, for `cost_v1`, the pinned price model and reference cost components (v1.5, additive; absent ⇒ `speed` and not serialized, so existing challenge ids are unchanged). docs/BENCHMARK_SPEC.md §14.
   */
  scoring?: ScoringSpec | null;
  season: string;
  security_profile: SecurityProfile;
  semantic_scope: SemanticScope;
  supersedes?: string | null;
  tier: Tier;
  toolchain_policy: ToolchainPolicy;
  workload_suite: WorkloadSuite;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "ClaimEncoding".
 */
export interface ClaimEncoding {
  format: string;
  max_claim_bytes: number;
  max_request_bytes: number;
  max_witness_bytes: number;
  spec_digest: Digest;
}
/**
 * Parameters of the judge-built admission statement that are not resource limits of the sandbox (`ArenaCore.ChallengeParams`). Optional so that challenges without a formal statement (demo) keep their ids.
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "FormalParams".
 */
export interface FormalParams {
  /**
   * Honest proof-size bound used by `VerifierComplete` (`ChallengeParams.maxProofBytes`); must equal `resource_limits.max_proof_bytes`.
   */
  max_proof_bytes: number;
  /**
   * Fuel cap of an explicit standard-model security reduction (`ChallengeParams.maxReductionFuel`).
   */
  max_reduction_fuel: number;
  /**
   * NPAI fuel given to the approved interpreter for one `verify` call (`ChallengeParams.verifyFuel`).
   */
  verify_fuel: number;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "HardwareProfile".
 */
export interface HardwareProfile {
  cpu_model: string;
  gpu?: string | null;
  id: string;
  ram_bytes: number;
  vcpus: number;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "MeasurementProcedure".
 */
export interface MeasurementProcedure {
  /**
   * `median` only in v1.
   */
  aggregation: string;
  cold_runs: number;
  concurrency: number;
  /**
   * How benchmark invocations are isolated (v1.4, additive; absent ⇒ `vm_per_invocation`, i.e. bench-spec-v1, and not serialized, so existing challenge ids are unchanged). See docs/BENCHMARK_SPEC.md §4.
   */
  invocation_mode?: InvocationMode | null;
  measured_runs: number;
  /**
   * Runs farther than this many MADs from the median are flagged (not dropped).
   */
  outlier_mad_k: number;
  per_run_timeout_ms: number;
  warmup_runs: number;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "NearcorePin".
 */
export interface NearcorePin {
  commit: string;
  repo: string;
  tag: string;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "ResourceLimits".
 */
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
 * `ChallengeDefinition.scoring` (v1.5, additive).
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "ScoringSpec".
 */
export interface ScoringSpec {
  cost_baseline?: CostBaselineClass[];
  /**
   * Reference candidate's `prepare` wall ns (only charged when `prepare_amortization_requests > 0`).
   */
  cost_baseline_prepare_ns?: number | null;
  kind: ScoringKind;
  price_model?: PriceModel | null;
  /**
   * JCS sha256 of `price_model`; shown on every cost-board row.
   */
  price_model_digest?: Digest | null;
  /**
   * Aggregation of per-run verify totals (v1.6, additive; absent = `median`). `cost_baseline.verify_ns` is pinned with the same statistic.
   */
  verify_statistic?: VerifyStatistic | null;
}
/**
 * Reference-candidate cost components of one class, measured under the challenge's procedure (component medians over measured runs; one run = one batch of `batch_size` requests).
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "CostBaselineClass".
 */
export interface CostBaselineClass {
  class_id: string;
  /**
   * Median Σ proof bytes per batch.
   */
  proof_bytes: number;
  /**
   * Median Σ prove wall ns per batch; must equal `workload_suite.baseline_ns`.
   */
  prove_ns: number;
  /**
   * Median Σ verify wall ns per batch, on `verifier_vcpus` CPUs.
   */
  verify_ns: number;
}
/**
 * `arena-price-model-v1`: integers only, femto-USD. Per-chunk system cost of one proved request (docs/BENCHMARK_SPEC.md §14.2):
 *
 * ```text C = c_cpu·vcpus_p·T_prove + c_cpu·vcpus_p·T_prepare·/A + N_v · ( c_cpu·vcpus_v·T_verify + (c_bw + c_store)·proof_bytes ) ```
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "PriceModel".
 */
export interface PriceModel {
  /**
   * `c_bw`: network cost per proof byte per validator.
   */
  bandwidth_fusd_per_byte: number;
  /**
   * `c_cpu`: price of one vCPU for one second (prover and validator).
   */
  cpu_fusd_per_vcpu_second: number;
  /**
   * `USD`.
   */
  currency: string;
  effective_from: string;
  id: string;
  /**
   * `A`: requests over which one `prepare` is amortized; 0 = `prepare` is not charged (reported only, bench-spec-v1 §2).
   */
  prepare_amortization_requests: number;
  rationale: PriceRationale[];
  /**
   * `arena-price-model-v1`.
   */
  schema: string;
  /**
   * `draft` (never pinned by a signed challenge) or `governed`.
   */
  status: string;
  /**
   * `c_store`: retention cost per proof byte per validator (0 = none).
   */
  storage_fusd_per_byte: number;
  /**
   * `femto_usd`.
   */
  unit: string;
  /**
   * `N_v`: validators that each verify every chunk's proof (stateless validation fan-out). ≥ 1.
   */
  validators_per_chunk: number;
  /**
   * vCPUs of the reference validator profile; `verify` is measured pinned to this many of the benchmark CPUs and charged for them. ≥ 1 and ≤ the challenge's `hardware_profile.vcpus`.
   */
  verifier_vcpus: number;
  version: number;
}
/**
 * Why a price-model parameter has its value (part of the hashed object, so the rationale cannot be edited without a new version).
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "PriceRationale".
 */
export interface PriceRationale {
  /**
   * `protocol` (read from pinned nearcore), `published` (public price list / docs), or `estimate` (a modelling choice).
   */
  basis: string;
  note: string;
  /**
   * Field name of the parameter, e.g. `validators_per_chunk`.
   */
  param: string;
  sources: string[];
}
/**
 * Governed security profile (`security/profiles/<id>.json`).
 *
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "SecurityProfile".
 */
export interface SecurityProfile {
  adversary: AdversaryClass;
  /**
   * Ids into `security/assumptions/*.json`; each pins an exact Lean declaration.
   */
  allowed_assumptions: string[];
  deployment_proofs_log2: number;
  id: string;
  max_aggregation_depth: number;
  max_hash_queries_log2: number;
  max_prover_queries_log2: number;
  model: SecurityModel;
  privacy: Privacy;
  setup_model: SetupModel;
  target_bits: number;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "SemanticScope".
 */
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
  kind: ScopeKind;
  name: string;
  restrictions: Restriction[];
  /**
   * Human-readable spec document digest (`spec/<name>.md`).
   */
  spec_doc_digest: Digest;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "FormalSpecRef".
 */
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
   * Tree digest of `spec/lean` + `formal-core` sources the challenge was frozen against.
   */
  tree_digest: Digest;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "Restriction".
 */
export interface Restriction {
  id: string;
  text: string;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "ToolchainPolicy".
 */
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
   * Digest of the formal checker image (rootfs) used for clean rechecks.
   */
  checker_image: Digest;
  lean_toolchain: string;
  /**
   * Independent kernel recheckers that must all accept, e.g. `lean4checker`, `nanoda`.
   */
  recheckers: string[];
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "WorkloadSuite".
 */
export interface WorkloadSuite {
  baseline_ns: [string, number][];
  /**
   * Baseline candidate submission id and per-class baseline medians (ns).
   */
  baseline_submission?: string | null;
  classes: WorkloadClass[];
  /**
   * Commitment to the held-out set (digest of its tree), revealed at season end.
   */
  heldout_commitment: Digest;
  /**
   * Public dev fixtures (tree digest). Held-out and fresh inputs are not listed here.
   */
  public_fixtures: Digest;
  revision: string;
}
/**
 * This interface was referenced by `ChallengeDefinition`'s JSON-Schema
 * via the `definition` "WorkloadClass".
 */
export interface WorkloadClass {
  /**
   * Number of requests per measured batch.
   */
  batch_size: number;
  description: string;
  /**
   * Digest of the generator spec (fresh inputs are sampled after freeze).
   */
  generator: Digest;
  id: string;
  /**
   * Weight in parts-per-million; all weights in a suite sum to 1_000_000.
   */
  weight_ppm: number;
}
