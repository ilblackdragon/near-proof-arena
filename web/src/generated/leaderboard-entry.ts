/* eslint-disable */
/**
 * GENERATED from common/schemas/leaderboard-entry.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * This interface was referenced by `LeaderboardEntry`'s JSON-Schema
 * via the `definition` "ScoringKind".
 */
export type ScoringKind = 'speed' | 'cost_v1';
/**
 * `sha256:<64 lowercase hex>`
 *
 * This interface was referenced by `LeaderboardEntry`'s JSON-Schema
 * via the `definition` "Digest".
 */
export type Digest = string;
/**
 * This interface was referenced by `LeaderboardEntry`'s JSON-Schema
 * via the `definition` "Decision".
 */
export type Decision = 'ADMITTED' | 'REJECTED' | 'INCONCLUSIVE' | 'INFRA_ERROR' | 'CANCELLED';
/**
 * This interface was referenced by `LeaderboardEntry`'s JSON-Schema
 * via the `definition` "Tier".
 */
export type Tier = 'formal' | 'experimental' | 'demo';

export interface LeaderboardEntry {
  accepted?: boolean | null;
  agent: string;
  backend_family: string;
  /**
   * Which board `rank` belongs to: `speed` (default) or `cost_v1` (additive, v1.5).
   */
  board?: ScoringKind | null;
  candidate_name: string;
  /**
   * The challenge this result was measured under (additive, v1.4). A result is never re-labelled or moved to another challenge's board.
   */
  challenge_id?: string;
  /**
   * Per-class cost components, so the board shows why (v1.5).
   */
  cost?: CostResult | null;
  cost_score_ci_milli?: number | null;
  /**
   * Cost-board score and its CI (cost_v1 challenges only; v1.5).
   */
  cost_score_milli?: number | null;
  decision?: Decision | null;
  hardware_profile: string;
  peak_rss_bytes?: number | null;
  proof_bytes?: number | null;
  /**
   * That challenge's NEAR protocol version (additive, v1.4).
   */
  protocol_version?: number;
  prove_median_ns?: number | null;
  rank?: number | null;
  revoked: boolean;
  scope: string;
  /**
   * Half-width of the score's 95% interval, milli units (additive, v1.1).
   */
  score_ci_milli?: number | null;
  score_milli?: number | null;
  security_profile: string;
  submission_id: string;
  submitted_at: string;
  /**
   * Set when the challenge has been superseded: the board is historical (frozen, closed for new submissions) and scores are not comparable with the successor's (additive, v1.4).
   */
  superseded_by?: string | null;
  tier: Tier;
  verify_median_ns?: number | null;
}
/**
 * `BenchmarkResult.cost` (v1.5, additive): the cost-board result.
 *
 * This interface was referenced by `LeaderboardEntry`'s JSON-Schema
 * via the `definition` "CostResult".
 */
export interface CostResult {
  classes: CostClass[];
  kind: ScoringKind;
  price_model_digest: Digest;
  price_model_id: string;
  score_ci_milli?: number | null;
  score_milli?: number | null;
  validators_per_chunk: number;
  verifier_vcpus: number;
}
/**
 * Cost components of one class (component medians, integer femto-USD per batch run). `*_fusd` validator terms already include the `N_v` factor.
 *
 * This interface was referenced by `LeaderboardEntry`'s JSON-Schema
 * via the `definition` "CostClass".
 */
export interface CostClass {
  bandwidth_fusd: number;
  baseline_total_fusd: number;
  class_id: string;
  prepare_fusd: number;
  proof_bytes: number;
  prove_fusd: number;
  prove_ns: number;
  storage_fusd: number;
  total_fusd: number;
  verify_fusd: number;
  verify_ns: number;
  weight_ppm: number;
}
