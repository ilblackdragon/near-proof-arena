/* eslint-disable */
/**
 * GENERATED from common/schemas/leaderboard-entry.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

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
  candidate_name: string;
  decision?: Decision | null;
  hardware_profile: string;
  peak_rss_bytes?: number | null;
  proof_bytes?: number | null;
  prove_median_ns?: number | null;
  rank?: number | null;
  revoked: boolean;
  scope: string;
  score_milli?: number | null;
  security_profile: string;
  submission_id: string;
  submitted_at: string;
  tier: Tier;
  verify_median_ns?: number | null;
}
