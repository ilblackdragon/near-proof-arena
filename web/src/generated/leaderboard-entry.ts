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
  /**
   * The challenge this result was measured under (additive, v1.4). A result is never re-labelled or moved to another challenge's board.
   */
  challenge_id?: string;
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
