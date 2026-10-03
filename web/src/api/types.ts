/**
 * API types. Contract types are GENERATED from common/schemas (src/generated);
 * this file only re-exports them and adds the web client's normalised
 * envelopes plus *optional* fields the UI renders when the server provides
 * them (see README "API assumptions"). Nothing here changes the contracts.
 */
export type {
  ChallengeDefinition,
  Tier,
  ScopeKind,
  SecurityProfile,
  WorkloadClass,
  HardwareProfile,
} from '../generated/challenge';
export type {
  SubmissionView,
  BenchmarkResult,
  ClassMeasurement,
  GateResult,
  GateStatus,
  Decision,
  Stage,
  ReasonCode,
  ObligationId,
  ChangeClass,
  Revocation,
  EvidenceGraph,
  EvidenceEdge,
  EvidenceNode,
  EdgeStatus,
  NodeKind,
} from '../generated/submission';
export type { LeaderboardEntry } from '../generated/leaderboard-entry';
export type { VerifiedSurface } from '../generated/verified-surface';
export type { Assumption } from '../generated/assumption';

import type { ChallengeDefinition } from '../generated/challenge';
import type { SubmissionView, Stage } from '../generated/submission';
import type { LeaderboardEntry } from '../generated/leaderboard-entry';
import type { VerifiedSurface } from '../generated/verified-surface';

/** A challenge as served by `/v1/challenges[/id]`, normalised. */
export interface ChallengeRecord {
  id: string;
  /** Digest reported by the server, if any. */
  digest: string | null;
  definition: ChallengeDefinition;
}

export interface LabelledDigest {
  label: string;
  digest: string;
}

export interface LogBlock {
  name: string;
  text: string;
  truncated?: boolean;
}

export interface RevocationEvent {
  action: string;
  reason: string;
  at: string;
  by: string;
}

export interface TrustedBaseEntry {
  id: string;
  label: string;
  digest?: string | null;
}

export interface AssumptionRef {
  id: string;
  lean_decl?: string;
  description?: string;
}

/**
 * Optional, non-contract fields the submission page renders when present.
 * The frozen `SubmissionView` is the guaranteed baseline.
 */
export interface SubmissionExtras {
  artifacts?: LabelledDigest[];
  verified_surface?: VerifiedSurface | null;
  build?: Record<string, string | number | boolean | null>;
  assumptions?: AssumptionRef[];
  trusted_base?: TrustedBaseEntry[];
  logs?: LogBlock[];
  revocation_history?: RevocationEvent[];
}

export type SubmissionDetail = SubmissionView & SubmissionExtras;

/** Optional CI half-width on leaderboard rows (not in the frozen entry). */
export type BoardEntry = LeaderboardEntry & { score_ci_milli?: number | null; reference?: boolean };

export const STAGES: Stage[] = [
  'RECEIVED',
  'VALIDATED',
  'BUILT',
  'FORMAL_CHECKED',
  'CONFORMANCE_CHECKED',
  'BENCHMARKED',
  'DECIDED',
];
