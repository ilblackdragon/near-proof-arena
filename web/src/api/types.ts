/**
 * API types. Everything is GENERATED (src/generated) from common/schemas and
 * server/openapi.json; this file only re-exports and names them.
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

export type { StoredChallenge, EventPayload } from '../generated/api';
export type {
  ArtifactRef,
  AssumptionRef,
  BuildInfo,
  LogExcerpt,
  RevocationEvent,
  TrustedBaseEntry,
} from '../generated/submission';

import type { StoredChallenge } from '../generated/api';
import type { ChallengeDefinition } from '../generated/challenge';
import type { SubmissionView, Stage } from '../generated/submission';
import type { LeaderboardEntry } from '../generated/leaderboard-entry';

/**
 * A challenge as served by `/v1/challenges[/id]` (`StoredChallenge` in
 * server/openapi.json), with the definition typed from the frozen schema.
 */
export type ChallengeRecord = Omit<StoredChallenge, 'definition'> & { definition: ChallengeDefinition };

/** `GET /v1/submissions/{id}` (includes the v1.1 additive fields). */
export type SubmissionDetail = SubmissionView;
export type BoardEntry = LeaderboardEntry;

export const STAGES: Stage[] = [
  'RECEIVED',
  'VALIDATED',
  'BUILT',
  'FORMAL_CHECKED',
  'CONFORMANCE_CHECKED',
  'BENCHMARKED',
  'DECIDED',
];
