/**
 * Leaderboard partitioning. The official ranked section admits ONLY entries
 * that are tier=formal, decision=ADMITTED, accepted=true, not revoked, on a
 * formal-tier challenge, and not the reference baseline. Everything else is
 * shown in a separate, clearly-labelled, unranked section. Server-provided
 * `rank` is ignored for anything outside the official section.
 */
import type { BoardEntry, ChallengeDefinition } from '../api/types';

export type SectionKey = 'official' | 'formal_other' | 'revoked' | 'reference' | 'experimental' | 'demo';

export interface RankedEntry {
  rank: number;
  entry: BoardEntry;
}

export interface Board {
  official: RankedEntry[];
  formal_other: BoardEntry[];
  revoked: BoardEntry[];
  reference: BoardEntry[];
  experimental: BoardEntry[];
  demo: BoardEntry[];
}

export function isReference(e: BoardEntry, def: ChallengeDefinition | undefined): boolean {
  return e.reference === true || (!!def?.workload_suite.baseline_submission && def.workload_suite.baseline_submission === e.submission_id);
}

export function isOfficiallyRankable(e: BoardEntry, def: ChallengeDefinition | undefined): boolean {
  return (
    def?.tier === 'formal' &&
    e.tier === 'formal' &&
    e.decision === 'ADMITTED' &&
    e.accepted === true &&
    e.revoked === false &&
    !isReference(e, def)
  );
}

export function classify(e: BoardEntry, def: ChallengeDefinition | undefined): SectionKey {
  if (e.tier === 'demo' || def?.tier === 'demo') return 'demo';
  if (e.revoked !== false) return 'revoked';
  if (isReference(e, def)) return 'reference';
  if (e.tier === 'experimental' || def?.tier === 'experimental') return 'experimental';
  if (isOfficiallyRankable(e, def)) return 'official';
  return 'formal_other';
}

const byScoreDesc = (a: BoardEntry, b: BoardEntry) => {
  const sa = typeof a.score_milli === 'number' ? a.score_milli : -1;
  const sb = typeof b.score_milli === 'number' ? b.score_milli : -1;
  if (sa !== sb) return sb - sa;
  return String(a.submitted_at).localeCompare(String(b.submitted_at));
};

export function partition(entries: BoardEntry[], def: ChallengeDefinition | undefined): Board {
  const b: Board = { official: [], formal_other: [], revoked: [], reference: [], experimental: [], demo: [] };
  const official: BoardEntry[] = [];
  for (const e of entries) {
    const k = classify(e, def);
    if (k === 'official') official.push(e);
    else b[k].push(e);
  }
  // Rank by judge-measured score (ties: earlier submission first). A server
  // `rank` is not trusted to order the board; the score is the ranking key.
  official.sort(byScoreDesc);
  b.official = official.map((entry, i) => ({ rank: i + 1, entry }));
  for (const k of ['formal_other', 'revoked', 'reference', 'experimental', 'demo'] as const) b[k].sort(byScoreDesc);
  return b;
}
