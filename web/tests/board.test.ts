import { describe, expect, it } from 'vitest';
import { partition } from '../src/lib/board';
import type { BoardEntry } from '../src/api/types';
import { makeDefinition } from '../mock/fixtures';

const def = makeDefinition({ name: 'DEMO FIXTURE board', tier: 'formal', baseline: 'sub_ref' });
const e = (o: Partial<BoardEntry> & { submission_id: string }): BoardEntry => ({
  agent: 'demo-fixture-agent',
  candidate_name: o.submission_id,
  backend_family: 'x',
  tier: 'formal',
  decision: 'ADMITTED',
  accepted: true,
  score_milli: 100_000,
  hardware_profile: 'hw',
  scope: 's',
  security_profile: 'p',
  submitted_at: '2026-09-01T00:00:00Z',
  revoked: false,
  rank: null,
  ...o,
});

describe('partition', () => {
  it('ranks only formal ADMITTED accepted non-revoked entries, by score', () => {
    const b = partition(
      [
        e({ submission_id: 'sub_low', score_milli: 120_000, rank: 1 }),
        e({ submission_id: 'sub_high', score_milli: 300_000, rank: 9 }),
        e({ submission_id: 'sub_demo', tier: 'demo', score_milli: 9_000_000, rank: 1 }),
        e({ submission_id: 'sub_exp', tier: 'experimental', score_milli: 8_000_000 }),
        e({ submission_id: 'sub_rev', revoked: true, score_milli: 7_000_000 }),
        e({ submission_id: 'sub_ref' }),
        e({ submission_id: 'sub_pend', decision: null, accepted: null }),
        e({ submission_id: 'sub_rej', decision: 'REJECTED', accepted: false }),
        e({ submission_id: 'sub_weird', decision: 'ADMITTED', accepted: null }),
      ],
      def,
    );
    expect(b.official.map((r) => [r.rank, r.entry.submission_id])).toEqual([
      [1, 'sub_high'],
      [2, 'sub_low'],
    ]);
    expect(b.demo.map((x) => x.submission_id)).toEqual(['sub_demo']);
    expect(b.experimental.map((x) => x.submission_id)).toEqual(['sub_exp']);
    expect(b.revoked.map((x) => x.submission_id)).toEqual(['sub_rev']);
    expect(b.reference.map((x) => x.submission_id)).toEqual(['sub_ref']);
    expect(b.formal_other.map((x) => x.submission_id).sort()).toEqual(['sub_pend', 'sub_rej', 'sub_weird']);
  });
  it('never ranks anything on a non-formal challenge', () => {
    const b = partition([e({ submission_id: 'sub_a' })], makeDefinition({ name: 'd', tier: 'demo' }));
    expect(b.official).toEqual([]);
    expect(b.demo).toHaveLength(1);
    const x = partition([e({ submission_id: 'sub_a' })], makeDefinition({ name: 'x', tier: 'experimental' }));
    expect(x.official).toEqual([]);
    expect(x.experimental).toHaveLength(1);
  });
});
