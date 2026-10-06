import { screen, within } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import type { ChallengeDefinition } from '../src/api/types';
import type { CostResult } from '../src/generated/leaderboard-entry';
import { benchmark, challengeRecord, makeDefinition, makeSub, type Dataset } from '../mock/fixtures';
import { renderApp } from './helpers';

const DIGEST = 'sha256:' + 'c0'.repeat(32);
const OTHER = 'sha256:' + 'ee'.repeat(32);

function costDef(): ChallengeDefinition {
  const d = makeDefinition({ name: 'DEMO FIXTURE cost board', tier: 'formal' });
  d.scoring = {
    kind: 'cost_v1',
    price_model_digest: DIGEST,
    price_model: {
      schema: 'arena-price-model-v1',
      id: 'pm-test',
      version: 1,
      status: 'governed',
      effective_from: '2026-10-05',
      currency: 'USD',
      unit: 'femto_usd',
      validators_per_chunk: 84,
      verifier_vcpus: 8,
      cpu_fusd_per_vcpu_second: 7_610_000_000,
      bandwidth_fusd_per_byte: 82_000,
      storage_fusd_per_byte: 0,
      prepare_amortization_requests: 0,
      rationale: [],
    },
    cost_baseline: [],
  };
  return d;
}

function cost(score: number, digest = DIGEST): CostResult {
  return {
    kind: 'cost_v1',
    price_model_id: 'pm-test@v1',
    price_model_digest: digest,
    validators_per_chunk: 84,
    verifier_vcpus: 8,
    score_milli: score,
    score_ci_milli: 500,
    classes: [
      {
        class_id: 'transfer-small',
        weight_ppm: 1_000_000,
        prove_ns: 1_000_000,
        verify_ns: 40_000_000,
        proof_bytes: 8_000,
        prove_fusd: 60_880_000,
        prepare_fusd: 0,
        verify_fusd: 204_000_000_000,
        bandwidth_fusd: 55_000_000_000,
        storage_fusd: 0,
        total_fusd: 259_060_880_000,
        baseline_total_fusd: 259_060_880_000,
      },
    ],
  };
}

function section(name: RegExp) {
  return screen.getByRole('heading', { level: 2, name }).closest('section') as HTMLElement;
}

describe('cost board', () => {
  it('ranks the same admitted entries by cost score, separately from speed', async () => {
    const c = challengeRecord(costDef());
    const sub = (id: string, speed: number, cr: CostResult | null, at: string) =>
      makeSub({
        id,
        challenge_id: c.id,
        candidate_name: `DEMO FIXTURE ${id}`,
        score_milli: speed,
        created_at: at,
        benchmark: { ...benchmark(speed), cost: cr },
      });
    const ds: Dataset = {
      challenges: [c],
      submissions: [
        sub('sub_fast', 110_000, cost(91_000), '2026-10-01T00:00:00Z'),
        sub('sub_lean', 97_000, cost(207_000), '2026-10-02T00:00:00Z'),
        sub('sub_alien', 150_000, cost(999_000, OTHER), '2026-10-03T00:00:00Z'),
      ],
    };
    renderApp(`/challenges/${c.id}`, ds);
    await screen.findByRole('heading', { name: /Cost board/ });
    const speedRows = within(section(/Official ranking/)).getAllByRole('row').slice(1);
    expect(within(speedRows[0]).getByText(/sub_alien/)).toBeInTheDocument();

    const costSec = section(/Cost board/);
    expect(costSec).toHaveTextContent('N_v = 84');
    expect(costSec).toHaveTextContent(DIGEST);
    const board = costSec.querySelector('table.cost-board') as HTMLElement;
    const rows = Array.from(board.querySelectorAll(':scope > tbody > tr'));
    // the result under another price model is never ranked here
    expect(rows).toHaveLength(2);
    expect(rows[0]).toHaveTextContent(/sub_lean/);
    expect(rows[0]).toHaveTextContent('207.000 ± 0.500');
    expect(rows[1]).toHaveTextContent(/sub_fast/);
    expect(costSec).not.toHaveTextContent(/sub_alien/);
    // the breakdown says why
    expect(rows[0]).toHaveTextContent('N_v × verify');
    expect(rows[0]).toHaveTextContent('1.00×');
  });

  it('a speed-only challenge has no cost board', async () => {
    const c = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE speed only', tier: 'formal' }));
    const ds: Dataset = {
      challenges: [c],
      submissions: [
        makeSub({ id: 'sub_a', challenge_id: c.id, score_milli: 100_000, benchmark: { ...benchmark(100_000), cost: cost(5) } }),
      ],
    };
    renderApp(`/challenges/${c.id}`, ds);
    await screen.findByRole('heading', { name: /Official ranking/ });
    expect(screen.queryByRole('heading', { name: /Cost board/ })).toBeNull();
  });
});
