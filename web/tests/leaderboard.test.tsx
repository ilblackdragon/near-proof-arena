import { screen, waitFor, within } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import { benchmark, challengeRecord, demoDataset, makeDefinition, makeSub, type Dataset } from '../mock/fixtures';
import { renderApp } from './helpers';

function section(name: RegExp) {
  const h = screen.getByRole('heading', { level: 2, name });
  return h.closest('section') as HTMLElement;
}

describe('leaderboard', () => {
  it('shows an honest empty state when nothing is formally admitted', async () => {
    const c = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE empty', tier: 'formal' }));
    const ds: Dataset = {
      challenges: [c],
      submissions: [
        makeSub({ id: 'sub_p', challenge_id: c.id, decision: null, accepted: null, stage: 'BUILT' }),
        makeSub({ id: 'sub_r', challenge_id: c.id, decision: 'REJECTED', accepted: false, reason_codes: ['SORRY_FOUND'] }),
      ],
    };
    renderApp(`/challenges/${c.id}`, ds);
    expect(await screen.findByText('No formally admitted submissions yet.')).toBeInTheDocument();
    const official = section(/Official ranking/);
    expect(within(official).queryByRole('table')).toBeNull();
    // The non-admitted ones are listed, unranked, elsewhere.
    const other = section(/not admitted or pending/);
    expect(within(other).getAllByRole('row')).toHaveLength(3);
    expect(within(other).getByText('PENDING')).toBeInTheDocument();
    expect(within(other).getByText('pending (accepted = null)')).toBeInTheDocument();
  });

  it('with an empty leaderboard response there is no placeholder data', async () => {
    const c = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE none', tier: 'formal' }));
    const { container } = renderApp(`/challenges/${c.id}`, { challenges: [c], submissions: [] });
    await screen.findByText('No formally admitted submissions yet.');
    expect(container.querySelectorAll('table.board')).toHaveLength(0);
  });

  it('never ranks DEMO results, even if marked admitted with a high score', async () => {
    const ds = demoDataset();
    const ranked = ds.challenges[1];
    renderApp(`/challenges/${ranked.id}`, ds);
    await screen.findByRole('heading', { name: /DEMO results — never ranked/ });
    const official = section(/Official ranking/);
    const rows = within(official).getAllByRole('row').slice(1);
    // alpha (245) and beta (312.5) only; revoked gamma (500) and reference excluded.
    expect(rows).toHaveLength(2);
    expect(within(rows[0]).getByText(/faster prover/)).toBeInTheDocument();
    expect(rows[0].querySelector('td.rank')?.textContent).toBe('1');
    expect(rows[1].querySelector('td.rank')?.textContent).toBe('2');
    expect(within(official).queryByText(/bwrap-dev/)).toBeNull();
    expect(within(official).queryByText(/DEMO · NOT RANKED/)).toBeNull();

    const demo = section(/DEMO results — never ranked/);
    expect(within(demo).getByText(/bwrap-dev run/)).toBeInTheDocument();
    for (const r of within(demo).getAllByRole('row').slice(1)) {
      expect(r.querySelector('td.rank')?.textContent).toBe('—');
    }
    expect(section(/Revoked/)).toHaveTextContent(/gamma/);
    expect(section(/Reference baseline/)).toHaveTextContent(/reference re-execution/);
    expect(section(/Experimental/)).toHaveTextContent(/gpu experiment/);
  });

  it('a demo-tier challenge has no official board at all', async () => {
    const c = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE demo-only', tier: 'demo' }));
    const ds: Dataset = {
      challenges: [c],
      submissions: [makeSub({ id: 'sub_d', challenge_id: c.id, tier: 'demo', score_milli: 999_000, benchmark: benchmark(999_000) })],
    };
    renderApp(`/challenges/${c.id}`, ds);
    expect(await screen.findByText(/It has no official ranked board/)).toBeInTheDocument();
    await waitFor(() => expect(section(/DEMO results/)).toHaveTextContent('DEMO FIXTURE prover'));
  });

  it('ignores a server-supplied rank on non-official rows', async () => {
    const c = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE ranks', tier: 'formal' }));
    const s = makeSub({ id: 'sub_x', challenge_id: c.id, tier: 'experimental', score_milli: 1 });
    const ds: Dataset = {
      challenges: [c],
      submissions: [s],
      leaderboards: {
        [c.id]: [
          {
            rank: 1,
            submission_id: 'sub_x',
            agent: 'demo-fixture-agent',
            candidate_name: 'DEMO FIXTURE exp',
            backend_family: 'x',
            tier: 'experimental',
            decision: 'ADMITTED',
            accepted: true,
            score_milli: 999_999,
            hardware_profile: 'hw',
            scope: 's',
            security_profile: 'p',
            submitted_at: '2026-09-01T00:00:00Z',
            revoked: false,
          },
        ],
      },
    };
    renderApp(`/challenges/${c.id}`, ds);
    expect(await screen.findByText('No formally admitted submissions yet.')).toBeInTheDocument();
    const exp = section(/Experimental/);
    expect(exp.querySelector('td.rank')?.textContent).toBe('—');
  });

  it('shows score with CI and challenge scope details', async () => {
    const ds = demoDataset();
    const ranked = ds.challenges[1];
    renderApp(`/challenges/${ranked.id}`, ds);
    await screen.findByRole('heading', { name: /Official ranking/ });
    expect(screen.getByText('312.500 ± 3.750')).toBeInTheDocument();
    expect(screen.getByText('Full chunk transition')).toBeInTheDocument();
    expect(screen.getByText('block_finality')).toBeInTheDocument();
  });
});
