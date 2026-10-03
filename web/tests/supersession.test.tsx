import { screen, waitFor, within } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import { benchmark, challengeRecord, makeDefinition, makeSub, type Dataset } from '../mock/fixtures';
import type { ChallengeRecord } from '../src/api/types';
import { renderApp } from './helpers';

function upgradePair(): { oldC: ChallengeRecord; newC: ChallengeRecord; ds: Dataset } {
  const oldBase = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE transfer v1', tier: 'formal' }));
  const newDef = { ...makeDefinition({ name: 'DEMO FIXTURE transfer v1-1', tier: 'formal' }), protocol_version: 81, supersedes: oldBase.id };
  const newC = challengeRecord(newDef);
  const oldC = { ...oldBase, open: false, superseded_by: newC.id };
  const ds: Dataset = {
    challenges: [oldC, newC],
    submissions: [
      makeSub({ id: 'sub_old_win', challenge_id: oldC.id, candidate_name: 'DEMO FIXTURE old winner', score_milli: 200_000, benchmark: benchmark(200_000, 2) }),
    ],
  };
  return { oldC, newC, ds };
}

describe('challenge supersession', () => {
  it('superseded challenge: prominent banner with successor link on challenge and board; board keeps its ranking', async () => {
    const { oldC, newC, ds } = upgradePair();
    renderApp(`/challenges/${oldC.id}`, ds);
    const banners = await screen.findAllByText(/This challenge has been replaced by/);
    expect(banners).toHaveLength(2);
    for (const b of banners) {
      const link = within(b.closest('.superseded-banner') as HTMLElement).getByRole('link');
      expect(link).toHaveAttribute('href', `/challenges/${newC.id}`);
    }
    expect(screen.getByText(/This board is frozen/)).toHaveTextContent('protocol version 80');
    const official = (await screen.findByRole('heading', { level: 2, name: /Official ranking/ })).closest('section')!;
    await waitFor(() => expect(within(official).getByText('DEMO FIXTURE old winner')).toBeInTheDocument());
    expect(within(official).getByText('protocol v80')).toBeInTheDocument();
    expect(within(official).getAllByText('SUPERSEDED').length).toBeGreaterThan(0);
    const lineage = screen.getByRole('list', { name: /supersession chain/ });
    expect(lineage).toHaveTextContent('SUCCESSOR');
    expect(lineage).toHaveTextContent('SUPERSEDED');
  });

  it('successor shows the "supersedes" lineage with the closed predecessor', async () => {
    const { oldC, newC, ds } = upgradePair();
    renderApp(`/challenges/${newC.id}`, ds);
    const lineage = await screen.findByRole('list', { name: /supersession chain/ });
    await waitFor(() => expect(lineage).toHaveTextContent('DEMO FIXTURE transfer v1 · protocol v80'));
    expect(within(lineage).getByRole('link', { name: oldC.id })).toHaveAttribute('href', `/challenges/${oldC.id}`);
    expect(lineage).toHaveTextContent('SUPERSEDED');
    expect(screen.queryByText(/This challenge has been replaced by/)).toBeNull();
    expect(await screen.findByText('No formally admitted submissions yet.')).toBeInTheDocument();
  });

  it('closed (not superseded) challenge shows a closed state; list shows badges', async () => {
    const { ds } = upgradePair();
    const closed = { ...challengeRecord(makeDefinition({ name: 'DEMO FIXTURE paused', tier: 'formal' })), open: false };
    ds.challenges.push(closed);
    const r = renderApp(`/challenges/${closed.id}`, ds);
    expect(await screen.findAllByText(/is not accepting new submissions/)).toHaveLength(2);
    r.unmount();
    renderApp('/', ds);
    await screen.findByText('DEMO FIXTURE paused');
    expect(screen.getAllByText('SUPERSEDED')).toHaveLength(1);
    expect(screen.getAllByText('CLOSED')).toHaveLength(1);
  });

  it('never ranks an entry labelled with a different challenge id', async () => {
    const { newC, ds } = upgradePair();
    const s = makeSub({ id: 'sub_foreign', challenge_id: newC.id, candidate_name: 'DEMO FIXTURE foreign', score_milli: 999_000 });
    ds.leaderboards = {
      [newC.id]: [{ rank: 1, submission_id: s.id, challenge_id: 'chl_' + 'f'.repeat(32), protocol_version: 80, agent: 'demo-fixture-agent', candidate_name: s.candidate_name, backend_family: 'x', tier: 'formal', decision: 'ADMITTED', accepted: true, score_milli: 999_000, hardware_profile: 'hw', scope: 's', security_profile: 'p', submitted_at: '2026-09-01T00:00:00Z', revoked: false }],
    };
    renderApp(`/challenges/${newC.id}`, ds);
    expect(await screen.findByText(/labelled with a different challenge id/)).toBeInTheDocument();
    expect(screen.getByText('No formally admitted submissions yet.')).toBeInTheDocument();
  });
});
