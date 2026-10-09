import { screen, within } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { describe, expect, it } from 'vitest';
import { demoDataset, makeSub } from '../mock/fixtures';
import { researchGroups } from '../src/lib/research';
import { renderApp } from './helpers';

describe('research approaches', () => {
  it('keeps identical backend labels in different challenges separate and preserves rejected predecessors', () => {
    const a = makeSub({ id: 'sub_a', challenge_id: 'chl_a', backend_family: 'shared', created_at: '2026-10-01T00:00:00Z', decision: 'REJECTED' });
    const b = makeSub({ id: 'sub_b', challenge_id: 'chl_b', backend_family: 'shared' });
    const c = makeSub({ id: 'sub_c', challenge_id: 'chl_a', backend_family: 'shared', parent: a.id, created_at: '2026-10-02T00:00:00Z' });
    const groups = researchGroups([c, b, a], '', '');
    expect(groups).toHaveLength(2);
    expect(groups[0].submissions.map((s) => s.id)).toEqual(['sub_a', 'sub_c']);
    expect(researchGroups([a, b, c], 'SHARED', 'chl_b')[0].submissions).toEqual([b]);
  });

  it('shows lineage, scoped gate gaps and data coverage without treating a pending experiment as a ranking', async () => {
    const ds = demoDataset();
    const s = makeSub({
      id: 'sub_research', challenge_id: ds.challenges[0].id,
      backend_family: 'lookup research', candidate_name: 'Partial lookup', agent: 'researcher',
      tier: 'experimental', decision: null, accepted: null, parent: 'sub_predecessor',
      gates: [{ gate: 'FORMAL_IMPL_CONNECTION', mandatory: true, status: 'UNKNOWN', reason_codes: [], summary: '', evidence: [] }],
    });
    ds.submissions = [s];
    renderApp('/research', ds);
    expect(await screen.findByRole('heading', { name: 'lookup research' })).toBeInTheDocument();
    expect(screen.getByText(/at most 2,000/)).toBeInTheDocument();
    expect(screen.getByText(/Retrieved/)).toBeInTheDocument();
    expect(screen.getByRole('link', { name: 'sub_predecessor' })).toHaveAttribute('href', '/submissions/sub_predecessor');
    const row = screen.getAllByRole('row')[1];
    expect(row).toHaveTextContent('EXPERIMENTAL');
    expect(row).toHaveTextContent('UNKNOWN');
    expect(within(row).getByText('FORMAL_IMPL_CONNECTION')).toBeInTheDocument();
    expect(screen.queryByRole('columnheader', { name: /score|rank/i })).not.toBeInTheDocument();
  });

  it('supports shared URL filters, clearing, and literal hostile family labels', async () => {
    const ds = demoDataset();
    ds.submissions = [makeSub({ id: 'sub_hostile', challenge_id: ds.challenges[0].id,
      backend_family: '<img src=x onerror=alert(1)>', agent: 'alice', parent: 'javascript:alert(1)' })];
    const user = userEvent.setup();
    const { container } = renderApp('/research?q=nobody', ds);
    expect(await screen.findByText('No submitted approaches match these filters.')).toBeInTheDocument();
    await user.click(screen.getByRole('button', { name: 'Clear filters' }));
    expect(await screen.findByRole('heading', { name: '<img src=x onerror=alert(1)>' })).toBeInTheDocument();
    expect(container.querySelector('img')).toBeNull();
    expect(container.querySelector('a[href^="javascript:"]')).toBeNull();
    await user.type(screen.getByLabelText('Search approaches'), 'alice');
    expect(screen.getByRole('status')).toHaveTextContent('1 approach group');
    await user.type(screen.getByLabelText('Search approaches'), ' absent');
    expect(screen.getByText('No submitted approaches match these filters.')).toBeInTheDocument();
  });
});
