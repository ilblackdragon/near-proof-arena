import { screen, waitFor, within } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { describe, expect, it } from 'vitest';
import { demoDataset } from '../mock/fixtures';
import { renderApp } from './helpers';

const bodyRows = () => screen.getAllByRole('row').slice(1);

describe('all submissions view', () => {
  it('lists everything and filters by decision, tier, challenge and agent', async () => {
    const ds = demoDataset();
    const user = userEvent.setup();
    const { fetchSpy } = renderApp('/submissions', ds);
    await waitFor(() => expect(bodyRows()).toHaveLength(ds.submissions.length));

    await user.selectOptions(screen.getByLabelText('Decision'), 'PENDING');
    await waitFor(() => expect(bodyRows()).toHaveLength(1));
    expect(bodyRows()[0]).toHaveTextContent('in-flight');

    await user.selectOptions(screen.getByLabelText('Decision'), '');
    await user.selectOptions(screen.getByLabelText('Tier'), 'demo');
    await waitFor(() => expect(bodyRows()).toHaveLength(2));

    await user.selectOptions(screen.getByLabelText('Tier'), '');
    await user.selectOptions(screen.getByLabelText('Challenge'), ds.challenges[0].id);
    await waitFor(() => expect(bodyRows()).toHaveLength(3));
    expect(fetchSpy.mock.calls.some((c) => String(c[0]).includes(`challenge_id=${ds.challenges[0].id}`))).toBe(true);

    await user.click(screen.getByRole('button', { name: 'Clear filters' }));
    await user.type(screen.getByLabelText('Agent'), 'demo-fixture-arena');
    await user.click(screen.getByRole('button', { name: 'Apply' }));
    await waitFor(() => expect(bodyRows()).toHaveLength(1));
    expect(within(bodyRows()[0]).getAllByRole('link')[0]).toHaveAttribute('href', '/submissions/sub_demo_ref');
  });

  it('honest empty state for no matches', async () => {
    renderApp('/submissions?agent=nobody', demoDataset());
    expect(await screen.findByText('No submissions match these filters.')).toBeInTheDocument();
  });
});
