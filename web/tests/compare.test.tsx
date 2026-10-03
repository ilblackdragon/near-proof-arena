import { screen, waitFor } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import { demoDataset } from '../mock/fixtures';
import { renderApp } from './helpers';

describe('compare', () => {
  it('shows two submissions side by side and marks differences', async () => {
    const { container } = renderApp('/compare?a=sub_demo_beta&b=sub_demo_alpha', demoDataset());
    await waitFor(() => expect(container.querySelector('table.compare')).not.toBeNull());
    await waitFor(() => expect(screen.getByText('312.500 ± 3.750')).toBeInTheDocument());
    expect(screen.getByText('245.000 ± 2.940')).toBeInTheDocument();
    const scoreRow = screen.getByText('Score').closest('tr')!;
    expect(scoreRow).toHaveClass('differ');
    // Same verifier artifact (PROVER_ONLY child) -> not marked as differing.
    expect(screen.getByText('Verify artifact').closest('tr')).not.toHaveClass('differ');
    expect(screen.getByText('Gate AXIOM_AUDIT').closest('tr')).toHaveTextContent('reused');
  });

  it('rejects malformed ids', async () => {
    renderApp('/compare?a=<script>&b=sub_demo_alpha', demoDataset());
    expect(await screen.findByText(/Submission ids look like/)).toBeInTheDocument();
  });
});
