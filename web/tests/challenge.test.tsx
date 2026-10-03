import { screen, within } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import { challengeRecord, demoDataset, makeDefinition, type Dataset } from '../mock/fixtures';
import { renderApp } from './helpers';

describe('challenges', () => {
  it('lists challenges with tier, scope and excludes', async () => {
    renderApp('/', demoDataset());
    const rows = await screen.findAllByRole('row');
    expect(rows).toHaveLength(4);
    expect(screen.getAllByText('SUBSET of NEAR semantics').length).toBe(2);
    expect(screen.getByText('Full chunk transition')).toBeInTheDocument();
    expect(screen.getAllByText('DEMO · NOT RANKED')).toHaveLength(1);
    expect(screen.getAllByText('data_availability').length).toBe(3);
  });

  it('detail shows id, digest, pin, scope excludes prominently and verifies the id', async () => {
    const ds = demoDataset();
    const c = ds.challenges[0];
    renderApp(`/challenges/${c.id}`, ds);
    const excl = await screen.findByRole('region', { name: /does NOT establish/ });
    for (const x of ['block_finality', 'data_availability', 'receipt_inclusion']) {
      expect(within(excl).getByText(x)).toBeInTheDocument();
    }
    expect(within(excl).getByText('single_action')).toBeInTheDocument();
    expect(await screen.findByText(/id and digest recomputed in this browser/)).toBeInTheDocument();
    expect(screen.getAllByText(c.id).length).toBeGreaterThan(0);
    expect(screen.getByText(c.digest!)).toBeInTheDocument();
    const facts = screen.getByRole('heading', { name: 'Definition' }).nextElementSibling as HTMLElement;
    expect(within(facts).getByText('validity-classical-128')).toBeInTheDocument();
    expect(within(facts).getByText('demo-cpu-32')).toBeInTheDocument();
    expect(within(facts).getByText('demo-r1')).toBeInTheDocument();
    expect(within(facts).getByText('80')).toBeInTheDocument();
  });

  it('shows registration (signature, governance key, open state)', async () => {
    const ds = demoDataset();
    const c = ds.challenges[0];
    renderApp(`/challenges/${c.id}`, ds);
    await screen.findByText('demo-fixture-governance-key');
    expect(screen.getByText(/demo-fixture-admin/)).toBeInTheDocument();
    expect(screen.getByText('open')).toBeInTheDocument();
  });

  it('drops records whose top-level tier disagrees with the signed definition', async () => {
    const c = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE tier-lie', tier: 'demo' }));
    renderApp(`/challenges/${c.id}`, { challenges: [{ ...c, tier: 'formal' }], submissions: [] });
    expect(await screen.findByText(/Malformed challenge record/)).toBeInTheDocument();
  });

  it('flags a challenge whose definition does not hash to its id', async () => {
    const good = challengeRecord(makeDefinition({ name: 'DEMO FIXTURE tamper', tier: 'formal' }));
    const tampered = { ...good, definition: { ...good.definition, excludes_note: 'x', name: 'DEMO FIXTURE tampered' } };
    const ds: Dataset = { challenges: [tampered], submissions: [] };
    renderApp(`/challenges/${good.id}`, ds);
    expect(await screen.findByText(/MISMATCH/)).toBeInTheDocument();
  });

});
