import { act, screen, waitFor, within } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import { demoDataset, evidenceGraph } from '../mock/fixtures';
import { renderApp } from './helpers';
import { FakeEventSource } from './setup';

describe('submission detail', () => {
  it('pending submission (accepted: null) subscribes to SSE and refetches on events', async () => {
    const ds = demoDataset();
    const { fetchSpy } = renderApp('/submissions/sub_demo_pending', ds);
    await screen.findByRole('heading', { level: 1, name: /in-flight/ });
    expect(screen.getAllByText('PENDING').length).toBeGreaterThan(0);
    expect(screen.getByText('pending (accepted = null)')).toBeInTheDocument();
    expect(screen.getByText('Not benchmarked.')).toBeInTheDocument();
    expect(screen.getByText(/No evidence graph has been recorded/)).toBeInTheDocument();
    // Current stage is marked.
    const current = document.querySelector('[aria-current="step"]');
    expect(current?.textContent).toMatch(/BUILT/);

    await waitFor(() => expect(FakeEventSource.instances).toHaveLength(1));
    const es = FakeEventSource.instances[0];
    expect(es.url).toBe('/v1/submissions/sub_demo_pending/events');
    act(() => es.open());
    expect(screen.getByText('live')).toBeInTheDocument();

    // Server advances; an event triggers a refetch of the authoritative record.
    const sub = ds.submissions.find((s) => s.id === 'sub_demo_pending')!;
    sub.stage = 'DECIDED';
    sub.decision = 'REJECTED';
    sub.accepted = false;
    const before = fetchSpy.mock.calls.length;
    act(() => es.emit('stage', '{"stage":"DECIDED","x":"\u001b[31m<b>"}'));
    await waitFor(() => expect(fetchSpy.mock.calls.length).toBeGreaterThan(before), { timeout: 2000 });
    await waitFor(() => expect(screen.getByText('not accepted')).toBeInTheDocument());
    expect(screen.getAllByText('REJECTED').length).toBeGreaterThan(0);
    // Once decided, the stream is closed.
    await waitFor(() => expect(es.readyState).toBe(2));
    // Event payload was rendered sanitised.
    expect(document.body.textContent).not.toContain('\u001b');
  });

  it('decided submissions do not open an event stream', async () => {
    renderApp('/submissions/sub_demo_alpha', demoDataset());
    await screen.findByRole('heading', { level: 1, name: /alpha/ });
    expect(FakeEventSource.instances).toHaveLength(0);
  });

  it('shows the revocation banner with reason, actor and history', async () => {
    renderApp('/submissions/sub_demo_revoked', demoDataset());
    const banner = await screen.findByRole('alert', { name: /admission has been revoked/ });
    expect(banner).toHaveTextContent('axiom allowlist entry withdrawn by governance');
    expect(banner).toHaveTextContent('demo-fixture-governance');
    expect(banner).toHaveTextContent('2026-09-10 12:00:00Z');
    expect(within(banner).getByRole('list')).toHaveTextContent('revoked');
  });

  it('renders gates with reason codes, reused_from links and lineage', async () => {
    renderApp('/submissions/sub_demo_beta', demoDataset());
    await screen.findByRole('heading', { level: 1, name: /faster prover/ });
    const gates = screen.getByRole('heading', { name: 'Gates' }).closest('section')!;
    const reused = within(gates).getAllByRole('link', { name: 'sub_demo_alpha' });
    expect(reused.length).toBeGreaterThan(3);
    expect(reused[0]).toHaveAttribute('href', '/submissions/sub_demo_alpha');
    const lineage = screen.getByRole('list', { name: /Parent lineage/ });
    await waitFor(() => expect(lineage).toHaveTextContent(/DEMO FIXTURE alpha/));
    expect(lineage).toHaveTextContent('PROVER_ONLY');
    expect(screen.getByRole('link', { name: /Download signed report/ })).toHaveAttribute(
      'href',
      '/v1/submissions/sub_demo_beta/report',
    );
  });

  it('draws MISSING evidence edges red-dashed and lists them first', async () => {
    const { container } = renderApp('/submissions/sub_demo_rejected', demoDataset());
    await screen.findByRole('heading', { level: 1, name: /shortcut prover/ });
    expect(screen.getByText(/1 MISSING evidence edge/)).toBeInTheDocument();
    const svg = container.querySelector('svg.graph')!;
    expect(svg.querySelectorAll('path.edge-missing')).toHaveLength(1);
    expect(svg.querySelectorAll('path.edge-checked').length).toBeGreaterThan(0);
    expect(svg.querySelectorAll('path.edge-trusted').length).toBeGreaterThan(0);
    expect(svg.querySelectorAll('path.edge-tested').length).toBeGreaterThan(0);
    expect(within(svg as unknown as HTMLElement).getByText('MISSING')).toBeInTheDocument();
    const table = container.querySelector('details.edge-details table')!;
    const first = table.querySelectorAll('tbody tr')[0];
    expect(first).toHaveClass('row-missing');
    expect(first).toHaveTextContent('No FORMAL_IMPL_CONNECTION evidence.');
    expect(screen.getAllByText('FORBIDDEN_AXIOM').length).toBeGreaterThan(0);
  });

  it('never drops edges with an unknown status (shown as missing)', async () => {
    const ds = demoDataset();
    const s = ds.submissions.find((x) => x.id === 'sub_demo_alpha')!;
    const g = evidenceGraph();
    (g.edges[0] as { status: string }).status = 'proven-trust-me';
    s.evidence_graph = g;
    const { container } = renderApp('/submissions/sub_demo_alpha', ds);
    await screen.findByText(/1 MISSING evidence edge/);
    expect(container.querySelectorAll('svg.graph path.edge-missing')).toHaveLength(1);
    expect(container.textContent).toContain('[invalid status reported]');
  });

  it('shows per-workload performance and assumptions/trusted base', async () => {
    renderApp('/submissions/sub_demo_alpha', demoDataset());
    await screen.findByRole('heading', { level: 1, name: /alpha/ });
    const perf = screen.getByRole('heading', { name: 'Performance' }).closest('section')!;
    expect(within(perf).getByText('transfer-small')).toBeInTheDocument();
    expect(within(perf).getByText('transfer-batch')).toBeInTheDocument();
    expect(within(perf).getAllByText('2.45×').length).toBe(2);
    const trust = screen.getByRole('heading', { name: /Assumptions and trusted base/ }).closest('section')!;
    expect(trust).toHaveTextContent('sha256_collision_resistant');
    expect(trust).toHaveTextContent('Lean 4 kernel');
    expect(screen.getByText('Verify artifact')).toBeInTheDocument();
  });

  it('labels DEMO submissions unmistakably', async () => {
    renderApp('/submissions/sub_demo_plumbing', demoDataset());
    await screen.findByRole('heading', { level: 1, name: /plumbing run/ });
    expect(screen.getByText(/DEMO result: produced for plumbing demonstration/)).toBeInTheDocument();
    expect(screen.getAllByText('DEMO · NOT RANKED').length).toBeGreaterThan(0);
    // The mock banner is visible whenever fixtures are served.
    expect(screen.getByText(/MOCK API · demo fixtures only/)).toBeInTheDocument();
  });

  it('rejects malformed ids without calling the API', async () => {
    const { fetchSpy } = renderApp('/submissions/..%2F..%2Fadmin', demoDataset());
    expect(await screen.findByText('Invalid submission id')).toBeInTheDocument();
    expect(fetchSpy).not.toHaveBeenCalled();
  });
});

describe('stage progress after a decision', () => {
  it('does not show stages that never ran as complete (cancel / fail-fast)', async () => {
    const ds = demoDataset();
    const s = ds.submissions.find((x) => x.id === 'sub_demo_rejected')!;
    renderApp('/submissions/sub_demo_rejected', ds);
    await screen.findByRole('heading', { level: 1, name: /shortcut prover/ });
    const items = within(screen.getByRole('list', { name: 'Pipeline stages' })).getAllByRole('listitem');
    const cls = items.map((li) => li.className.replace('stage ', ''));
    // PKG/BUILD passed, AXIOM_AUDIT failed in FORMAL_CHECKED, later stages never ran.
    expect(cls).toEqual(['done', 'done', 'done', 'failed', 'not_run', 'not_run', 'done']);
    expect(s.stage).toBe('DECIDED');
  });
});

describe('verified surface: verify route', () => {
  it('shows verify route, bytecode digest and verifier model', async () => {
    const ds = demoDataset();
    const s = ds.submissions.find((x) => x.id === 'sub_demo_alpha')!;
    s.verified_surface = {
      ...s.verified_surface!,
      verify_route: 'npai-v1',
      verifier_bytecode: `sha256:${'b'.repeat(64)}`,
      verifier_model: 'Candidate.Model.verify',
      verifier_model_module: 'Candidate.Model',
    };
    renderApp('/submissions/sub_demo_alpha', ds);
    await screen.findByRole('heading', { level: 1, name: /alpha/ });
    const dig = screen.getByRole('heading', { name: 'Digests' }).closest('section')!;
    expect(within(dig).getByText('npai-v1')).toBeInTheDocument();
    expect(within(dig).getByText(/approved NPAI interpreter/)).toBeInTheDocument();
    expect(within(dig).getByText(`sha256:${'b'.repeat(64)}`)).toBeInTheDocument();
    expect(within(dig).getByText('Candidate.Model.verify')).toBeInTheDocument();
    expect(within(dig).getByText('Candidate.Model')).toBeInTheDocument();
  });

  it('flags an unknown verify route', async () => {
    const ds = demoDataset();
    const s = ds.submissions.find((x) => x.id === 'sub_demo_alpha')!;
    s.verified_surface = { ...s.verified_surface!, verify_route: 'trust-me' as never };
    renderApp('/submissions/sub_demo_alpha', ds);
    expect(await screen.findByText(/unknown route/)).toBeInTheDocument();
  });
});
