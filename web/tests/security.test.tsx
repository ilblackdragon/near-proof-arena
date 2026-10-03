import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { screen, waitFor, within } from '@testing-library/react';
import { describe, expect, it } from 'vitest';
import { challengeRecord, demoDataset, makeDefinition, makeSub, type Dataset } from '../mock/fixtures';
import { renderApp } from './helpers';

const SCRIPT = '<script>window.__pwned=1</script>';
const IMG = '<img src=x onerror="window.__pwned=2">';
const RTL = 'safe‮exe.txt‬';
const ANSI = '\u001b[31mRED\u001b[0m\u001b]8;;http://evil\u0007link\u001b]8;;\u0007';

function hostileDataset(): Dataset {
  const c = challengeRecord(
    makeDefinition({
      name: `DEMO FIXTURE ${SCRIPT}`,
      tier: 'formal',
      excludes: [IMG, RTL],
      restrictions: [{ id: ANSI, text: SCRIPT }],
    }),
  );
  const base = {
    challenge_id: c.id,
    candidate_name: `DEMO FIXTURE ${SCRIPT}`,
    agent: RTL,
    backend_family: IMG,
  };
  const s1 = makeSub({
    id: 'sub_hostile1',
    ...base,
    score_milli: 150_000,
    gates: [
      {
        gate: 'AXIOM_AUDIT',
        mandatory: true,
        status: 'PASS',
        reason_codes: [],
        summary: `${IMG} ${ANSI} ${RTL}`,
        evidence: [{ label: SCRIPT, digest: `sha256:${'a'.repeat(64)}`, public: true }],
        reused_from: 'javascript:alert(1)',
      },
    ],
    build: { [SCRIPT]: IMG, note: ANSI },
    logs: [{ name: IMG, text: `${ANSI}\n${SCRIPT}\n${RTL}\r\nbell\u0007` }],
    evidence_graph: {
      nodes: [
        { id: 'a', kind: 'theorem', label: SCRIPT, digest: null },
        { id: 'b', kind: 'artifact', label: `${IMG}${RTL}`, digest: null },
      ],
      edges: [{ from: 'a', to: 'b', kind: IMG, status: 'missing', evidence: [], note: ANSI }],
    },
    revoked: { reason: `${SCRIPT}${RTL}`, revoked_at: '2026-09-09T00:00:00Z', revoked_by: IMG },
    parent: 'sub_hostile2',
    change_class: 'PROVER_ONLY',
  });
  const s2 = makeSub({ id: 'sub_hostile2', ...base, tier: 'demo', parent: '"><script>x</script>' });
  return { challenges: [c], submissions: [s1, s2] };
}

function assertInert(root: HTMLElement) {
  // No element was created from any payload.
  expect(root.querySelectorAll('script')).toHaveLength(0);
  expect(root.querySelectorAll('img')).toHaveLength(0);
  expect(root.querySelectorAll('[onerror],[onload],[onclick]')).toHaveLength(0);
  expect((window as unknown as { __pwned?: number }).__pwned).toBeUndefined();
  const text = root.textContent ?? '';
  // No raw escape / bidi control characters reach the DOM.
  expect(text).not.toMatch(/[\u001b\u009b‪-‮⁦-⁩\u0007]/);
  // Every link is internal (or the API report path).
  for (const a of Array.from(root.querySelectorAll('a[href]'))) {
    const href = a.getAttribute('href')!;
    expect(href === '#main' || href.startsWith('/'), href).toBe(true);
    expect(href.startsWith('//')).toBe(false);
  }
}

describe('hostile candidate strings render inert', () => {
  it('submission detail page', async () => {
    const { container } = renderApp('/submissions/sub_hostile1', hostileDataset());
    await screen.findByRole('heading', { level: 1, name: /DEMO FIXTURE <script>/ });
    await waitFor(() => expect(screen.getAllByText(/sub_hostile2/).length).toBeGreaterThan(0));
    // Payloads are visible as literal text.
    expect(container.textContent).toContain(SCRIPT);
    expect(container.textContent).toContain('<img src=x onerror=');
    // RTL override is shown as a visible marker.
    expect(container.textContent).toContain('safe[U+202E]exe.txt[U+202C]');
    // ANSI stripped from logs and summaries; OSC-8 hyperlink did not become a link.
    expect(container.textContent).toContain('REDlink');
    expect(container.querySelector('a[href*="evil"]')).toBeNull();
    // reused_from with javascript: is rendered as inert text, never a link.
    expect(container.textContent).toContain('javascript:alert(1)');
    expect(container.querySelector('a[href^="javascript"]')).toBeNull();
    // Malformed parent id in lineage is not linked.
    expect(container.querySelector('a[href*="script"]')).toBeNull();
    // Revocation banner text is inert as well.
    expect(screen.getByText(/admission has been revoked/)).toBeInTheDocument();
    assertInert(container);
  });

  it('challenge page + leaderboard', async () => {
    const { container } = renderApp(`/challenges/${hostileDataset().challenges[0].id}`, hostileDataset());
    await screen.findByText(/What an admitted proof does NOT establish/);
    await screen.findByRole('heading', { name: /Official ranking/ });
    await waitFor(() => expect(container.querySelector('table.board')).not.toBeNull());
    expect(container.textContent).toContain(SCRIPT);
    assertInert(container);
  });

  it('submissions list and compare', async () => {
    const ds = hostileDataset();
    const a = renderApp('/submissions', ds);
    await waitFor(() => expect(a.container.querySelectorAll('tbody tr').length).toBe(2));
    assertInert(a.container);
    a.unmount();
    const b = renderApp('/compare?a=sub_hostile1&b=sub_hostile2', ds);
    await waitFor(() => expect(b.container.querySelector('table.compare')).not.toBeNull());
    await waitFor(() => expect(within(b.container.querySelector('table.compare')!).getAllByText(/DEMO FIXTURE <script>/).length).toBe(2));
    assertInert(b.container);
  });

  it('the demo dataset (incl. its hostile fixture) renders inert everywhere', async () => {
    const ds = demoDataset();
    const r = renderApp('/submissions/sub_demo_hostile', ds);
    await screen.findByText(/prove\.stderr <b>bold<\/b>/);
    assertInert(r.container);
  });
});

describe('source audit', () => {
  const files: string[] = [];
  const walk = (d: string) => {
    for (const f of readdirSync(d)) {
      const p = join(d, f);
      if (statSync(p).isDirectory()) walk(p);
      else if (/\.(ts|tsx)$/.test(p)) files.push(p);
    }
  };
  walk(join(__dirname, '../src'));

  it('never uses raw-HTML or dynamic-code sinks', () => {
    const banned = [
      /dangerouslySetInnerHTML/,
      /\.innerHTML/,
      /\.outerHTML/,
      /insertAdjacentHTML/,
      /document\.write/,
      /\beval\(/,
      /new Function\(/,
      /createContextualFragment/,
      /DOMParser/,
      /srcdoc/i,
      /<iframe/i,
      /<img\b/i,
      /window\.open\(/,
    ];
    for (const f of files) {
      const src = readFileSync(f, 'utf8');
      for (const re of banned) expect(re.test(src), `${f} matches ${re}`).toBe(false);
    }
  });

  it('builds hrefs only from internal paths', () => {
    for (const f of files) {
      const src = readFileSync(f, 'utf8');
      for (const m of src.matchAll(/href=\{([^}]*)\}/g)) {
        expect(['reportUrl(s.id)'], `${f}: href={${m[1]}}`).toContain(m[1]);
      }
    }
  });

  it('does not import mock fixtures from application code', () => {
    for (const f of files) {
      expect(/from ['"][./]*mock\//.test(readFileSync(f, 'utf8')), f).toBe(false);
    }
  });
});
