/**
 * Framework-agnostic fixture router for the read-only API surface. Used by
 * the Vite dev middleware (ARENA_MOCK=1) and by the tests' fetch stub.
 * Every response carries `X-Arena-Mock: demo-fixtures` so the UI shows a
 * persistent DEMO banner.
 */
import { leaderboardFor, type Dataset } from './fixtures';

export interface MockResponse {
  status: number;
  body: unknown;
}

export const MOCK_HEADER = 'x-arena-mock';

export function route(ds: Dataset, method: string, rawUrl: string): MockResponse | 'sse' | null {
  const url = new URL(rawUrl, 'http://mock.invalid');
  const p = url.pathname;
  if (!p.startsWith('/v1/')) return null;
  if (method !== 'GET') return { status: 405, body: { error: 'read-only mock' } };
  let m: RegExpMatchArray | null;
  if (p === '/v1/challenges') return { status: 200, body: ds.challenges };
  if ((m = p.match(/^\/v1\/challenges\/([^/]+)$/))) {
    const c = ds.challenges.find((x) => x.id === decodeURIComponent(m![1]));
    return c ? { status: 200, body: c } : { status: 404, body: { error: 'not found' } };
  }
  if ((m = p.match(/^\/v1\/leaderboards\/([^/]+)$/))) {
    const lb = leaderboardFor(ds, decodeURIComponent(m[1]));
    return lb ? { status: 200, body: { challenge_id: m[1], entries: lb } } : { status: 404, body: { error: 'not found' } };
  }
  if (p === '/v1/submissions') {
    const ch = url.searchParams.get('challenge_id');
    const ag = url.searchParams.get('agent');
    return {
      status: 200,
      body: ds.submissions.filter((s) => (!ch || s.challenge_id === ch) && (!ag || s.agent === ag)),
    };
  }
  if ((m = p.match(/^\/v1\/submissions\/([^/]+)\/events$/))) return 'sse';
  if ((m = p.match(/^\/v1\/submissions\/([^/]+)\/report$/))) {
    const s = ds.submissions.find((x) => x.id === decodeURIComponent(m![1]));
    return s
      ? { status: 200, body: { demo_fixture: true, note: 'DEMO FIXTURE — unsigned mock report', submission: s } }
      : { status: 404, body: { error: 'not found' } };
  }
  if ((m = p.match(/^\/v1\/submissions\/([^/]+)$/))) {
    const s = ds.submissions.find((x) => x.id === decodeURIComponent(m![1]));
    return s ? { status: 200, body: s } : { status: 404, body: { error: 'not found' } };
  }
  return { status: 404, body: { error: 'not found' } };
}

/** A `fetch` implementation backed by a dataset (tests). */
export function mockFetch(ds: Dataset): typeof fetch {
  return (async (input: RequestInfo | URL, init?: RequestInit) => {
    const url = typeof input === 'string' ? input : input instanceof URL ? input.href : input.url;
    const r = route(ds, init?.method ?? 'GET', url);
    if (r === null || r === 'sse') return new Response('not found', { status: 404 });
    return new Response(JSON.stringify(r.body), {
      status: r.status,
      headers: { 'content-type': 'application/json', [MOCK_HEADER]: 'demo-fixtures' },
    });
  }) as typeof fetch;
}
