import { describe, expect, it, vi } from 'vitest';
import { getLeaderboard, getSubmission, listChallenges, listSubmissions, ApiError } from '../src/api/client';
import { canonicalJson } from '../src/lib/jcs';
import { demoDataset } from '../mock/fixtures';

const respond = (body: unknown, status = 200) =>
  vi.stubGlobal('fetch', vi.fn(async () => new Response(typeof body === 'string' ? body : JSON.stringify(body), { status })));

describe('api client', () => {
  it('expects bare arrays; drops malformed records', async () => {
    const ds = demoDataset();
    respond([ds.challenges[0], { id: 'chl_bad' }, { ...ds.challenges[1], signature: 7 }, 'junk']);
    expect(await listChallenges()).toHaveLength(1);
    respond([ds.submissions[0], { id: 'not-a-sub' }]);
    expect(await listSubmissions({})).toHaveLength(1);
    respond([{ submission_id: 'sub_x' }]);
    expect(await getLeaderboard(ds.challenges[0].id)).toHaveLength(0);
    respond({ challenges: [ds.challenges[0]] });
    await expect(listChallenges()).rejects.toThrow(/expected an array/);
  });

  it('rejects mismatched ids, invalid JSON and oversized bodies', async () => {
    const ds = demoDataset();
    respond(ds.submissions[1]);
    await expect(getSubmission('sub_demo_ref')).rejects.toThrow(/does not match/);
    respond('{not json');
    await expect(listChallenges()).rejects.toThrow(/invalid JSON/);
    respond('x'.repeat(8 * 1024 * 1024 + 1));
    await expect(listChallenges()).rejects.toThrow(/too large/);
    respond({}, 500);
    await expect(listChallenges()).rejects.toBeInstanceOf(ApiError);
  });

  it('only issues credential-less GETs to /v1 paths', async () => {
    const f = vi.fn(async () => new Response('[]'));
    vi.stubGlobal('fetch', f);
    await listSubmissions({ agent: 'a&b=c' });
    const [url, init] = f.mock.calls[0] as unknown as [string, RequestInit];
    expect(url).toBe('/v1/submissions?agent=a%26b%3Dc');
    expect(init.method).toBe('GET');
    expect(init.credentials).toBe('omit');
  });
});

describe('canonical JSON', () => {
  it('sorts keys, no whitespace, rejects floats', () => {
    expect(canonicalJson({ b: 1, a: [true, null, 'x'] })).toBe('{"a":[true,null,"x"],"b":1}');
    expect(() => canonicalJson({ a: 1.5 })).toThrow();
  });
});
