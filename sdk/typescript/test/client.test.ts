import { test } from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  ArenaClient,
  AuthError,
  NotFoundError,
  RejectedError,
  SseParser,
  UnavailableError,
  defaultIdempotencyKey,
  packageDigest,
} from "../src/index.ts";
import type { SubmissionView } from "../src/index.ts";

const CHL = "chl_0123456789abcdef0123456789abcdef";

function view(stage: string, decision: string | null = null, extra: Record<string, unknown> = {}): SubmissionView {
  return {
    id: "sub_1", challenge_id: CHL, agent: "a", candidate_name: "toy", backend_family: "toy",
    parent: null, tier: "formal", package_digest: "sha256:" + "0".repeat(64),
    stage: stage as SubmissionView["stage"], decision: decision as SubmissionView["decision"],
    accepted: decision === null ? null : decision === "ADMITTED", score_milli: null,
    change_class: null, gates: [], reason_codes: [], benchmark: null, evidence_graph: null,
    revoked: null, created_at: "t", updated_at: "t", ...extra,
  } as SubmissionView;
}

type Handler = (url: URL, init: RequestInit) => Response | Promise<Response>;
function mockFetch(h: Handler): { fetch: typeof fetch; calls: Array<{ url: URL; init: RequestInit }> } {
  const calls: Array<{ url: URL; init: RequestInit }> = [];
  const f = (async (input: RequestInfo | URL, init: RequestInit = {}) => {
    const url = new URL(String(input));
    calls.push({ url, init });
    return h(url, init);
  }) as typeof fetch;
  return { fetch: f, calls };
}
const json = (v: unknown, status = 200) => new Response(JSON.stringify(v), { status, headers: { "content-type": "application/json" } });
const hdr = (init: RequestInit, k: string) => (init.headers as Record<string, string>)[k];
const noSleep = async () => {};

test("submitArchive uploads then creates the submission", async () => {
  const data = new TextEncoder().encode("tar-bytes");
  const m = mockFetch(async (url, init) => {
    assert.equal(hdr(init, "Authorization"), "Bearer tok");
    if (url.pathname === "/v1/uploads") {
      assert.equal(hdr(init, "Content-Type"), "application/x-tar");
      return json({ upload_id: "u1", digest: await packageDigest(new Uint8Array(init.body as ArrayBuffer)) });
    }
    if (url.pathname === "/v1/submissions") return json(view("RECEIVED", null, { extra: 1 }), 201);
    return json({}, 404);
  });
  const c = new ArenaClient({ baseUrl: "http://arena.test/", token: "tok", fetch: m.fetch });
  const sub = await c.submitArchive(CHL, data, { parent: "sub_0" });
  assert.equal(sub.id, "sub_1");
  assert.equal((sub as unknown as Record<string, unknown>)["extra"], 1);
  const body = JSON.parse(m.calls[1]!.init.body as string);
  const digest = "sha256:" + createHash("sha256").update(data).digest("hex");
  assert.deepEqual(body, {
    challenge_id: CHL,
    upload_digest: digest,
    idempotency_key: await defaultIdempotencyKey(CHL, digest, "sub_0"),
    parent: "sub_0",
  });
});

test("idempotency key derivation matches the CLI", async () => {
  const d = "sha256:" + "a".repeat(64);
  const expect = "arena-cli-" + createHash("sha256").update(`${CHL}\n${d}\n`).digest("hex").slice(0, 32);
  assert.equal(await defaultIdempotencyKey(CHL, d), expect);
});

test("upload digest mismatch is detected", async () => {
  const m = mockFetch(() => json({ upload_id: "u", digest: "sha256:" + "f".repeat(64) }));
  const c = new ArenaClient({ baseUrl: "http://x", token: "t", fetch: m.fetch });
  await assert.rejects(c.upload(new Uint8Array([1])), UnavailableError);
});

test("HTTP errors map to typed errors", async () => {
  for (const [status, cls, code] of [[401, AuthError, 4], [403, AuthError, 4], [404, NotFoundError, 7], [422, RejectedError, 6], [503, UnavailableError, 5], [429, UnavailableError, 5]] as const) {
    const c = new ArenaClient({ baseUrl: "http://x", fetch: mockFetch(() => new Response("nope", { status })).fetch });
    await assert.rejects(c.submission("sub_1"), (e: unknown) => e instanceof cls && (e as AuthError).exitCode === code && (e as AuthError).status === status);
  }
  const c = new ArenaClient({ baseUrl: "http://x", fetch: (async () => { throw new TypeError("fetch failed"); }) as typeof fetch });
  await assert.rejects(c.challenges(), UnavailableError);
});

test("ids are validated locally", async () => {
  const c = new ArenaClient({ baseUrl: "http://x", fetch: mockFetch(() => json({})).fetch });
  await assert.rejects(c.submission("../admin"), TypeError);
  await assert.rejects(c.leaderboard("sub_1"), TypeError);
});

test("list endpoints accept bare or wrapped arrays", async () => {
  const m = mockFetch((url) => {
    if (url.pathname.startsWith("/v1/leaderboards/")) return json({ entries: [{ rank: 1 }] });
    if (url.pathname === "/v1/submissions") {
      assert.equal(url.searchParams.get("challenge_id"), CHL);
      return json([view("BUILT")]);
    }
    return json([{ id: CHL }]);
  });
  const c = new ArenaClient({ baseUrl: "http://x", fetch: m.fetch });
  assert.deepEqual(await c.leaderboard(CHL), [{ rank: 1 }]);
  assert.deepEqual(await c.challenges(), [{ id: CHL }]);
  assert.equal((await c.submissions({ challengeId: CHL }))[0]!.stage, "BUILT");
});

test("SSE parser handles chunk boundaries, CRLF, comments, ids", () => {
  const p = new SseParser();
  const evs = [
    ...p.push(": hi\r\nevent: st"),
    ...p.push("age\r\nid: 7\r\ndata: {\"a\":\r"),
    ...p.push("\ndata: 1}\r\n\r\ndata: x\n\n"),
  ];
  assert.equal(evs.length, 2);
  assert.deepEqual(evs[0], { event: "stage", data: '{"a":\n1}', id: "7" });
  assert.deepEqual(evs[1], { event: "message", data: "x", id: "7" });
});

function streamOf(chunks: string[]): ReadableStream<Uint8Array> {
  const enc = new TextEncoder();
  return new ReadableStream({
    start(ctrl) {
      for (const c of chunks) ctrl.enqueue(enc.encode(c));
      ctrl.close();
    },
  });
}

test("events() streams via fetch body", async () => {
  const m = mockFetch((_u, init) => {
    assert.equal(hdr(init, "Accept"), "text/event-stream");
    assert.equal(hdr(init, "Last-Event-ID"), "3");
    return new Response(streamOf(["event: stage\nda", "ta: {}\nid: 4\n\n"]), { headers: { "content-type": "text/event-stream" } });
  });
  const c = new ArenaClient({ baseUrl: "http://x", fetch: m.fetch });
  const evs = [];
  for await (const e of c.events("sub_1", { lastEventId: "3" })) evs.push(e);
  assert.deepEqual(evs, [{ event: "stage", data: "{}", id: "4" }]);
});

test("watch() follows SSE until decided", async () => {
  let n = 0;
  const m = mockFetch((url) => {
    if (url.pathname.endsWith("/events")) return new Response(streamOf(["data: a\n\n", "data: b\n\n"]));
    n++;
    if (n === 1) return json(view("VALIDATED"));
    if (n === 2) return json(view("BUILT"));
    return json(view("DECIDED", "REJECTED", { reason_codes: ["CLAIM_MISMATCH"] }));
  });
  const c = new ArenaClient({ baseUrl: "http://x", fetch: m.fetch, sleep: noSleep });
  const stages = [];
  for await (const v of c.watch("sub_1")) stages.push(v.stage);
  assert.deepEqual(stages, ["VALIDATED", "BUILT", "DECIDED"]);
});

test("wait() falls back to polling when SSE is unavailable", async () => {
  let n = 0;
  const m = mockFetch((url) => {
    if (url.pathname.endsWith("/events")) return new Response("", { status: 404 });
    n++;
    return json(n > 4 ? view("DECIDED", "ADMITTED") : view("BUILT"));
  });
  const c = new ArenaClient({ baseUrl: "http://x", fetch: m.fetch, sleep: noSleep });
  assert.equal((await c.wait("sub_1")).decision, "ADMITTED");
});

test("generated types are up to date", () => {
  execFileSync(process.execPath, [new URL("../scripts/gen-types.mjs", import.meta.url).pathname, "--check"]);
});
