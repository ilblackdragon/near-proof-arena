import { AuthError, UnavailableError, errorForStatus } from "./errors.ts";
import { parseSseStream, type SseEvent } from "./sse.ts";
import type { ChallengeDefinition, LeaderboardEntry, SubmissionView } from "./types.ts";

export const DEFAULT_URL = "http://127.0.0.1:8471";

/** Terminal decisions; `decision` is `null` while a submission is pending. */
export const DECISIONS = ["ADMITTED", "REJECTED", "INCONCLUSIVE", "INFRA_ERROR", "CANCELLED"] as const;

export interface UploadResult {
  upload_id: string;
  digest: string;
}

export interface ClientOptions {
  /** Defaults to `process.env.ARENA_URL` or `http://127.0.0.1:8471`. */
  baseUrl?: string;
  /** Defaults to `process.env.ARENA_TOKEN`. */
  token?: string;
  /** Injectable `fetch` (tests, proxies). Defaults to `globalThis.fetch`. */
  fetch?: typeof fetch;
  /** Injectable sleep for watch back-off (tests). */
  sleep?: (ms: number) => Promise<void>;
}

export interface WatchOptions {
  timeoutMs?: number;
  pollIntervalMs?: number;
  signal?: AbortSignal;
}

const ID = /^[A-Za-z0-9_-]{1,128}$/;
function checkId(v: string, prefix: string): string {
  if (!v.startsWith(prefix) || !ID.test(v)) throw new TypeError(`invalid id ${JSON.stringify(v)} (expected ${prefix}...)`);
  return v;
}

function env(name: string): string | undefined {
  const p = (globalThis as { process?: { env?: Record<string, string | undefined> } }).process;
  const v = p?.env?.[name];
  return v ? v : undefined;
}

function hex(buf: ArrayBuffer): string {
  return [...new Uint8Array(buf)].map((b) => b.toString(16).padStart(2, "0")).join("");
}

/** `sha256:<hex>` of the exact uploaded bytes (the `upload_digest`). */
export async function packageDigest(data: Uint8Array): Promise<string> {
  return "sha256:" + hex(await crypto.subtle.digest("SHA-256", data as Uint8Array<ArrayBuffer>));
}

/** Same derivation as the `arena` CLI: identical retries never duplicate a submission. */
export async function defaultIdempotencyKey(challengeId: string, digest: string, parent?: string | null): Promise<string> {
  const h = new TextEncoder().encode(`${challengeId}\n${digest}\n${parent ?? ""}`);
  return "arena-cli-" + hex(await crypto.subtle.digest("SHA-256", h)).slice(0, 32);
}

function listOf<T>(v: unknown, ...keys: string[]): T[] {
  if (Array.isArray(v)) return v as T[];
  if (v && typeof v === "object") {
    for (const k of keys) {
      const x = (v as Record<string, unknown>)[k];
      if (Array.isArray(x)) return x as T[];
    }
  }
  return [];
}

/** fetch-based client for the NEAR Proof Arena API v1. Responses are the server's objects verbatim. */
export class ArenaClient {
  readonly baseUrl: string;
  readonly token: string | undefined;
  #fetch: typeof fetch;
  #sleep: (ms: number) => Promise<void>;

  constructor(opts: ClientOptions = {}) {
    this.baseUrl = (opts.baseUrl ?? env("ARENA_URL") ?? DEFAULT_URL).replace(/\/+$/, "");
    this.token = opts.token ?? env("ARENA_TOKEN");
    this.#fetch = opts.fetch ?? globalThis.fetch.bind(globalThis);
    this.#sleep = opts.sleep ?? ((ms) => new Promise((r) => setTimeout(r, ms)));
  }

  #headers(extra: Record<string, string> = {}): Record<string, string> {
    const h: Record<string, string> = { ...extra };
    if (this.token) h["Authorization"] = `Bearer ${this.token}`;
    return h;
  }

  async #request(method: string, path: string, init: { body?: BodyInit; headers?: Record<string, string>; signal?: AbortSignal } = {}): Promise<Response> {
    let r: Response;
    try {
      r = await this.#fetch(this.baseUrl + path, {
        method,
        headers: this.#headers(init.headers),
        ...(init.body !== undefined ? { body: init.body } : {}),
        ...(init.signal ? { signal: init.signal } : {}),
      });
    } catch (e) {
      if (init.signal?.aborted) throw e;
      throw new UnavailableError(`cannot reach arena server: ${String(e)}`);
    }
    if (r.status >= 400) throw errorForStatus(r.status, await r.text().catch(() => ""));
    return r;
  }

  async #json<T>(method: string, path: string, init: { body?: BodyInit; headers?: Record<string, string> } = {}): Promise<T> {
    const r = await this.#request(method, path, { headers: { Accept: "application/json", ...init.headers }, ...(init.body !== undefined ? { body: init.body } : {}) });
    const text = await r.text();
    try {
      return JSON.parse(text) as T;
    } catch (e) {
      throw new UnavailableError(`server sent invalid JSON: ${String(e)}`, r.status, text);
    }
  }

  async challenges(): Promise<unknown[]> {
    return listOf(await this.#json("GET", "/v1/challenges"), "challenges");
  }

  /** `GET /v1/challenges/{id}`: a `ChallengeDefinition` or `{id, definition}` envelope. */
  async challenge(id: string): Promise<unknown> {
    return this.#json("GET", `/v1/challenges/${checkId(id, "chl_")}`);
  }

  async challengeDefinition(id: string): Promise<ChallengeDefinition> {
    const v = (await this.challenge(id)) as Record<string, unknown>;
    return (v["definition"] ?? v) as ChallengeDefinition;
  }

  /** `POST /v1/uploads` with the raw package archive (from `arena pack`). */
  async upload(data: Uint8Array): Promise<UploadResult> {
    const res = await this.#json<UploadResult>("POST", "/v1/uploads", {
      body: data as Uint8Array<ArrayBuffer>,
      headers: { "Content-Type": "application/x-tar" },
    });
    const want = await packageDigest(data);
    if (res.digest !== want) throw new UnavailableError(`server reported digest ${JSON.stringify(res.digest)}, expected ${want}`);
    return res;
  }

  async createSubmission(challengeId: string, uploadDigest: string, idempotencyKey: string, parent?: string | null): Promise<SubmissionView> {
    const body: Record<string, string> = {
      challenge_id: checkId(challengeId, "chl_"),
      upload_digest: uploadDigest,
      idempotency_key: idempotencyKey,
    };
    if (parent != null) body["parent"] = checkId(parent, "sub_");
    return this.#json("POST", "/v1/submissions", { body: JSON.stringify(body), headers: { "Content-Type": "application/json" } });
  }

  /** Upload and submit in one step. */
  async submitArchive(challengeId: string, data: Uint8Array, opts: { parent?: string | null; idempotencyKey?: string } = {}): Promise<SubmissionView> {
    const up = await this.upload(data);
    const key = opts.idempotencyKey ?? (await defaultIdempotencyKey(challengeId, up.digest, opts.parent));
    return this.createSubmission(challengeId, up.digest, key, opts.parent);
  }

  async submission(id: string): Promise<SubmissionView> {
    return this.#json("GET", `/v1/submissions/${checkId(id, "sub_")}`);
  }

  async submissions(filter: { challengeId?: string; agent?: string } = {}): Promise<SubmissionView[]> {
    const q = new URLSearchParams();
    if (filter.challengeId) q.set("challenge_id", filter.challengeId);
    if (filter.agent) q.set("agent", filter.agent);
    const qs = q.toString();
    return listOf(await this.#json("GET", `/v1/submissions${qs ? "?" + qs : ""}`), "submissions");
  }

  /** Signed JSON report. */
  async report(id: string): Promise<unknown> {
    return this.#json("GET", `/v1/submissions/${checkId(id, "sub_")}/report`);
  }

  async cancel(id: string): Promise<unknown> {
    return this.#json("POST", `/v1/submissions/${checkId(id, "sub_")}/cancel`, { body: "{}", headers: { "Content-Type": "application/json" } });
  }

  async leaderboard(challengeId: string): Promise<LeaderboardEntry[]> {
    return listOf(await this.#json("GET", `/v1/leaderboards/${checkId(challengeId, "chl_")}`), "entries", "leaderboard");
  }

  /** Server-Sent Events of a submission, until the server closes the stream. */
  async *events(id: string, opts: { lastEventId?: string; signal?: AbortSignal } = {}): AsyncGenerator<SseEvent> {
    const headers: Record<string, string> = { Accept: "text/event-stream" };
    if (opts.lastEventId) headers["Last-Event-ID"] = opts.lastEventId;
    const r = await this.#request("GET", `/v1/submissions/${checkId(id, "sub_")}/events`, { headers, ...(opts.signal ? { signal: opts.signal } : {}) });
    if (!r.body) return;
    try {
      yield* parseSseStream(r.body);
    } catch (e) {
      if (opts.signal?.aborted) throw e;
      throw new UnavailableError(`event stream: ${String(e)}`);
    }
  }

  /**
   * Yield the authoritative `SubmissionView` whenever it changes, ending with
   * the decided view. SSE is used as a change signal; falls back to polling.
   */
  async *watch(id: string, opts: WatchOptions = {}): AsyncGenerator<SubmissionView> {
    const start = Date.now();
    const poll = opts.pollIntervalMs ?? 2000;
    let last = "";
    let lastId: string | undefined;
    let sseFailures = 0;
    const expired = () => opts.timeoutMs !== undefined && Date.now() - start > opts.timeoutMs;
    const fresh = async (): Promise<SubmissionView | undefined> => {
      const v = await this.submission(id);
      const s = JSON.stringify(v);
      if (s === last) return undefined;
      last = s;
      return v;
    };
    for (;;) {
      const v = await fresh();
      if (v) {
        yield v;
        if (v.decision != null) return;
      }
      if (expired()) throw new UnavailableError(`timed out waiting for ${id}`);
      if (sseFailures < 3) {
        try {
          for await (const ev of this.events(id, { ...(lastId ? { lastEventId: lastId } : {}), ...(opts.signal ? { signal: opts.signal } : {}) })) {
            if (ev.id) lastId = ev.id;
            const v2 = await fresh();
            if (v2) {
              yield v2;
              if (v2.decision != null) return;
            }
            if (expired()) throw new UnavailableError(`timed out waiting for ${id}`);
          }
        } catch (e) {
          if (e instanceof AuthError || opts.signal?.aborted || expired()) throw e;
          sseFailures++;
        }
      }
      await this.#sleep(sseFailures >= 3 ? poll : 300);
    }
  }

  /** Resolve with the decided `SubmissionView`. */
  async wait(id: string, opts: WatchOptions = {}): Promise<SubmissionView> {
    let v: SubmissionView | undefined;
    for await (v of this.watch(id, opts));
    if (!v) throw new UnavailableError("no submission view received");
    return v;
  }
}
