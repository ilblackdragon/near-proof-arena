/**
 * Read-only API client. Every response is size-bounded, parsed as JSON and
 * shape-checked before reaching components; malformed records are dropped
 * rather than rendered half-formed. The client never sends credentials and
 * never issues non-GET requests.
 */
import { apiUrl } from '../config';
import { isChallengeId, isSubmissionId } from '../lib/ids';
import type {
  BoardEntry,
  ChallengeDefinition,
  ChallengeRecord,
  SubmissionDetail,
  SubmissionView,
} from './types';

/** Upper bound on any JSON response body (bytes, approx. via UTF-16 length). */
export const MAX_RESPONSE_CHARS = 8 * 1024 * 1024;
/** Upper bound on list lengths we will render. */
export const MAX_LIST = 2000;

export class ApiError extends Error {
  constructor(
    message: string,
    readonly status: number | null,
  ) {
    super(message);
  }
}

/** Set when the dev fixture server answers (header `X-Arena-Mock`). */
let mockSeen = false;
const mockListeners = new Set<() => void>();
export const isMockApi = () => mockSeen;
export function onMockDetected(fn: () => void): () => void {
  mockListeners.add(fn);
  return () => mockListeners.delete(fn);
}

async function getJson(path: string, signal?: AbortSignal): Promise<unknown> {
  let res: Response;
  try {
    res = await fetch(apiUrl(path), {
      method: 'GET',
      credentials: 'omit',
      headers: { Accept: 'application/json' },
      signal,
    });
  } catch (e) {
    if ((e as Error)?.name === 'AbortError') throw e;
    throw new ApiError('Network error contacting the arena API', null);
  }
  if (res.headers.get('x-arena-mock') && !mockSeen) {
    mockSeen = true;
    mockListeners.forEach((f) => f());
  }
  if (!res.ok) {
    throw new ApiError(res.status === 404 ? 'Not found' : `API returned HTTP ${res.status}`, res.status);
  }
  const len = Number(res.headers.get('content-length') ?? '0');
  if (len > MAX_RESPONSE_CHARS) throw new ApiError('Response too large', res.status);
  const text = await res.text();
  if (text.length > MAX_RESPONSE_CHARS) throw new ApiError('Response too large', res.status);
  try {
    return JSON.parse(text);
  } catch {
    throw new ApiError('API returned invalid JSON', res.status);
  }
}

const isObj = (v: unknown): v is Record<string, unknown> =>
  typeof v === 'object' && v !== null && !Array.isArray(v);
const isStr = (v: unknown): v is string => typeof v === 'string';

/** List endpoints return bare JSON arrays (server/openapi.json). */
function asList(v: unknown, what: string): unknown[] {
  if (!Array.isArray(v)) throw new ApiError(`Unexpected response shape (expected an array of ${what})`, null);
  return v.slice(0, MAX_LIST);
}

function looksLikeDefinition(v: unknown): v is ChallengeDefinition {
  return (
    isObj(v) &&
    isStr(v.name) &&
    isStr(v.tier) &&
    isObj(v.nearcore) &&
    isObj(v.semantic_scope) &&
    isObj(v.security_profile) &&
    isObj(v.hardware_profile) &&
    isObj(v.workload_suite) &&
    Array.isArray((v.semantic_scope as Record<string, unknown>).excludes) &&
    Array.isArray((v.semantic_scope as Record<string, unknown>).restrictions)
  );
}

/** Validate a `StoredChallenge`. The record's `tier` must agree with the signed definition. */
export function parseChallenge(v: unknown): ChallengeRecord | null {
  if (
    !isObj(v) ||
    !isChallengeId(v.id) ||
    !isStr(v.digest) ||
    !isStr(v.signature) ||
    !isStr(v.governance_key) ||
    !isStr(v.registered_at) ||
    !isStr(v.registered_by) ||
    typeof v.open !== 'boolean' ||
    !looksLikeDefinition(v.definition) ||
    v.tier !== v.definition.tier
  ) {
    return null;
  }
  return v as unknown as ChallengeRecord;
}

function looksLikeSubmission(v: unknown): v is SubmissionView {
  return (
    isObj(v) &&
    isSubmissionId(v.id) &&
    isStr(v.challenge_id) &&
    isStr(v.agent) &&
    isStr(v.candidate_name) &&
    isStr(v.tier) &&
    isStr(v.stage) &&
    Array.isArray(v.gates) &&
    Array.isArray(v.reason_codes)
  );
}

function looksLikeEntry(v: unknown): v is BoardEntry {
  return (
    isObj(v) &&
    isSubmissionId(v.submission_id) &&
    isStr(v.agent) &&
    isStr(v.candidate_name) &&
    isStr(v.tier) &&
    typeof v.revoked === 'boolean'
  );
}

export async function listChallenges(signal?: AbortSignal): Promise<ChallengeRecord[]> {
  const list = asList(await getJson('/v1/challenges', signal), 'challenges');
  return list.map(parseChallenge).filter((c): c is ChallengeRecord => c !== null);
}

export async function getChallenge(id: string, signal?: AbortSignal): Promise<ChallengeRecord> {
  if (!isChallengeId(id)) throw new ApiError('Invalid challenge id', null);
  const c = parseChallenge(await getJson(`/v1/challenges/${encodeURIComponent(id)}`, signal));
  if (!c) throw new ApiError('Malformed challenge record', null);
  if (c.id !== id) throw new ApiError('Challenge id in response does not match request', null);
  return c;
}

export async function getLeaderboard(challengeId: string, signal?: AbortSignal): Promise<BoardEntry[]> {
  if (!isChallengeId(challengeId)) throw new ApiError('Invalid challenge id', null);
  const list = asList(await getJson(`/v1/leaderboards/${encodeURIComponent(challengeId)}`, signal), 'entries');
  return list.filter(looksLikeEntry);
}

export interface SubmissionQuery {
  challenge_id?: string;
  agent?: string;
}

export async function listSubmissions(q: SubmissionQuery, signal?: AbortSignal): Promise<SubmissionView[]> {
  const params = new URLSearchParams();
  if (q.challenge_id) params.set('challenge_id', q.challenge_id.slice(0, 64));
  if (q.agent) params.set('agent', q.agent.slice(0, 64));
  const qs = params.toString();
  const list = asList(await getJson(`/v1/submissions${qs ? `?${qs}` : ''}`, signal), 'submissions');
  return list.filter(looksLikeSubmission);
}

export async function getSubmission(id: string, signal?: AbortSignal): Promise<SubmissionDetail> {
  if (!isSubmissionId(id)) throw new ApiError('Invalid submission id', null);
  const v = await getJson(`/v1/submissions/${encodeURIComponent(id)}`, signal);
  if (!looksLikeSubmission(v)) throw new ApiError('Malformed submission record', null);
  if (v.id !== id) throw new ApiError('Submission id in response does not match request', null);
  return v;
}

export const reportUrl = (id: string) => apiUrl(`/v1/submissions/${encodeURIComponent(id)}/report`);
export const eventsUrl = (id: string) => apiUrl(`/v1/submissions/${encodeURIComponent(id)}/events`);
