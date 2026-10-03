import { useCallback, useEffect, useRef, useState } from 'react';
import { canonicalDigest, challengeIdFromDigest, CanonicalError } from '../lib/jcs';
import { isSubmissionId } from '../lib/ids';
import { sanitizeInline } from '../lib/text';
import { eventsUrl, getChallenge, getSubmission } from './client';
import type { ChallengeRecord, EventPayload, SubmissionDetail } from './types';

export type Async<T> =
  | { status: 'loading'; data?: undefined; error?: undefined }
  | { status: 'error'; data?: undefined; error: Error }
  | { status: 'ok'; data: T; error?: undefined };

/** Fetch with abort-on-unmount; `reload` refetches without flashing the loading state. */
export function useAsync<T>(fn: (signal: AbortSignal) => Promise<T>, deps: unknown[]) {
  const [state, setState] = useState<Async<T>>({ status: 'loading' });
  const [tick, setTick] = useState(0);
  const fnRef = useRef(fn);
  fnRef.current = fn;
  const key = JSON.stringify(deps);
  const lastKey = useRef<string | null>(null);
  useEffect(() => {
    const ac = new AbortController();
    if (lastKey.current !== key) {
      lastKey.current = key;
      setState({ status: 'loading' });
    }
    fnRef
      .current(ac.signal)
      .then((data) => {
        if (!ac.signal.aborted) setState({ status: 'ok', data });
      })
      .catch((error: Error) => {
        if (!ac.signal.aborted && error?.name !== 'AbortError') setState({ status: 'error', error });
      });
    return () => ac.abort();
  }, [key, tick]);
  const reload = useCallback(() => setTick((t) => t + 1), []);
  return [state, reload] as const;
}

export type VerifyState =
  | { status: 'pending' }
  | { status: 'verified'; digest: string }
  | { status: 'mismatch'; digest: string; reason: string }
  | { status: 'unavailable'; reason: string };

/**
 * Recompute the challenge id/digest from its definition (CONTRACTS §1:
 * "the id is recomputed by every reader and mismatch = reject").
 */
export function useChallengeVerification(c: ChallengeRecord | undefined): VerifyState {
  const [st, setSt] = useState<VerifyState>({ status: 'pending' });
  useEffect(() => {
    if (!c) return;
    let live = true;
    setSt({ status: 'pending' });
    canonicalDigest(c.definition)
      .then((digest) => {
        if (!live) return;
        if (digest === null) {
          setSt({ status: 'unavailable', reason: 'WebCrypto unavailable in this context' });
        } else if (challengeIdFromDigest(digest) !== c.id) {
          setSt({ status: 'mismatch', digest, reason: 'id does not match sha256(JCS(definition))' });
        } else if (c.digest !== digest) {
          setSt({ status: 'mismatch', digest, reason: 'server digest does not match recomputed digest' });
        } else {
          setSt({ status: 'verified', digest });
        }
      })
      .catch((e: unknown) => {
        if (!live) return;
        setSt(
          e instanceof CanonicalError
            ? { status: 'mismatch', digest: '', reason: `definition is not canonical: ${e.message}` }
            : { status: 'unavailable', reason: 'digest computation failed' },
        );
      });
    return () => {
      live = false;
    };
  }, [c]);
  return st;
}

export interface StreamEvent {
  seq: number;
  type: string;
  text: string;
}
export type StreamStatus = 'idle' | 'connecting' | 'live' | 'closed' | 'unsupported' | 'error';

/** Summarise an `EventPayload` (server/openapi.json) for display; falls back to the raw text. */
export function describeEvent(raw: string): string {
  try {
    const p = JSON.parse(raw) as Partial<EventPayload>;
    if (p && typeof p.action === 'string') {
      const data = p.data === undefined ? '' : ` ${JSON.stringify(p.data)}`;
      return `${typeof p.at === 'string' ? p.at + ' ' : ''}${p.action}${data}`;
    }
  } catch {
    /* not JSON: show as text */
  }
  return raw;
}

const EVENT_TYPES = ['message', 'stage', 'gate', 'decision', 'progress', 'log', 'status', 'done'];
const MAX_EVENTS = 100;
const MAX_EVENT_CHARS = 2048;

/**
 * Subscribe to `/v1/submissions/{id}/events` (SSE) while `enabled`. Each event
 * is recorded (bounded, sanitised) and triggers a throttled `onChange` so the
 * page refetches the authoritative submission record; event payloads are
 * never trusted as state on their own.
 */
export function useSubmissionEvents(id: string, enabled: boolean, onChange: () => void) {
  const [events, setEvents] = useState<StreamEvent[]>([]);
  const [status, setStatus] = useState<StreamStatus>('idle');
  const cb = useRef(onChange);
  cb.current = onChange;

  useEffect(() => {
    if (!enabled || !isSubmissionId(id)) {
      setStatus((s) => (s === 'live' || s === 'connecting' ? 'closed' : s));
      return;
    }
    if (typeof EventSource === 'undefined') {
      setStatus('unsupported');
      return;
    }
    setStatus('connecting');
    const es = new EventSource(eventsUrl(id));
    let seq = 0;
    let timer: ReturnType<typeof setTimeout> | null = null;
    const schedule = () => {
      if (timer) return;
      timer = setTimeout(() => {
        timer = null;
        cb.current();
      }, 500);
    };
    const handler = (ev: Event) => {
      const me = ev as MessageEvent;
      const raw = typeof me.data === 'string' ? me.data.slice(0, MAX_EVENT_CHARS) : '';
      const entry: StreamEvent = {
        seq: ++seq,
        type: sanitizeInline(ev.type, 32).text,
        text: sanitizeInline(describeEvent(raw), 512).text,
      };
      setEvents((prev) => [...prev, entry].slice(-MAX_EVENTS));
      schedule();
    };
    es.onopen = () => setStatus('live');
    es.onerror = () => {
      // EventSource auto-reconnects unless CLOSED.
      setStatus(es.readyState === 2 ? 'closed' : 'connecting');
    };
    for (const t of EVENT_TYPES) es.addEventListener(t, handler);
    return () => {
      if (timer) clearTimeout(timer);
      es.close();
      setStatus('closed');
    };
  }, [id, enabled]);

  return { events, status };
}

export interface LineageHop {
  id: string;
  sub: SubmissionDetail | null;
  error?: string;
}

const MAX_LINEAGE = 20;

/** Walk `parent` links (bounded depth, cycle-safe). */
export function useLineage(start: SubmissionDetail | undefined) {
  const [hops, setHops] = useState<LineageHop[]>([]);
  const [done, setDone] = useState(false);
  const parent = start?.parent ?? null;
  const startId = start?.id;
  useEffect(() => {
    const ac = new AbortController();
    setHops([]);
    setDone(false);
    (async () => {
      const seen = new Set<string>(startId ? [startId] : []);
      const acc: LineageHop[] = [];
      let next: string | null = parent;
      while (next && acc.length < MAX_LINEAGE) {
        const cur: string = next;
        if (seen.has(cur)) {
          acc.push({ id: cur, sub: null, error: 'cycle detected' });
          break;
        }
        seen.add(cur);
        if (!isSubmissionId(cur)) {
          acc.push({ id: cur, sub: null, error: 'invalid id' });
          break;
        }
        try {
          const s = await getSubmission(cur, ac.signal);
          acc.push({ id: cur, sub: s });
          next = s.parent ?? null;
        } catch (e) {
          if ((e as Error).name === 'AbortError') return;
          acc.push({ id: cur, sub: null, error: (e as Error).message });
          break;
        }
        if (!ac.signal.aborted) setHops([...acc]);
      }
      if (!ac.signal.aborted) {
        setHops([...acc]);
        setDone(true);
      }
    })();
    return () => ac.abort();
  }, [parent, startId]);
  return { hops, done, truncated: hops.length >= MAX_LINEAGE };
}

export interface ChallengeLineageHop {
  id: string;
  c: ChallengeRecord | null;
  error?: string;
}

/** Walk `definition.supersedes` (bounded, cycle-safe). */
export function useChallengeLineage(start: ChallengeRecord | undefined) {
  const [hops, setHops] = useState<ChallengeLineageHop[]>([]);
  const first = start?.definition.supersedes ?? null;
  const startId = start?.id;
  useEffect(() => {
    const ac = new AbortController();
    setHops([]);
    (async () => {
      const seen = new Set<string>(startId ? [startId] : []);
      const acc: ChallengeLineageHop[] = [];
      let next: string | null = first;
      while (next && acc.length < MAX_LINEAGE) {
        const cur: string = next;
        if (seen.has(cur)) {
          acc.push({ id: cur, c: null, error: 'cycle detected' });
          break;
        }
        seen.add(cur);
        try {
          const c = await getChallenge(cur, ac.signal);
          acc.push({ id: cur, c });
          next = c.definition.supersedes ?? null;
        } catch (e) {
          if ((e as Error).name === 'AbortError') return;
          acc.push({ id: cur, c: null, error: (e as Error).message });
          break;
        }
      }
      if (!ac.signal.aborted) setHops(acc);
    })();
    return () => ac.abort();
  }, [first, startId]);
  return hops;
}
