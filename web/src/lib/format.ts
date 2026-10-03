/** Number formatting. All inputs are integers from the API (no floats in contracts). */

const isNum = (v: unknown): v is number => typeof v === 'number' && Number.isFinite(v);

export function fmtNs(ns: unknown): string {
  if (!isNum(ns)) return '—';
  if (ns < 1e3) return `${ns} ns`;
  if (ns < 1e6) return `${(ns / 1e3).toFixed(1)} µs`;
  if (ns < 1e9) return `${(ns / 1e6).toFixed(2)} ms`;
  return `${(ns / 1e9).toFixed(3)} s`;
}

export function fmtBytes(b: unknown): string {
  if (!isNum(b)) return '—';
  const units = ['B', 'KiB', 'MiB', 'GiB', 'TiB'];
  let v = b;
  let i = 0;
  while (v >= 1024 && i < units.length - 1) {
    v /= 1024;
    i++;
  }
  return i === 0 ? `${v} B` : `${v.toFixed(v >= 100 ? 0 : v >= 10 ? 1 : 2)} ${units[i]}`;
}

/** `score_milli` is score * 1000 as an integer. */
export function fmtScore(milli: unknown): string {
  if (!isNum(milli)) return '—';
  return (milli / 1000).toFixed(3);
}

export function fmtScoreCi(milli: unknown, ciMilli: unknown): string {
  if (!isNum(milli)) return '—';
  if (!isNum(ciMilli)) return fmtScore(milli);
  return `${fmtScore(milli)} ± ${(ciMilli / 1000).toFixed(3)}`;
}

export function fmtPpm(ppm: unknown): string {
  if (!isNum(ppm)) return '—';
  return `${(ppm / 10_000).toFixed(2)}%`;
}

/** Timestamps are rendered as given (ISO-8601 expected) plus a parsed UTC form when valid. */
export function fmtTime(s: unknown): string {
  if (typeof s !== 'string' || s.length === 0) return '—';
  if (s.length > 64) return s.slice(0, 64) + '…';
  const t = Date.parse(s);
  if (Number.isNaN(t)) return s;
  return new Date(t).toISOString().replace('T', ' ').replace(/\.\d{3}Z$/, 'Z');
}

export function fmtInt(v: unknown): string {
  return isNum(v) ? v.toLocaleString('en-US') : '—';
}
