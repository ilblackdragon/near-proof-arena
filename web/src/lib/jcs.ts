/**
 * Canonical JSON as defined in docs/CONTRACTS.md §1 (RFC 8785 subset: sorted
 * keys by UTF-16 code units, no whitespace, integers only). Used to recompute
 * challenge ids in the browser: `chl_` + first 32 hex of sha256(JCS(def)).
 */
export class CanonicalError extends Error {}

export function canonicalJson(v: unknown): string {
  if (v === null) return 'null';
  switch (typeof v) {
    case 'boolean':
      return v ? 'true' : 'false';
    case 'string':
      return JSON.stringify(v);
    case 'number':
      if (!Number.isSafeInteger(v)) throw new CanonicalError('non-integer or unsafe number');
      return String(v);
    case 'object': {
      if (Array.isArray(v)) return `[${v.map(canonicalJson).join(',')}]`;
      const o = v as Record<string, unknown>;
      // Default JS sort compares UTF-16 code units, as JCS requires.
      const keys = Object.keys(o)
        .filter((k) => o[k] !== undefined)
        .sort();
      return `{${keys.map((k) => `${JSON.stringify(k)}:${canonicalJson(o[k])}`).join(',')}}`;
    }
    default:
      throw new CanonicalError(`unsupported value type ${typeof v}`);
  }
}

function hex(buf: ArrayBuffer): string {
  return Array.from(new Uint8Array(buf), (b) => b.toString(16).padStart(2, '0')).join('');
}

/** `sha256:<hex>` of the canonical JSON, or null if WebCrypto is unavailable. */
export async function canonicalDigest(v: unknown): Promise<string | null> {
  const subtle = globalThis.crypto?.subtle;
  if (!subtle) return null;
  const bytes = new TextEncoder().encode(canonicalJson(v));
  return `sha256:${hex(await subtle.digest('SHA-256', bytes))}`;
}

export const challengeIdFromDigest = (digest: string) => `chl_${digest.slice('sha256:'.length, 'sha256:'.length + 32)}`;
