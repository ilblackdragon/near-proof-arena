/**
 * API base URL. Empty string = same origin (production behind a reverse proxy,
 * or the Vite dev proxy). Set `VITE_API_BASE` at build time to point elsewhere;
 * the build adds that origin to the CSP `connect-src`.
 */
const raw = (import.meta.env.VITE_API_BASE as string | undefined) ?? '';
export const API_BASE = raw.replace(/\/+$/, '');

export function apiUrl(path: string): string {
  if (!path.startsWith('/v1/')) throw new Error('API paths must start with /v1/');
  return `${API_BASE}${path}`;
}
