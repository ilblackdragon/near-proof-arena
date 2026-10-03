/** Error hierarchy; `exitCode` mirrors the `arena` CLI exit codes (docs/AGENT_CONTRACT.md §9). */
export class ArenaError extends Error {
  readonly status: number | null;
  readonly body: string;
  readonly exitCode: number = 1;
  constructor(message: string, status: number | null = null, body = "") {
    super(message);
    this.name = new.target.name;
    this.status = status;
    this.body = body;
  }
}
/** HTTP 401/403 or missing token. */
export class AuthError extends ArenaError {
  override readonly exitCode = 4;
}
/** Unreachable, timeout, HTTP 5xx/429 — retry with the same idempotency key. */
export class UnavailableError extends ArenaError {
  override readonly exitCode = 5;
}
/** HTTP 400/409/413/422 and other 4xx. */
export class RejectedError extends ArenaError {
  override readonly exitCode = 6;
}
/** HTTP 404. */
export class NotFoundError extends ArenaError {
  override readonly exitCode = 7;
}

export function errorForStatus(status: number, body: string): ArenaError {
  const msg = `HTTP ${status}: ${body.slice(0, 2000)}`;
  if (status === 401 || status === 403) return new AuthError(msg, status, body);
  if (status === 404) return new NotFoundError(msg, status, body);
  if (status === 429 || status >= 500) return new UnavailableError(msg, status, body);
  return new RejectedError(msg, status, body);
}
