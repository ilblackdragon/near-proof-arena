/**
 * Identifier validation. Only identifiers matching these shapes are ever
 * turned into internal links or API paths; anything else is rendered as inert
 * text. Values are additionally passed through `encodeURIComponent`.
 */
export const CHALLENGE_ID_RE = /^chl_[0-9a-f]{32}$/;
export const SUBMISSION_ID_RE = /^sub_[A-Za-z0-9_-]{1,96}$/;
export const DIGEST_RE = /^sha256:[0-9a-f]{64}$/;
export const AGENT_RE = /^[A-Za-z0-9_.-]{1,64}$/;

export const isChallengeId = (v: unknown): v is string =>
  typeof v === 'string' && CHALLENGE_ID_RE.test(v);
export const isSubmissionId = (v: unknown): v is string =>
  typeof v === 'string' && SUBMISSION_ID_RE.test(v);
export const isDigest = (v: unknown): v is string => typeof v === 'string' && DIGEST_RE.test(v);

export const challengePath = (id: string) => `/challenges/${encodeURIComponent(id)}`;
export const submissionPath = (id: string) => `/submissions/${encodeURIComponent(id)}`;
