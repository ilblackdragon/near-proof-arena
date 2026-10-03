/**
 * Neutralisation of untrusted (candidate- or runner-provided) strings.
 *
 * React already escapes text content, so markup in a string can never become
 * DOM. These helpers additionally defend against *visual* attacks that survive
 * escaping: terminal escape sequences, bidi overrides (e.g. U+202E "RTL
 * override" used to disguise names/digests), zero-width characters, other
 * control characters, and unbounded length.
 *
 * Invisible/control characters are replaced with a visible `[U+XXXX]` marker
 * rather than silently removed, so a reader can tell something was there.
 */

/** Default maximum code points for inline strings (names, labels). */
export const INLINE_MAX = 256;
/** Maximum code points for a single block of log text. */
export const BLOCK_MAX = 64 * 1024;

// ANSI / VT escape sequences:
//   CSI:  ESC [ params intermediates final     (also 8-bit CSI U+009B)
//   OSC:  ESC ] ... (BEL | ESC \)             (also 8-bit OSC U+009D)
//   other two-char ESC sequences.
// eslint-disable-next-line no-control-regex
const ANSI_RE = /(?:\u001b\[|\u009b)[0-?]*[ -/]*[@-~]|(?:\u001b\]|\u009d)[^\u0007\u001b\u009c]*(?:\u0007|\u001b\\|\u009c)?|\u001b[@-Z\\-_]/g;

// Bidi controls, zero-width and other invisible format characters.
const INVISIBLE_RE = /[؜ᅟᅠ᠎​-‏‪-‮⁠-⁩⁪-⁯ㅤ︀-️﻿￹-￻]/g;

// C0 controls (except TAB/LF, handled per mode), DEL, C1 controls, lone surrogates.
// eslint-disable-next-line no-control-regex
const CONTROL_INLINE_RE = /[\u0000-\u001f\u007f-\u009f]/g;
// eslint-disable-next-line no-control-regex
const CONTROL_BLOCK_RE = /[\u0000-\u0008\u000b-\u001f\u007f-\u009f]/g;
const LONE_SURROGATE_RE = /[\ud800-\udbff](?![\udc00-\udfff])|(?<![\ud800-\udbff])[\udc00-\udfff]/g;

function marker(ch: string): string {
  const cp = ch.codePointAt(0) ?? 0;
  return `[U+${cp.toString(16).toUpperCase().padStart(4, '0')}]`;
}

/** Coerce an unknown JSON value to a display string without ever producing markup. */
export function coerce(value: unknown): string {
  if (value === null || value === undefined) return '';
  if (typeof value === 'string') return value;
  if (typeof value === 'number' || typeof value === 'boolean' || typeof value === 'bigint') {
    return String(value);
  }
  return '[invalid value]';
}

function truncate(s: string, max: number): { text: string; truncated: number } {
  // Count by code points so we never split a surrogate pair.
  const cps = Array.from(s);
  if (cps.length <= max) return { text: s, truncated: 0 };
  return { text: cps.slice(0, max).join(''), truncated: cps.length - max };
}

export interface Sanitized {
  text: string;
  /** Number of code points removed by truncation. */
  truncated: number;
  /** True if any escape sequence or invisible/control char was neutralised. */
  altered: boolean;
}

function neutralise(input: string, controlRe: RegExp): { s: string; altered: boolean } {
  let altered = false;
  const flag = <T,>(x: T) => {
    altered = true;
    return x;
  };
  let s = input.replace(ANSI_RE, () => flag(''));
  s = s.replace(INVISIBLE_RE, (c) => flag(marker(c)));
  s = s.replace(controlRe, (c) => flag(marker(c)));
  s = s.replace(LONE_SURROGATE_RE, () => flag('�'));
  return { s, altered };
}

/** Single-line display: no newlines, no controls, bounded. */
export function sanitizeInline(value: unknown, max = INLINE_MAX): Sanitized {
  // Truncate generously first so hostile megabyte strings never hit the regexes.
  const pre = truncate(coerce(value), max * 4);
  const { s, altered } = neutralise(pre.text, CONTROL_INLINE_RE);
  const t = truncate(s, max);
  return { text: t.text, truncated: t.truncated + pre.truncated, altered };
}

/** Multi-line display (logs): keeps LF and TAB, normalises CR, bounded. */
export function sanitizeBlock(value: unknown, max = BLOCK_MAX): Sanitized {
  const pre = truncate(coerce(value), max * 2);
  const normalised = pre.text.replace(/\r\n?/g, '\n');
  const { s, altered } = neutralise(normalised, CONTROL_BLOCK_RE);
  const t = truncate(s, max);
  return { text: t.text, truncated: t.truncated + pre.truncated, altered };
}

/** Convenience: sanitised inline text with a visible truncation suffix. */
export function displayInline(value: unknown, max = INLINE_MAX): string {
  const r = sanitizeInline(value, max);
  return r.truncated > 0 ? `${r.text}… [+${r.truncated} chars]` : r.text;
}
