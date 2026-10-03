import { describe, expect, it } from 'vitest';
import { displayInline, sanitizeBlock, sanitizeInline } from '../src/lib/text';

describe('sanitizeInline', () => {
  it('strips ANSI CSI/OSC sequences', () => {
    const r = sanitizeInline('\u001b[1;31mred\u001b[0m \u001b]0;title\u0007x \u009b2Jy');
    expect(r.text).toBe('red x y');
    expect(r.altered).toBe(true);
    expect(r.text).not.toMatch(/\u001b|\u009b/);
  });
  it('makes bidi overrides and zero-width chars visible', () => {
    const r = sanitizeInline('abc‮gpj.exe‬​');
    expect(r.text).toBe('abc[U+202E]gpj.exe[U+202C][U+200B]');
  });
  it('neutralises control characters including newlines inline', () => {
    expect(sanitizeInline('a\nb\u0000c\u007f').text).toBe('a[U+000A]b[U+0000]c[U+007F]');
  });
  it('leaves markup characters for React to escape (never interpreted)', () => {
    expect(sanitizeInline('<script>alert(1)</script>').text).toBe('<script>alert(1)</script>');
  });
  it('truncates by code point and reports the remainder', () => {
    const r = sanitizeInline('😀'.repeat(10), 4);
    expect(r.text).toBe('😀'.repeat(4));
    expect(r.truncated).toBe(6);
    expect(displayInline('x'.repeat(300), 10)).toBe('xxxxxxxxxx… [+290 chars]');
  });
  it('replaces lone surrogates', () => {
    expect(sanitizeInline('a\ud800b').text).toBe('a�b');
  });
  it('coerces non-strings without producing markup', () => {
    expect(sanitizeInline({ toString: () => '<b>' }).text).toBe('[invalid value]');
    expect(sanitizeInline(42).text).toBe('42');
    expect(sanitizeInline(null).text).toBe('');
  });
});

describe('sanitizeBlock', () => {
  it('keeps newlines/tabs, normalises CR, strips ANSI', () => {
    const r = sanitizeBlock('\u001b[32mok\u001b[0m\r\nnext\tcol\rover\u0007');
    expect(r.text).toBe('ok\nnext\tcol\nover[U+0007]');
  });
  it('bounds very large input', () => {
    const r = sanitizeBlock('a'.repeat(200_000), 1000);
    expect(r.text.length).toBe(1000);
    expect(r.truncated).toBe(199_000);
  });
});
