import { sanitizeBlock, sanitizeInline, INLINE_MAX, BLOCK_MAX } from '../lib/text';

/**
 * The ONLY way untrusted strings reach the DOM: as React text children
 * (escaped), after neutralising control/bidi characters, inside a <bdi> so
 * that a hostile string cannot reorder surrounding text.
 */
export function T({ v, max = INLINE_MAX, className }: { v: unknown; max?: number; className?: string }) {
  const r = sanitizeInline(v, max);
  return (
    <bdi className={className ? `ut ${className}` : 'ut'} data-altered={r.altered || undefined}>
      {r.text}
      {r.truncated > 0 && <span className="trunc">{`… [+${r.truncated} chars]`}</span>}
    </bdi>
  );
}

/** Pre-formatted bounded text block (logs, summaries). */
export function TextBlock({ v, max = BLOCK_MAX, label }: { v: unknown; max?: number; label?: string }) {
  const r = sanitizeBlock(v, max);
  return (
    <div className="textblock">
      <pre className="ut-block" dir="ltr" tabIndex={0} aria-label={label}>
        {r.text}
      </pre>
      {r.truncated > 0 && <p className="note">Truncated: {r.truncated.toLocaleString('en-US')} further characters not shown.</p>}
      {r.altered && <p className="note">Control, escape, or invisible characters were neutralised for display.</p>}
    </div>
  );
}
