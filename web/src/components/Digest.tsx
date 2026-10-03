import { isDigest } from '../lib/ids';
import { T } from './Text';

/** Shows a digest in monospace, abbreviated, with the full value selectable. */
export function DigestText({ d, full = false }: { d: unknown; full?: boolean }) {
  if (!isDigest(d)) {
    return (
      <span className="bad mono" title="not a valid sha256 digest">
        <T v={d} max={80} /> (invalid digest)
      </span>
    );
  }
  const hex = d.slice(7);
  return (
    <code className="digest" title={d}>
      {full ? d : `sha256:${hex.slice(0, 12)}…${hex.slice(-6)}`}
    </code>
  );
}
