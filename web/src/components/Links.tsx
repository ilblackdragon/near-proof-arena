import { Link } from 'react-router-dom';
import { challengePath, isChallengeId, isSubmissionId, submissionPath } from '../lib/ids';
import { T } from './Text';

/** Internal link only if the id is well-formed; otherwise inert text. */
export function SubLink({ id, children }: { id: unknown; children?: React.ReactNode }) {
  if (!isSubmissionId(id)) return <T v={id} max={100} className="mono" />;
  return (
    <Link to={submissionPath(id)} className="mono">
      {children ?? id}
    </Link>
  );
}

export function ChlLink({ id, children }: { id: unknown; children?: React.ReactNode }) {
  if (!isChallengeId(id)) return <T v={id} max={100} className="mono" />;
  return <Link to={challengePath(id)}>{children ?? <span className="mono">{id}</span>}</Link>;
}
