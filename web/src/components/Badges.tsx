import type { Decision, GateStatus, Tier, EdgeStatus } from '../api/types';

export function TierBadge({ tier }: { tier: Tier | string }) {
  switch (tier) {
    case 'formal':
      return <span className="badge tier-formal">FORMAL</span>;
    case 'experimental':
      return <span className="badge tier-experimental" title="Tested only; never formally ranked">EXPERIMENTAL</span>;
    case 'demo':
      return <span className="badge tier-demo" title="Plumbing demonstration; never ranked">DEMO · NOT RANKED</span>;
    default:
      return <span className="badge">UNKNOWN TIER</span>;
  }
}

export const ReferenceBadge = () => (
  <span className="badge tier-reference" title="Reference baseline; not part of the competition ranking">
    REFERENCE
  </span>
);

export function DecisionBadge({ decision }: { decision?: Decision | null }) {
  if (decision === null || decision === undefined) {
    return <span className="badge dec-pending">PENDING</span>;
  }
  const cls: Record<Decision, string> = {
    ADMITTED: 'dec-admitted',
    REJECTED: 'dec-rejected',
    INCONCLUSIVE: 'dec-inconclusive',
    INFRA_ERROR: 'dec-infra',
    CANCELLED: 'dec-cancelled',
  };
  if (!(decision in cls)) return <span className="badge">UNKNOWN</span>;
  return <span className={`badge ${cls[decision]}`}>{decision.replace('_', ' ')}</span>;
}

export function AcceptedText({ accepted }: { accepted?: boolean | null }) {
  if (accepted === true) return <span className="ok">accepted</span>;
  if (accepted === false) return <span className="bad">not accepted</span>;
  return <span className="muted">pending (accepted = null)</span>;
}

export function GateStatusBadge({ status }: { status: GateStatus }) {
  const map: Record<GateStatus, [string, string]> = {
    PASS: ['gate-pass', 'PASS'],
    FAIL: ['gate-fail', 'FAIL'],
    UNKNOWN: ['gate-unknown', 'UNKNOWN'],
    NOT_APPLICABLE: ['gate-na', 'N/A'],
  };
  const [c, l] = map[status] ?? ['', 'INVALID'];
  return <span className={`badge ${c}`}>{l}</span>;
}

export function EdgeStatusBadge({ status }: { status: EdgeStatus }) {
  const label = { checked: 'CHECKED', trusted: 'TRUSTED', tested: 'TESTED', missing: 'MISSING' }[status] ?? 'INVALID';
  return <span className={`badge edge-${status}`}>{label}</span>;
}

export const RevokedBadge = () => <span className="badge revoked">REVOKED</span>;
