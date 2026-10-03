import type { GateResult } from '../api/types';
import { fmtTime } from '../lib/format';
import { GateStatusBadge } from './Badges';
import { DigestText } from './Digest';
import { SubLink } from './Links';
import { T } from './Text';

const MAX_GATES = 64;

export function GatesTable({ gates }: { gates: GateResult[] }) {
  if (gates.length === 0) return <p className="empty">No gate results recorded yet.</p>;
  return (
    <div className="table-wrap">
      <table className="data gates">
        <thead>
          <tr>
            <th scope="col">Gate</th>
            <th scope="col">Mandatory</th>
            <th scope="col">Status</th>
            <th scope="col">Reason codes</th>
            <th scope="col">Summary</th>
            <th scope="col">Evidence</th>
            <th scope="col">Reused from</th>
            <th scope="col">Finished</th>
          </tr>
        </thead>
        <tbody>
          {gates.slice(0, MAX_GATES).map((g, i) => (
            <tr key={i} className={`gate-row status-${String(g.status).toLowerCase()}`}>
              <th scope="row">
                <code><T v={g.gate} max={40} /></code>
              </th>
              <td>{g.mandatory ? 'yes' : 'no'}</td>
              <td>
                <GateStatusBadge status={g.status} />
              </td>
              <td>
                {g.reason_codes.length === 0
                  ? '—'
                  : g.reason_codes.slice(0, 16).map((r, j) => (
                      <code key={j} className="sp reason">
                        <T v={r} max={40} />
                      </code>
                    ))}
              </td>
              <td className="summary">
                <T v={g.summary} max={500} />
              </td>
              <td className="small">
                {g.evidence.length === 0 ? (
                  '—'
                ) : (
                  <ul className="plain">
                    {g.evidence.slice(0, 8).map((e, j) => (
                      <li key={j}>
                        <T v={e.label} max={60} />: <DigestText d={e.digest} />
                        {!e.public && <span className="muted"> (not public)</span>}
                      </li>
                    ))}
                    {g.evidence.length > 8 && <li className="muted">+{g.evidence.length - 8} more</li>}
                  </ul>
                )}
              </td>
              <td className="small">{g.reused_from ? <SubLink id={g.reused_from} /> : '—'}</td>
              <td className="small nowrap">{fmtTime(g.finished_at)}</td>
            </tr>
          ))}
        </tbody>
      </table>
      {gates.length > MAX_GATES && <p className="note">{gates.length - MAX_GATES} further gate rows not shown.</p>}
    </div>
  );
}
