import { useState } from 'react';
import { useSearchParams } from 'react-router-dom';
import { getSubmission } from '../api/client';
import { useAsync } from '../api/hooks';
import type { SubmissionDetail } from '../api/types';
import { AcceptedText, DecisionBadge, GateStatusBadge, RevokedBadge, TierBadge } from '../components/Badges';
import { DigestText } from '../components/Digest';
import { ChlLink, SubLink } from '../components/Links';
import { T } from '../components/Text';
import { fmtBytes, fmtNs, fmtScoreCi } from '../lib/format';
import { isSubmissionId } from '../lib/ids';
import { displayInline } from '../lib/text';

type Loaded = { status: 'ok'; data: SubmissionDetail } | { status: 'loading' } | { status: 'error'; error: Error } | { status: 'none' };

function useSub(id: string): Loaded {
  const valid = isSubmissionId(id);
  const [st] = useAsync((s) => (valid ? getSubmission(id, s) : Promise.resolve(null)), [id]);
  if (!valid) return { status: 'none' };
  if (st.status === 'ok') return st.data ? { status: 'ok', data: st.data } : { status: 'none' };
  return st;
}

function Cell({ l }: { l: Loaded }) {
  if (l.status === 'loading') return <span className="muted">loading…</span>;
  if (l.status === 'error') return <span className="bad"><T v={l.error.message} /></span>;
  if (l.status === 'none') return <span className="muted">—</span>;
  return null;
}

export function ComparePage() {
  const [params, setParams] = useSearchParams();
  const a = (params.get('a') ?? '').slice(0, 100);
  const b = (params.get('b') ?? '').slice(0, 100);
  const [da, setDa] = useState(a);
  const [db, setDb] = useState(b);
  const A = useSub(a);
  const B = useSub(b);

  return (
    <section>
      <h1>Compare submissions</h1>
      <form
        className="filters"
        aria-label="Choose submissions to compare"
        onSubmit={(e) => {
          e.preventDefault();
          const next = new URLSearchParams();
          if (da.trim()) next.set('a', da.trim());
          if (db.trim()) next.set('b', db.trim());
          setParams(next);
        }}
      >
        <label>
          Submission A
          <input value={da} onChange={(e) => setDa(e.target.value)} maxLength={100} placeholder="sub_…" spellCheck={false} />
        </label>
        <label>
          Submission B
          <input value={db} onChange={(e) => setDb(e.target.value)} maxLength={100} placeholder="sub_…" spellCheck={false} />
        </label>
        <button type="submit">Compare</button>
      </form>
      {(a && !isSubmissionId(a)) || (b && !isSubmissionId(b)) ? (
        <p className="bad" role="alert">Submission ids look like <code>sub_…</code>.</p>
      ) : null}
      {A.status === 'ok' || B.status === 'ok' ? (
        <CompareTable A={A} B={B} />
      ) : (
        <div className="small muted">
          <p>Enter two submission ids. A: <Cell l={A} /> B: <Cell l={B} /></p>
        </div>
      )}
    </section>
  );
}

function CompareTable({ A, B }: { A: Loaded; B: Loaded }) {
  const sa = A.status === 'ok' ? A.data : null;
  const sb = B.status === 'ok' ? B.data : null;
  const row = (label: string, f: (s: SubmissionDetail) => React.ReactNode, key?: (s: SubmissionDetail) => unknown) => {
    const differ = key && sa && sb ? JSON.stringify(key(sa)) !== JSON.stringify(key(sb)) : false;
    return (
      <tr className={differ ? 'differ' : undefined}>
        <th scope="row">
          {displayInline(label, 80)}
          {differ && <span className="sr-only"> (differs)</span>}
          {differ && <span className="diff-mark" aria-hidden="true"> ≠</span>}
        </th>
        <td>{sa ? f(sa) : <Cell l={A} />}</td>
        <td>{sb ? f(sb) : <Cell l={B} />}</td>
      </tr>
    );
  };
  const gateIds = Array.from(new Set([...(sa?.gates ?? []), ...(sb?.gates ?? [])].map((g) => g.gate))).slice(0, 32);
  const classIds = Array.from(
    new Set([...(sa?.benchmark?.classes ?? []), ...(sb?.benchmark?.classes ?? [])].map((c) => c.class_id)),
  ).slice(0, 32);
  const gate = (s: SubmissionDetail, id: string) => s.gates.find((g) => g.gate === id);
  const cls = (s: SubmissionDetail, id: string) => s.benchmark?.classes.find((c) => c.class_id === id);

  return (
    <div className="table-wrap">
      <table className="data compare">
        <caption className="sr-only">Side-by-side comparison; rows marked ≠ differ</caption>
        <thead>
          <tr>
            <th scope="col">Field</th>
            <th scope="col">A {sa && <SubLink id={sa.id} />}</th>
            <th scope="col">B {sb && <SubLink id={sb.id} />}</th>
          </tr>
        </thead>
        <tbody>
          {row('Candidate', (s) => <T v={s.candidate_name} max={64} empty="(unnamed — manifest not yet validated)" />, (s) => s.candidate_name)}
          {row('Agent', (s) => <T v={s.agent} max={64} />, (s) => s.agent)}
          {row('Challenge', (s) => <ChlLink id={s.challenge_id} />, (s) => s.challenge_id)}
          {row('Tier', (s) => <TierBadge tier={s.tier} />, (s) => s.tier)}
          {row('Decision', (s) => (
            <>
              <DecisionBadge decision={s.decision} /> {s.revoked && <RevokedBadge />}
            </>
          ), (s) => [s.decision, !!s.revoked])}
          {row('Accepted', (s) => <AcceptedText accepted={s.accepted} />, (s) => s.accepted)}
          {row('Score', (s) => (s.accepted === true ? fmtScoreCi(s.score_milli, s.benchmark?.score_ci_milli) : '—'), (s) => s.score_milli)}
          {row('Change class', (s) => s.change_class ?? '—', (s) => s.change_class)}
          {row('Parent', (s) => (s.parent ? <SubLink id={s.parent} /> : '—'), (s) => s.parent)}
          {row('Package', (s) => <DigestText d={s.package_digest} />, (s) => s.package_digest)}
          {row('Verify artifact', (s) => (s.verified_surface ? <DigestText d={s.verified_surface.verify_artifact} /> : '—'), (s) => s.verified_surface?.verify_artifact)}
          {row('Formal tree', (s) => (s.verified_surface ? <DigestText d={s.verified_surface.formal_tree} /> : '—'), (s) => s.verified_surface?.formal_tree)}
          {row('Missing evidence edges', (s) => (s.evidence_graph ? String(s.evidence_graph.edges.filter((e) => e.status === 'missing').length) : 'no graph'), (s) => s.evidence_graph?.edges.filter((e) => e.status === 'missing').length)}
          {gateIds.map((id) => (
            <RowFrag key={`g-${id}`}>
              {row(`Gate ${id}`, (s) => {
                const g = gate(s, id);
                return g ? (
                  <>
                    <GateStatusBadge status={g.status} />
                    {g.reused_from && <span className="small muted"> reused</span>}
                  </>
                ) : (
                  <span className="muted">not run</span>
                );
              }, (s) => gate(s, id)?.status)}
            </RowFrag>
          ))}
          {classIds.map((id) => (
            <RowFrag key={`c-${id}`}>
              {row(`Prove median: ${id.slice(0, 40)}`, (s) => fmtNs(cls(s, id)?.median_ns), (s) => cls(s, id)?.median_ns)}
              {row(`Verify median: ${id.slice(0, 40)}`, (s) => fmtNs(cls(s, id)?.verify_median_ns), (s) => cls(s, id)?.verify_median_ns)}
              {row(`Max proof: ${id.slice(0, 40)}`, (s) => fmtBytes(cls(s, id)?.proof_bytes_max), (s) => cls(s, id)?.proof_bytes_max)}
            </RowFrag>
          ))}
        </tbody>
      </table>
    </div>
  );
}

const RowFrag = ({ children }: { children: React.ReactNode }) => <>{children}</>;
