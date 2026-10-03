import { Link, useParams } from 'react-router-dom';
import { getSubmission, reportUrl } from '../api/client';
import { useAsync, useLineage, useSubmissionEvents } from '../api/hooks';
import type { SubmissionDetail } from '../api/types';
import { AsyncView } from '../components/AsyncView';
import { AcceptedText, DecisionBadge, RevokedBadge, TierBadge } from '../components/Badges';
import { EvidenceGraphView } from '../components/EvidenceGraphView';
import { GatesTable } from '../components/GatesTable';
import { ChlLink } from '../components/Links';
import { PerfTable } from '../components/PerfTable';
import { StageProgress } from '../components/StageProgress';
import {
  BuildMeta,
  Digests,
  EventStream,
  Lineage,
  Logs,
  RevocationBanner,
  TrustSurface,
} from '../components/SubmissionParts';
import { T } from '../components/Text';
import { fmtScoreCi } from '../lib/format';
import { isSubmissionId } from '../lib/ids';

export function SubmissionPage() {
  const { id = '' } = useParams();
  if (!isSubmissionId(id)) {
    return (
      <section>
        <h1>Invalid submission id</h1>
        <p>
          <Link to="/submissions">All submissions</Link>
        </p>
      </section>
    );
  }
  return <SubmissionLoader id={id} />;
}

function SubmissionLoader({ id }: { id: string }) {
  const [state, reload] = useAsync((s) => getSubmission(id, s), [id]);
  const pending = state.status === 'ok' && state.data.decision == null;
  const stream = useSubmissionEvents(id, pending, reload);
  return (
    <AsyncView state={state} what="submission">
      {(s) => <SubmissionBody s={s} stream={stream} />}
    </AsyncView>
  );
}

function SubmissionBody({ s, stream }: { s: SubmissionDetail; stream: ReturnType<typeof useSubmissionEvents> }) {
  const lineage = useLineage(s);
  const missingCount = (s.evidence_graph?.edges ?? []).filter((e) => e.status === 'missing').length;
  return (
    <article className={s.tier === 'demo' ? 'submission is-demo' : 'submission'}>
      <p className="crumbs">
        <Link to="/submissions">Submissions</Link> / <ChlLink id={s.challenge_id} />
      </p>
      <h1>
        <T v={s.candidate_name} max={80} />{' '}
        <span className="h-badges">
          <TierBadge tier={s.tier} /> <DecisionBadge decision={s.decision} />
          {s.revoked && <RevokedBadge />}
        </span>
      </h1>
      <p className="mono small muted">{s.id}</p>
      {s.tier === 'demo' && (
        <p className="demo-warning" role="note">
          DEMO result: produced for plumbing demonstration (simulated components or unsafe dev sandbox
          permitted). It is never ranked and proves nothing about NEAR.
        </p>
      )}
      <RevocationBanner s={s} />

      <div className="summary-strip">
        <div>
          <span className="k">Accepted</span>
          <AcceptedText accepted={s.accepted} />
        </div>
        <div>
          <span className="k">Score</span>
          {s.accepted === true ? fmtScoreCi(s.score_milli, s.benchmark?.score_ci_milli) : '—'}
        </div>
        <div>
          <span className="k">Reason codes</span>
          {s.reason_codes.length === 0
            ? '—'
            : s.reason_codes.slice(0, 16).map((r, i) => (
                <code key={i} className="sp reason">
                  <T v={r} max={40} />
                </code>
              ))}
        </div>
        <div>
          <span className="k">Missing evidence</span>
          {s.evidence_graph ? (missingCount > 0 ? <span className="bad">{missingCount} edge(s)</span> : 'none') : 'no graph'}
        </div>
        <div>
          <a className="button" href={reportUrl(s.id)} download={`${s.id}-report.json`}>
            Download signed report
          </a>
        </div>
      </div>

      <section className="card" aria-labelledby="h-progress">
        <h2 id="h-progress">Pipeline progress</h2>
        <StageProgress stage={s.stage} decision={s.decision} />
        <EventStream status={stream.status} events={stream.events} />
      </section>

      <div className="facts-grid">
        <section className="card" aria-labelledby="h-digests">
          <h2 id="h-digests">Digests</h2>
          <Digests s={s} />
        </section>
        <section className="card" aria-labelledby="h-build">
          <h2 id="h-build">Candidate &amp; build</h2>
          <BuildMeta s={s} />
        </section>
      </div>

      <section className="card" aria-labelledby="h-lineage">
        <h2 id="h-lineage">Lineage</h2>
        <Lineage s={s} {...lineage} />
      </section>

      <section className="card" aria-labelledby="h-gates">
        <h2 id="h-gates">Gates</h2>
        <GatesTable gates={s.gates} />
      </section>

      <section className="card" aria-labelledby="h-trust">
        <h2 id="h-trust">Assumptions and trusted base</h2>
        <TrustSurface s={s} />
      </section>

      <section className="card" aria-labelledby="h-evidence">
        <h2 id="h-evidence">Evidence graph</h2>
        <EvidenceGraphView graph={s.evidence_graph} />
      </section>

      <section className="card" aria-labelledby="h-perf">
        <h2 id="h-perf">Performance</h2>
        {s.benchmark ? <PerfTable b={s.benchmark} accepted={s.accepted} /> : <p className="empty">Not benchmarked.</p>}
      </section>

      <section className="card" aria-labelledby="h-logs">
        <h2 id="h-logs">Logs</h2>
        <Logs s={s} />
      </section>

      <p>
        <Link to={`/compare?a=${encodeURIComponent(s.id)}${s.parent && isSubmissionId(s.parent) ? `&b=${encodeURIComponent(s.parent)}` : ''}`}>
          Compare {s.parent ? 'with parent' : 'with another submission'} →
        </Link>
      </p>
    </article>
  );
}
