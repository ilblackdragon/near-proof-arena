import { Fragment } from 'react';
import type { LineageHop, StreamEvent, StreamStatus } from '../api/hooks';
import type { SubmissionDetail } from '../api/types';
import { fmtNs, fmtTime } from '../lib/format';
import { DecisionBadge, RevokedBadge, TierBadge } from './Badges';
import { DigestText } from './Digest';
import { SubLink } from './Links';
import { T, TextBlock } from './Text';

export function RevocationBanner({ s }: { s: SubmissionDetail }) {
  const history = Array.isArray(s.revocation_history) ? s.revocation_history.slice(0, 50) : [];
  if (!s.revoked && history.length === 0) return null;
  return (
    <section className={s.revoked ? 'revocation-banner' : 'revocation-history'} role={s.revoked ? 'alert' : undefined} aria-labelledby="rev-h">
      <h2 id="rev-h">
        {s.revoked ? (
          <>
            <RevokedBadge /> This submission's admission has been revoked
          </>
        ) : (
          'Revocation history'
        )}
      </h2>
      {s.revoked && (
        <dl className="kv">
          <dt>Reason</dt>
          <dd>
            <T v={s.revoked.reason} max={1000} />
          </dd>
          <dt>Revoked at</dt>
          <dd>{fmtTime(s.revoked.revoked_at)}</dd>
          <dt>Revoked by</dt>
          <dd>
            <T v={s.revoked.revoked_by} max={80} />
          </dd>
        </dl>
      )}
      {history.length > 0 && (
        <ol className="history">
          {history.map((h, i) => (
            <li key={i}>
              {fmtTime(h.at)} — <strong><T v={h.action} max={32} /></strong> by <T v={h.by} max={80} />: <T v={h.reason} max={500} />
            </li>
          ))}
        </ol>
      )}
    </section>
  );
}

export function Lineage({ s, hops, done, truncated }: { s: SubmissionDetail; hops: LineageHop[]; done: boolean; truncated: boolean }) {
  if (!s.parent) {
    return <p className="small">No parent: this is a root submission (change class NO_PARENT).</p>;
  }
  return (
    <div>
      <ol className="lineage" aria-label="Parent lineage, newest first">
        <li>
          <strong>this</strong> <code className="mono">{s.id}</code>{' '}
          <span className="badge chg">{s.change_class ?? 'unclassified'}</span>
        </li>
        {hops.map((h, i) => (
          <li key={i}>
            <SubLink id={h.id} />{' '}
            {h.sub ? (
              <>
                <T v={h.sub.candidate_name} max={48} empty="(unnamed — manifest not yet validated)" /> <DecisionBadge decision={h.sub.decision} /> <TierBadge tier={h.sub.tier} />
                {h.sub.revoked && <RevokedBadge />}
                {h.sub.parent && <span className="badge chg">{h.sub.change_class ?? 'unclassified'}</span>}
              </>
            ) : (
              <span className="bad">unavailable: <T v={h.error} max={80} /></span>
            )}
          </li>
        ))}
        {!done && <li className="muted">loading…</li>}
      </ol>
      {truncated && <p className="note">Lineage display limited to 20 ancestors.</p>}
      <p className="small muted">
        Change class is computed by the judge. PROVER_ONLY children reuse formal gate results by
        content-addressed cache key (see "Reused from" in the gates table); VERIFIER_OR_PROTOCOL
        reopens every formal obligation.
      </p>
    </div>
  );
}

export function Digests({ s }: { s: SubmissionDetail }) {
  const arts = Array.isArray(s.artifacts) ? s.artifacts.slice(0, 64) : [];
  const vs = s.verified_surface;
  const graphArtifacts = (s.evidence_graph?.nodes ?? []).filter((n) => n.kind === 'artifact' && n.digest).slice(0, 64);
  return (
    <dl className="kv">
      <dt>Package</dt>
      <dd>
        <DigestText d={s.package_digest} full />
      </dd>
      {vs && (
        <>
          <dt>Verify artifact</dt>
          <dd><DigestText d={vs.verify_artifact} full /></dd>
          <dt>Prepare artifact</dt>
          <dd><DigestText d={vs.prepare_artifact} full /></dd>
          <dt>Public artifacts</dt>
          <dd><DigestText d={vs.public_artifacts} full /></dd>
          <dt>Formal tree</dt>
          <dd><DigestText d={vs.formal_tree} full /></dd>
          <dt>Certificate</dt>
          <dd><code><T v={vs.certificate_decl} max={120} /></code></dd>
          <dt>Checker image</dt>
          <dd><DigestText d={vs.checker_image} full /></dd>
        </>
      )}
      {arts.map((a, i) => (
        <Fragment key={`a${i}`}>
          <dt><T v={a.label} max={60} /></dt>
          <dd><DigestText d={a.digest} full /></dd>
        </Fragment>
      ))}
      {arts.length === 0 &&
        graphArtifacts.map((n, i) => (
          <Fragment key={`g${i}`}>
            <dt><T v={n.label} max={60} /></dt>
            <dd><DigestText d={n.digest} full /></dd>
          </Fragment>
        ))}
      {!vs && arts.length === 0 && graphArtifacts.length === 0 && (
        <>
          <dt>Artifacts</dt>
          <dd className="muted">No built-artifact digests reported yet.</dd>
        </>
      )}
    </dl>
  );
}

export function BuildMeta({ s }: { s: SubmissionDetail }) {
  const b = s.build;
  return (
    <dl className="kv">
      <dt>Candidate</dt>
      <dd><T v={s.candidate_name} max={64} empty="(unnamed — manifest not yet validated)" /></dd>
      <dt>Agent</dt>
      <dd><T v={s.agent} max={64} /></dd>
      <dt>Backend family</dt>
      <dd><T v={s.backend_family} max={64} /> <span className="muted small">(self-declared label, not trusted)</span></dd>
      <dt>Change class</dt>
      <dd>{s.change_class ? <code>{s.change_class}</code> : <span className="muted">not yet classified</span>}</dd>
      <dt>Created</dt>
      <dd>{fmtTime(s.created_at)}</dd>
      <dt>Updated</dt>
      <dd>{fmtTime(s.updated_at)}</dd>
      <dt>Judge build</dt>
      <dd>
        {b ? (
          <>
            {b.reproducible ? <span className="ok">reproducible (two builds bit-identical)</span> : <span className="bad">not shown reproducible</span>}
            {b.build_ns != null && <> · {fmtNs(b.build_ns)}</>}
          </>
        ) : (
          <span className="muted">no build recorded yet</span>
        )}
      </dd>
      {b?.toolchain_image && (
        <>
          <dt>Build image</dt>
          <dd>
            <code className="wrap"><T v={b.toolchain_image} max={120} /></code>
          </dd>
        </>
      )}
    </dl>
  );
}

export function TrustSurface({ s }: { s: SubmissionDetail }) {
  const nodes = s.evidence_graph?.nodes ?? [];
  const assumptions =
    Array.isArray(s.assumptions) && s.assumptions.length > 0
      ? s.assumptions.slice(0, 64).map((a) => ({ id: a.id, detail: a.lean_decl ?? a.description ?? '' }))
      : nodes.filter((n) => n.kind === 'assumption').slice(0, 64).map((n) => ({ id: n.id, detail: n.label }));
  const tcb =
    Array.isArray(s.trusted_base) && s.trusted_base.length > 0
      ? s.trusted_base.slice(0, 64).map((t) => ({ id: t.id, label: t.label, digest: t.digest ?? null }))
      : nodes.filter((n) => n.kind === 'tcb_component').slice(0, 64).map((n) => ({ id: n.id, label: n.label, digest: n.digest ?? null }));
  return (
    <div className="two-col">
      <div>
        <h3>Assumptions</h3>
        {assumptions.length === 0 ? (
          <p className="small muted">None reported.</p>
        ) : (
          <ul className="plain">
            {assumptions.map((a, i) => (
              <li key={i}>
                <code><T v={a.id} max={80} /></code> <span className="small muted"><T v={a.detail} max={200} /></span>
              </li>
            ))}
          </ul>
        )}
        <p className="small muted">Every assumption must be on the challenge's security-profile allowlist.</p>
      </div>
      <div>
        <h3>Trusted base</h3>
        {tcb.length === 0 ? (
          <p className="small muted">None reported.</p>
        ) : (
          <ul className="plain">
            {tcb.map((t, i) => (
              <li key={i}>
                <T v={t.label} max={80} /> {t.digest && <DigestText d={t.digest} />}
              </li>
            ))}
          </ul>
        )}
        <p className="small muted">Components trusted without proof (e.g. Lean kernel, checker image, sandbox).</p>
      </div>
    </div>
  );
}

export function Logs({ s }: { s: SubmissionDetail }) {
  const logs = Array.isArray(s.logs) ? s.logs.slice(0, 16) : [];
  if (logs.length === 0) {
    return <p className="small muted">No logs published for this submission. Gate summaries above are the bounded diagnostics.</p>;
  }
  return (
    <div>
      {logs.map((l, i) => (
        <details key={i} className="log">
          <summary>
            <T v={l.name} max={60} />
            {l.stage && (
              <span className="muted">
                {' '}
                · <T v={l.stage} max={32} />
              </span>
            )}
            {l.truncated && <span className="muted"> (truncated by the judge)</span>}
          </summary>
          <TextBlock v={l.text} label={`log ${i + 1}`} />
        </details>
      ))}
      <p className="small muted">Logs are untrusted diagnostics from sandboxed candidate code, shown as plain text.</p>
    </div>
  );
}

export function EventStream({ status, events }: { status: StreamStatus; events: StreamEvent[] }) {
  const label: Record<StreamStatus, string> = {
    idle: 'not subscribed (submission decided)',
    connecting: 'connecting…',
    live: 'live',
    closed: 'closed',
    unsupported: 'live updates unsupported in this browser',
    error: 'error',
  };
  return (
    <div className="events">
      <p className="small">
        Live updates: <span className={`stream stream-${status}`}>{label[status]}</span>
      </p>
      {events.length > 0 && (
        <ol className="event-list" aria-live="polite" aria-label="Recent pipeline events">
          {events.slice(-12).map((e) => (
            <li key={e.seq}>
              <code>{e.type}</code> <span className="small">{e.text}</span>
            </li>
          ))}
        </ol>
      )}
    </div>
  );
}
