import type { ChallengeRecord } from '../api/types';
import type { VerifyState } from '../api/hooks';
import { fmtBytes, fmtInt, fmtPpm, fmtTime } from '../lib/format';
import { TierBadge } from './Badges';
import { DigestText } from './Digest';
import { ChlLink } from './Links';
import { T } from './Text';
import type { ChallengeLineageHop } from '../api/hooks';

/**
 * Supersession / closed state (docs/PROTOCOL_UPGRADES.md). A superseded
 * challenge is closed to new submissions; its board stays attached to the
 * definition it was measured against.
 */
export function ChallengeStatusBanner({ c, where }: { c: ChallengeRecord; where: 'challenge' | 'leaderboard' }) {
  if (c.superseded_by) {
    return (
      <div className="superseded-banner" role="alert">
        <strong>Superseded.</strong> This challenge has been replaced by{' '}
        <ChlLink id={c.superseded_by}>
          <span className="mono">{String(c.superseded_by).slice(0, 40)}</span>
        </ChlLink>
        . It is closed to new submissions.
        {where === 'leaderboard'
          ? ' This board is frozen: its results were measured under this definition (protocol version ' +
            c.definition.protocol_version +
            ') and are not comparable with the successor board.'
          : ' Results recorded here remain attached to this definition.'}
      </div>
    );
  }
  if (!c.open) {
    return (
      <div className="closed-banner" role="status">
        <strong>Closed.</strong> This challenge is not accepting new submissions (the API answers{' '}
        <code>409 challenge_closed</code>). Existing results remain visible.
      </div>
    );
  }
  return null;
}

/** "Supersedes" chain, newest first: this challenge, then each predecessor. */
export function SupersessionLineage({ c, hops }: { c: ChallengeRecord; hops: ChallengeLineageHop[] }) {
  if (!c.definition.supersedes && !c.superseded_by) return null;
  return (
    <section className="card" aria-labelledby="sup-h">
      <h2 id="sup-h">Challenge lineage</h2>
      <ol className="lineage" aria-label="Challenge supersession chain, newest first">
        {c.superseded_by && (
          <li>
            <ChlLink id={c.superseded_by} /> <span className="badge tier-formal">SUCCESSOR</span>
          </li>
        )}
        <li>
          <strong>this</strong> <code className="mono">{c.id}</code> · protocol v{c.definition.protocol_version}{' '}
          {c.superseded_by ? <span className="badge closed">SUPERSEDED</span> : !c.open && <span className="badge closed">CLOSED</span>}
        </li>
        {hops.map((h, i) => (
          <li key={i}>
            supersedes <ChlLink id={h.id} />{' '}
            {h.c ? (
              <>
                <T v={h.c.definition.name} max={60} /> · protocol v{h.c.definition.protocol_version}{' '}
                {!h.c.open && <span className="badge closed">{h.c.superseded_by ? 'SUPERSEDED' : 'CLOSED'}</span>}
              </>
            ) : (
              <span className="bad">
                unavailable: <T v={h.error} max={80} />
              </span>
            )}
          </li>
        ))}
      </ol>
    </section>
  );
}

export function ScopeKindLabel({ kind }: { kind: string }) {
  if (kind === 'full_chunk_transition') return <span className="scope full">Full chunk transition</span>;
  if (kind === 'subset') return <span className="scope subset">SUBSET of NEAR semantics</span>;
  return <span className="scope">Unknown scope kind</span>;
}

/** The "what is NOT proven" callout. Always rendered, even when empty. */
export function ExcludesCallout({ c }: { c: ChallengeRecord }) {
  const s = c.definition.semantic_scope;
  return (
    <section className="callout excludes" aria-labelledby="excl-h">
      <h2 id="excl-h">What an admitted proof does NOT establish</h2>
      {s.excludes.length === 0 ? (
        <p>
          The challenge lists <strong>no exclusions</strong>. Check the restrictions below and the
          formal relation for the exact claim.
        </p>
      ) : (
        <ul className="excl-list">
          {s.excludes.map((x, i) => (
            <li key={i}>
              <code>
                <T v={x} max={120} />
              </code>
            </li>
          ))}
        </ul>
      )}
      <p className="scope-line">
        Scope: <ScopeKindLabel kind={s.kind} /> · granularity <code><T v={s.granularity} /></code>
      </p>
      {c.definition.security_profile?.privacy !== 'zero_knowledge' && (
        <p className="privacy-line">
          <strong>Validity only, not privacy:</strong> this challenge's security profile is{' '}
          <code>validity_only</code>. Admission proves that the claim is sound for the formal relation. It does not
          prove that the proof hides the witness (no zero-knowledge guarantee).
        </p>
      )}
      {s.restrictions.length > 0 && (
        <>
          <h3>Restrictions ({s.restrictions.length})</h3>
          <ul className="restrictions">
            {s.restrictions.map((r, i) => (
              <li key={i}>
                <code>
                  <T v={r.id} max={80} />
                </code>{' '}
                — <T v={r.text} max={400} />
              </li>
            ))}
          </ul>
        </>
      )}
    </section>
  );
}

function Row({ k, children }: { k: string; children: React.ReactNode }) {
  return (
    <>
      <dt>{k}</dt>
      <dd>{children}</dd>
    </>
  );
}

export function VerifyLine({ v }: { v: VerifyState }) {
  switch (v.status) {
    case 'pending':
      return <span className="muted">recomputing digest…</span>;
    case 'verified':
      return <span className="ok">✓ id and digest recomputed in this browser (JCS + SHA-256)</span>;
    case 'unavailable':
      return <span className="warn">not verified locally: <T v={v.reason} /></span>;
    case 'mismatch':
      return (
        <span className="bad" role="alert">
          ✗ MISMATCH — <T v={v.reason} />. Do not trust this challenge record.
        </span>
      );
  }
}

export function ChallengeFacts({ c, verify }: { c: ChallengeRecord; verify: VerifyState }) {
  const d = c.definition;
  const sp = d.security_profile;
  const hw = d.hardware_profile;
  const ws = d.workload_suite;
  return (
    <div className="facts-grid">
      <section className="card">
        <h2>Identity</h2>
        <dl className="kv">
          <Row k="Challenge id">
            <code className="mono wrap">{c.id}</code>
          </Row>
          <Row k="Digest">
            <DigestText d={c.digest} full />
          </Row>
          <Row k="Integrity">
            <VerifyLine v={verify} />
          </Row>
          <Row k="Tier">
            <TierBadge tier={d.tier} />
          </Row>
          <Row k="Submissions">{c.open ? 'open' : <span className="warn">closed</span>}</Row>
          <Row k="Signed by">
            <code className="mono wrap"><T v={c.governance_key} max={80} /></code>
          </Row>
          <Row k="Signature">
            <code className="mono wrap small"><T v={c.signature} max={140} /></code>
          </Row>
          <Row k="Registered">
            {fmtTime(c.registered_at)} by <T v={c.registered_by} max={64} />
          </Row>
          <Row k="Season">
            <T v={d.season} />
          </Row>
          <Row k="Created">{fmtTime(d.created_at)}</Row>
          <Row k="Supersedes">{d.supersedes ? <ChlLink id={d.supersedes} /> : '—'}</Row>
          <Row k="Superseded by">{c.superseded_by ? <ChlLink id={c.superseded_by} /> : '—'}</Row>
        </dl>
      </section>
      <section className="card">
        <h2>NEAR pin</h2>
        <dl className="kv">
          <Row k="nearcore">
            <T v={d.nearcore.tag} /> @ <code className="mono wrap"><T v={d.nearcore.commit} max={64} /></code>
          </Row>
          <Row k="Repository">
            <T v={d.nearcore.repo} max={200} />
          </Row>
          <Row k="Protocol version">{fmtInt(d.protocol_version)}</Row>
          <Row k="Chain id">
            <T v={d.chain_id} />
          </Row>
          <Row k="Runtime config">
            <DigestText d={d.runtime_config_digest} />
          </Row>
          <Row k="Claim encoding">
            <T v={d.claim_encoding.format} /> (max claim {fmtBytes(d.claim_encoding.max_claim_bytes)})
          </Row>
          <Row k="Formal relation">
            <code className="wrap"><T v={d.semantic_scope.formal_spec.relation_decl} max={200} /></code>
          </Row>
        </dl>
      </section>
      <section className="card">
        <h2>Security profile</h2>
        <dl className="kv">
          <Row k="Profile">
            <code><T v={sp.id} /></code>
          </Row>
          <Row k="Privacy">{sp.privacy === 'zero_knowledge' ? 'zero-knowledge' : 'validity only (not zero-knowledge)'}</Row>
          <Row k="Adversary">
            <T v={sp.adversary} /> <span className="muted">(implies no post-quantum security)</span>
          </Row>
          <Row k="Target">{fmtInt(sp.target_bits)} bits</Row>
          <Row k="Model">
            <T v={sp.model} />, setup <T v={sp.setup_model} />
          </Row>
          <Row k="Allowed assumptions">
            {sp.allowed_assumptions.length === 0 ? (
              'none'
            ) : (
              <ul className="inline-list">
                {sp.allowed_assumptions.map((a, i) => (
                  <li key={i}>
                    <code><T v={a} /></code>
                  </li>
                ))}
              </ul>
            )}
          </Row>
          <Row k="Query bounds">
            prover 2^{fmtInt(sp.max_prover_queries_log2)}, hash 2^{fmtInt(sp.max_hash_queries_log2)}, deployment 2^
            {fmtInt(sp.deployment_proofs_log2)} proofs
          </Row>
        </dl>
      </section>
      <section className="card">
        <h2>Hardware &amp; workload</h2>
        <dl className="kv">
          <Row k="Hardware profile">
            <code><T v={hw.id} /></code>
          </Row>
          <Row k="Machine">
            <T v={hw.cpu_model} />, {fmtInt(hw.vcpus)} vCPU, {fmtBytes(hw.ram_bytes)} RAM, GPU:{' '}
            {hw.gpu ? <T v={hw.gpu} /> : 'none'}
          </Row>
          <Row k="Suite revision">
            <code><T v={ws.revision} /></code>
          </Row>
          <Row k="Measurement">
            {fmtInt(d.measurement.warmup_runs)} warmup + {fmtInt(d.measurement.measured_runs)} measured runs,{' '}
            <T v={d.measurement.aggregation} />,{' '}
            {d.measurement.invocation_mode === 'vm_per_batch' ? 'one VM per batch' : 'one VM per invocation'}
          </Row>
          {d.formal_params && (
            <Row k="Formal params">
              verify fuel {fmtInt(d.formal_params.verify_fuel)}, max proof {fmtBytes(d.formal_params.max_proof_bytes)}, reduction fuel{' '}
              {fmtInt(d.formal_params.max_reduction_fuel)}
            </Row>
          )}
          <Row k="Limits">
            proof ≤ {fmtBytes(d.resource_limits.max_proof_bytes)}, verify ≤ {fmtInt(d.resource_limits.max_verify_ms)} ms, RAM ≤{' '}
            {fmtBytes(d.resource_limits.max_ram_bytes)}
          </Row>
        </dl>
        {ws.classes.length > 0 && (
          <table className="mini">
            <caption>Workload classes</caption>
            <thead>
              <tr>
                <th scope="col">Class</th>
                <th scope="col">Weight</th>
                <th scope="col">Batch</th>
              </tr>
            </thead>
            <tbody>
              {ws.classes.map((w, i) => (
                <tr key={i}>
                  <td>
                    <code><T v={w.id} /></code>
                    <div className="muted small"><T v={w.description} max={200} /></div>
                  </td>
                  <td className="num">{fmtPpm(w.weight_ppm)}</td>
                  <td className="num">{fmtInt(w.batch_size)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        )}
      </section>
      <section className="card span2">
        <h2>Required obligations</h2>
        <ul className="chips">
          {d.required_obligations.map((o, i) => (
            <li key={i} className="chip">
              <T v={o} />
            </li>
          ))}
        </ul>
        {d.not_applicable_gates.length > 0 && (
          <p className="small muted">
            May be NOT_APPLICABLE under this challenge:{' '}
            {d.not_applicable_gates.map((g, i) => (
              <code key={i} className="sp">
                <T v={g} />
              </code>
            ))}
          </p>
        )}
        <p className="small muted">
          Toolchain <code><T v={d.toolchain_policy.lean_toolchain} /></code>; rechecked by{' '}
          {d.toolchain_policy.recheckers.length === 0 ? 'no independent rechecker' : d.toolchain_policy.recheckers.map((r, i) => (
            <code key={i} className="sp"><T v={r} /></code>
          ))}
          ; {d.toolchain_policy.axiom_allowlist.length} allowlisted axioms.
        </p>
      </section>
    </div>
  );
}
