import type { BenchmarkResult } from '../api/types';
import { fmtBytes, fmtNs, fmtPpm, fmtScoreCi } from '../lib/format';
import { T } from './Text';

export function PerfTable({ b, accepted }: { b: BenchmarkResult; accepted?: boolean | null }) {
  return (
    <div>
      <dl className="kv inline-kv">
        <dt>Score</dt>
        <dd>
          {fmtScoreCi(b.score_milli, b.score_ci_milli)}
          {accepted !== true && b.score_milli != null && <span className="muted"> (diagnostic only — not admitted)</span>}
        </dd>
        <dt>Hardware</dt>
        <dd>
          <code><T v={b.hardware_profile} /></code>
        </dd>
        <dt>Suite</dt>
        <dd>
          <code><T v={b.suite_revision} /></code>
        </dd>
        <dt>Prepare</dt>
        <dd>{fmtNs(b.prepare_ns)}</dd>
        <dt>Public artifacts</dt>
        <dd>{fmtBytes(b.public_artifact_bytes)}</dd>
        <dt>Measured by</dt>
        <dd>
          <T v={b.measured_by} />
        </dd>
      </dl>
      {b.classes.length === 0 ? (
        <p className="empty">No per-workload measurements.</p>
      ) : (
        <div className="table-wrap">
          <table className="data">
            <caption>Per-workload measurements (judge-measured)</caption>
            <thead>
              <tr>
                <th scope="col">Workload class</th>
                <th scope="col">Weight</th>
                <th scope="col">Prove median</th>
                <th scope="col">MAD</th>
                <th scope="col">Baseline</th>
                <th scope="col">Speed-up</th>
                <th scope="col">Cold</th>
                <th scope="col">Verify median</th>
                <th scope="col">Max proof</th>
                <th scope="col">Peak RAM</th>
                <th scope="col">Runs</th>
              </tr>
            </thead>
            <tbody>
              {b.classes.slice(0, 64).map((c, i) => (
                <tr key={i}>
                  <th scope="row">
                    <code><T v={c.class_id} max={48} /></code>
                  </th>
                  <td className="num">{fmtPpm(c.weight_ppm)}</td>
                  <td className="num">{fmtNs(c.median_ns)}</td>
                  <td className="num">{fmtNs(c.mad_ns)}</td>
                  <td className="num">{fmtNs(c.baseline_ns)}</td>
                  <td className="num">{c.median_ns > 0 ? `${(c.baseline_ns / c.median_ns).toFixed(2)}×` : '—'}</td>
                  <td className="num">{fmtNs(c.cold_ns)}</td>
                  <td className="num">{fmtNs(c.verify_median_ns)}</td>
                  <td className="num">{fmtBytes(c.proof_bytes_max)}</td>
                  <td className="num">{fmtBytes(c.peak_rss_bytes)}</td>
                  <td className="num">{Array.isArray(c.runs_ns) ? c.runs_ns.length : '—'}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </div>
  );
}
