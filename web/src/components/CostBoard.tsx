import type { BoardEntry, ChallengeDefinition } from '../api/types';
import { costBoard } from '../lib/board';
import { fmtBytes, fmtFusd, fmtInt, fmtNs, fmtScoreCi } from '../lib/format';
import { SubLink } from './Links';
import { T } from './Text';

/** Per-class cost components of one entry: the "why" of its cost score. */
function Breakdown({ e }: { e: BoardEntry }) {
  const c = e.cost;
  if (!c) return <span className="muted">—</span>;
  return (
    <table className="data cost-breakdown small">
      <thead>
        <tr>
          <th scope="col">Class</th>
          <th scope="col">Prove</th>
          <th scope="col">N_v × verify</th>
          <th scope="col">N_v × bytes</th>
          <th scope="col">Total / batch</th>
          <th scope="col">vs reference</th>
          <th scope="col">Verify / batch</th>
          <th scope="col">Proof / batch</th>
        </tr>
      </thead>
      <tbody>
        {c.classes.map((k) => (
          <tr key={k.class_id}>
            <td>
              <T v={k.class_id} max={32} />
            </td>
            <td className="num">{fmtFusd(k.prove_fusd + k.prepare_fusd)}</td>
            <td className="num">{fmtFusd(k.verify_fusd)}</td>
            <td className="num">{fmtFusd(k.bandwidth_fusd + k.storage_fusd)}</td>
            <td className="num">{fmtFusd(k.total_fusd)}</td>
            <td className="num">
              {k.baseline_total_fusd > 0 ? `${(k.total_fusd / k.baseline_total_fusd).toFixed(2)}×` : '—'}
            </td>
            <td className="num">{fmtNs(k.verify_ns)}</td>
            <td className="num">{fmtBytes(k.proof_bytes)}</td>
          </tr>
        ))}
      </tbody>
    </table>
  );
}

export function CostBoard({
  entries,
  def,
  challengeId,
}: {
  entries: BoardEntry[];
  def: ChallengeDefinition;
  challengeId?: string;
}) {
  const sc = def.scoring;
  if (sc?.kind !== 'cost_v1' || !sc.price_model) return null;
  const pm = sc.price_model;
  const rows = costBoard(entries, def, challengeId);
  return (
    <section className="board-section cost-section" aria-labelledby="lb-cost">
      <h2 id="lb-cost">Cost board (cost_v1)</h2>
      <p className="small muted">
        Same admitted entries, ranked by system cost per proved chunk instead of prove time: prove on the
        prover plus, for each of N_v = {fmtInt(pm.validators_per_chunk)} validators, verify on{' '}
        {fmtInt(pm.verifier_vcpus)} vCPUs and the proof bytes. 100 = the reference candidate&apos;s cost; higher is
        cheaper. Price model <code><T v={`${pm.id}@v${pm.version}`} max={64} /></code> ({pm.status}),{' '}
        <code className="wrap">{sc.price_model_digest}</code>. Not comparable with the speed score above.
      </p>
      {rows.length === 0 ? (
        <p className="empty" role="status">
          No admitted submission has a cost score under this price model yet.
        </p>
      ) : (
        <div className="table-wrap">
          <table className="data board cost-board">
            <caption className="sr-only">Cost board</caption>
            <thead>
              <tr>
                <th scope="col">Rank</th>
                <th scope="col">Candidate / agent</th>
                <th scope="col">Cost score (95% CI)</th>
                <th scope="col">Speed score</th>
                <th scope="col">Per-class cost (why)</th>
              </tr>
            </thead>
            <tbody>
              {rows.map(({ entry: e, rank }) => (
                <tr key={e.submission_id}>
                  <td className="num rank">{rank}</td>
                  <td>
                    <SubLink id={e.submission_id}>
                      <T v={e.candidate_name} max={64} empty="(unnamed)" />
                    </SubLink>
                    <div className="small muted">
                      by <T v={e.agent} max={64} /> · <T v={e.backend_family} max={48} />
                    </div>
                  </td>
                  <td className="num">{fmtScoreCi(e.cost?.score_milli, e.cost?.score_ci_milli)}</td>
                  <td className="num muted">{fmtScoreCi(e.score_milli, e.score_ci_milli)}</td>
                  <td>
                    <Breakdown e={e} />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </section>
  );
}
