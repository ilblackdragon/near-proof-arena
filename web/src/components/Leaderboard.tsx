import type { BoardEntry, ChallengeDefinition } from '../api/types';
import { belongsTo, partition, type RankedEntry } from '../lib/board';
import { fmtBytes, fmtNs, fmtScoreCi, fmtTime } from '../lib/format';
import { AcceptedText, DecisionBadge, ReferenceBadge, RevokedBadge, TierBadge } from './Badges';
import { SubLink } from './Links';
import { T } from './Text';

function Row({ e, rank }: { e: BoardEntry; rank: number | null }) {
  return (
    <tr className={e.tier === 'demo' ? 'row-demo' : e.revoked ? 'row-revoked' : undefined}>
      <td className="num rank">{rank === null ? <span className="muted" aria-label="unranked">—</span> : rank}</td>
      <td>
        <SubLink id={e.submission_id}>
          <T v={e.candidate_name} max={64} empty="(unnamed — manifest not yet validated)" />
        </SubLink>
        <div className="small muted">
          by <T v={e.agent} max={64} /> · <T v={e.backend_family} max={48} />
        </div>
      </td>
      <td>
        <DecisionBadge decision={e.decision} /> <TierBadge tier={e.tier} />
        {e.revoked && <RevokedBadge />}
        <div className="small">
          <AcceptedText accepted={e.accepted} />
        </div>
      </td>
      <td className="num">{fmtScoreCi(e.score_milli, e.score_ci_milli)}</td>
      <td className="num">{fmtNs(e.prove_median_ns)}</td>
      <td className="num">{fmtNs(e.verify_median_ns)}</td>
      <td className="num">{fmtBytes(e.proof_bytes)}</td>
      <td className="num">{fmtBytes(e.peak_rss_bytes)}</td>
      <td className="small">
        <code><T v={e.hardware_profile} max={40} /></code>
      </td>
      <td className="small">
        <T v={e.scope} max={48} />
        {e.protocol_version !== undefined && <div className="muted">protocol v{e.protocol_version}</div>}
        {e.superseded_by && <div className="badge closed">SUPERSEDED</div>}
      </td>
      <td className="small">
        <code><T v={e.security_profile} max={48} /></code>
      </td>
      <td className="small nowrap">{fmtTime(e.submitted_at)}</td>
    </tr>
  );
}

function BoardTable({
  caption,
  rows,
}: {
  caption: string;
  rows: { e: BoardEntry; rank: number | null }[];
}) {
  return (
    <div className="table-wrap">
      <table className="data board">
        <caption className="sr-only">{caption}</caption>
        <thead>
          <tr>
            <th scope="col">Rank</th>
            <th scope="col">Candidate / agent</th>
            <th scope="col">Admission</th>
            <th scope="col">Score (95% CI)</th>
            <th scope="col">Prove median</th>
            <th scope="col">Verify median</th>
            <th scope="col">Proof size</th>
            <th scope="col">Peak RAM</th>
            <th scope="col">Hardware</th>
            <th scope="col">Scope</th>
            <th scope="col">Security</th>
            <th scope="col">Submitted</th>
          </tr>
        </thead>
        <tbody>
          {rows.map(({ e, rank }, i) => (
            <Row key={`${e.submission_id}-${i}`} e={e} rank={rank} />
          ))}
        </tbody>
      </table>
    </div>
  );
}

const unranked = (list: BoardEntry[]) => list.map((e) => ({ e, rank: null }));
const ranked = (list: RankedEntry[]) => list.map(({ entry, rank }) => ({ e: entry, rank }));

export function Leaderboard({
  entries,
  def,
  challengeId,
}: {
  entries: BoardEntry[];
  def: ChallengeDefinition;
  challengeId?: string;
}) {
  const b = partition(entries, def, challengeId);
  const foreign = challengeId ? entries.filter((e) => !belongsTo(e, challengeId)).length : 0;
  const isFormal = def.tier === 'formal';
  return (
    <div className="leaderboard">
      {foreign > 0 && (
        <p className="bad" role="alert">
          {foreign} entr{foreign === 1 ? 'y is' : 'ies are'} labelled with a different challenge id and are not ranked here.
        </p>
      )}
      <section className="board-section official" aria-labelledby="lb-official">
        <h2 id="lb-official">
          Official ranking <TierBadge tier="formal" />
        </h2>
        <p className="small muted">
          Only formal-tier submissions that the judge ADMITTED (every mandatory gate PASS) and that
          have not been revoked. Ranked by judge-measured score; higher is faster than the baseline
          (100 = baseline).
        </p>
        {!isFormal ? (
          <p className="empty" role="status">
            This is a <strong>{def.tier}</strong>-tier challenge. It has no official ranked board.
          </p>
        ) : b.official.length === 0 ? (
          <p className="empty" role="status">
            No formally admitted submissions yet.
          </p>
        ) : (
          <BoardTable caption="Official ranking" rows={ranked(b.official)} />
        )}
      </section>

      {b.formal_other.length > 0 && (
        <section className="board-section" aria-labelledby="lb-pending">
          <h2 id="lb-pending">Formal tier — not admitted or pending (unranked)</h2>
          <BoardTable caption="Formal tier, not admitted" rows={unranked(b.formal_other)} />
        </section>
      )}
      {b.revoked.length > 0 && (
        <section className="board-section revoked-section" aria-labelledby="lb-revoked">
          <h2 id="lb-revoked">
            <RevokedBadge /> Revoked (unranked)
          </h2>
          <p className="small muted">Admission was withdrawn after the fact. See each submission for the reason.</p>
          <BoardTable caption="Revoked" rows={unranked(b.revoked)} />
        </section>
      )}
      {b.reference.length > 0 && (
        <section className="board-section reference-section" aria-labelledby="lb-ref">
          <h2 id="lb-ref">
            <ReferenceBadge /> Reference baseline (unranked)
          </h2>
          <p className="small muted">The baseline the score is normalised against. Not a competitor.</p>
          <BoardTable caption="Reference" rows={unranked(b.reference)} />
        </section>
      )}
      {b.experimental.length > 0 && (
        <section className="board-section experimental-section" aria-labelledby="lb-exp">
          <h2 id="lb-exp">
            <TierBadge tier="experimental" /> Experimental (unranked)
          </h2>
          <p className="small muted">
            Tested and timed, but without the full formal obligations. Not comparable to the official
            ranking.
          </p>
          <BoardTable caption="Experimental" rows={unranked(b.experimental)} />
        </section>
      )}
      {b.demo.length > 0 && (
        <section className="board-section demo-section" aria-labelledby="lb-demo">
          <h2 id="lb-demo">
            <TierBadge tier="demo" /> DEMO results — never ranked
          </h2>
          <p className="demo-warning">
            DEMO: plumbing demonstrations that may use simulated components or an unsafe dev sandbox.
            These results prove nothing about NEAR state transitions.
          </p>
          <BoardTable caption="Demo results" rows={unranked(b.demo)} />
        </section>
      )}
    </div>
  );
}
