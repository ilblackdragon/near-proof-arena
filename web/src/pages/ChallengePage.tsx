import { Link, useParams } from 'react-router-dom';
import { getChallenge, getLeaderboard } from '../api/client';
import { useAsync, useChallengeVerification } from '../api/hooks';
import { AsyncView } from '../components/AsyncView';
import { TierBadge } from '../components/Badges';
import { ChallengeFacts, ExcludesCallout } from '../components/ChallengeInfo';
import { Leaderboard } from '../components/Leaderboard';
import { T } from '../components/Text';
import { isChallengeId } from '../lib/ids';
import type { ChallengeRecord } from '../api/types';

export function ChallengePage() {
  const { id = '' } = useParams();
  if (!isChallengeId(id)) {
    return (
      <section>
        <h1>Invalid challenge id</h1>
        <p>
          Challenge ids look like <code>chl_</code> followed by 32 hex characters. <Link to="/">All challenges</Link>
        </p>
      </section>
    );
  }
  return <ChallengeView id={id} />;
}

function ChallengeView({ id }: { id: string }) {
  const [state] = useAsync((s) => getChallenge(id, s), [id]);
  return (
    <AsyncView state={state} what="challenge">
      {(c) => <ChallengeBody c={c} />}
    </AsyncView>
  );
}

function ChallengeBody({ c }: { c: ChallengeRecord }) {
  const verify = useChallengeVerification(c);
  const [board] = useAsync((s) => getLeaderboard(c.id, s), [c.id]);
  const d = c.definition;
  return (
    <section>
      <p className="crumbs">
        <Link to="/">Challenges</Link> /
      </p>
      <h1>
        <T v={d.name} max={120} /> <TierBadge tier={d.tier} />
      </h1>
      <p className="mono small muted wrap">{c.id}</p>
      {d.tier === 'demo' && (
        <p className="demo-warning" role="note">
          DEMO challenge: results here are plumbing demonstrations and are never ranked.
        </p>
      )}
      <ExcludesCallout c={c} />
      <h2 className="section-h">Leaderboard</h2>
      <p className="small">
        <Link to={`/submissions?challenge=${encodeURIComponent(c.id)}`}>All submissions for this challenge →</Link>
      </p>
      <AsyncView state={board} what="leaderboard">
        {(entries) => <Leaderboard entries={entries} def={d} />}
      </AsyncView>
      <h2 className="section-h">Definition</h2>
      <ChallengeFacts c={c} verify={verify} />
    </section>
  );
}
