import { listChallenges } from '../api/client';
import { useAsync } from '../api/hooks';
import { AsyncView } from '../components/AsyncView';
import { TierBadge } from '../components/Badges';
import { ScopeKindLabel } from '../components/ChallengeInfo';
import { ChlLink } from '../components/Links';
import { T } from '../components/Text';

export function ChallengesPage() {
  const [state] = useAsync((s) => listChallenges(s), []);
  return (
    <section>
      <h1>Challenges</h1>
      <p className="lede">
        Each challenge is an immutable, governance-signed definition: the exact NEAR semantics to be
        proven, what is explicitly excluded, the security profile, the hardware and the workload
        suite. Only <strong>formal</strong>-tier challenges have an official ranked board.
      </p>
      <AsyncView state={state} what="challenges">
        {(list) =>
          list.length === 0 ? (
            <p className="empty">No challenges are published.</p>
          ) : (
            <div className="table-wrap">
              <table className="data">
                <thead>
                  <tr>
                    <th scope="col">Challenge</th>
                    <th scope="col">Tier</th>
                    <th scope="col">Scope</th>
                    <th scope="col">Excludes</th>
                    <th scope="col">nearcore / protocol</th>
                    <th scope="col">Security profile</th>
                    <th scope="col">Suite</th>
                  </tr>
                </thead>
                <tbody>
                  {list.map((c) => {
                    const d = c.definition;
                    return (
                      <tr key={c.id} className={d.tier === 'demo' ? 'row-demo' : undefined}>
                        <td>
                          <ChlLink id={c.id}>
                            <T v={d.name} max={80} />
                          </ChlLink>
                          <div className="mono small muted">{c.id}</div>
                        </td>
                        <td>
                          <TierBadge tier={d.tier} />
                        </td>
                        <td>
                          <ScopeKindLabel kind={d.semantic_scope.kind} />
                          <div className="small muted">
                            <T v={d.semantic_scope.name} max={60} />
                            {d.semantic_scope.restrictions.length > 0 &&
                              ` · ${d.semantic_scope.restrictions.length} restriction(s)`}
                          </div>
                        </td>
                        <td className="small">
                          {d.semantic_scope.excludes.length === 0
                            ? 'none listed'
                            : d.semantic_scope.excludes.slice(0, 4).map((x, i) => (
                                <code key={i} className="sp excl">
                                  <T v={x} max={40} />
                                </code>
                              ))}
                          {d.semantic_scope.excludes.length > 4 && ` +${d.semantic_scope.excludes.length - 4} more`}
                        </td>
                        <td className="small">
                          <T v={d.nearcore.tag} max={40} /> · v{d.protocol_version}
                        </td>
                        <td className="small">
                          <code>
                            <T v={d.security_profile.id} max={48} />
                          </code>
                        </td>
                        <td className="small">
                          <code>
                            <T v={d.workload_suite.revision} max={32} />
                          </code>
                        </td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            </div>
          )
        }
      </AsyncView>
    </section>
  );
}
