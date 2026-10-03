import { STAGES, type Decision, type Stage } from '../api/types';
import { DecisionBadge } from './Badges';

export function StageProgress({ stage, decision }: { stage: Stage; decision?: Decision | null }) {
  const idx = STAGES.indexOf(stage);
  return (
    <div className="stages">
      <ol className="stage-list" aria-label="Pipeline stages">
        {STAGES.map((s, i) => {
          const state = idx < 0 ? 'todo' : i < idx ? 'done' : i === idx ? (s === 'DECIDED' ? 'done' : 'current') : 'todo';
          return (
            <li key={s} className={`stage ${state}`} aria-current={i === idx ? 'step' : undefined}>
              <span className="stage-dot" aria-hidden="true" />
              <span className="stage-name">{s.replace(/_/g, ' ')}</span>
              <span className="sr-only">{state === 'done' ? ' (complete)' : state === 'current' ? ' (in progress)' : ' (not reached)'}</span>
            </li>
          );
        })}
      </ol>
      {idx < 0 && <p className="bad small">Unknown stage reported by the server.</p>}
      <p className="decision-line">
        Decision: <DecisionBadge decision={decision} />
      </p>
    </div>
  );
}
