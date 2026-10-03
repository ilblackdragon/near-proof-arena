import { STAGES, type Decision, type GateResult, type ObligationId, type Stage } from '../api/types';
import { DecisionBadge } from './Badges';

/** Which pipeline stage produces each gate (CONTRACTS §6/§7). */
const GATE_STAGE: Record<ObligationId, Stage> = {
  PKG_WELLFORMED: 'VALIDATED',
  BUILD_REPRODUCIBLE: 'BUILT',
  ARTIFACT_BINDING: 'BUILT',
  FORMAL_SEMANTIC_SOUNDNESS: 'FORMAL_CHECKED',
  FORMAL_SEMANTIC_COMPLETENESS: 'FORMAL_CHECKED',
  FORMAL_CRYPTO_SOUNDNESS: 'FORMAL_CHECKED',
  FORMAL_IMPL_CONNECTION: 'FORMAL_CHECKED',
  FORMAL_ZK: 'FORMAL_CHECKED',
  AXIOM_AUDIT: 'FORMAL_CHECKED',
  CONFORMANCE_DIFFERENTIAL: 'CONFORMANCE_CHECKED',
  ADVERSARIAL_PROOFS: 'CONFORMANCE_CHECKED',
  PROVER_RELIABILITY: 'CONFORMANCE_CHECKED',
  RESOURCE_LIMITS: 'CONFORMANCE_CHECKED',
  BENCHMARK: 'BENCHMARKED',
};

type StageState = 'done' | 'current' | 'todo' | 'failed' | 'not_run';

/**
 * Per-stage state. While running, stages before `stage` are done. Once a
 * decision exists, a stage counts as done only if it produced gate results:
 * a cancelled or fail-fast run reaches DECIDED without running later stages,
 * and those are shown as "not run" rather than as passed.
 */
export function stageStates(stage: Stage, decision: Decision | null | undefined, gates: GateResult[]): StageState[] {
  const idx = STAGES.indexOf(stage);
  if (decision == null || decision === 'ADMITTED') {
    return STAGES.map((s, i) =>
      idx < 0 ? 'todo' : i < idx ? 'done' : i === idx ? (s === 'DECIDED' ? 'done' : 'current') : 'todo',
    );
  }
  const ran = new Set<Stage>();
  const failed = new Set<Stage>();
  for (const g of gates) {
    const st = GATE_STAGE[g.gate];
    if (!st) continue;
    ran.add(st);
    if (g.status === 'FAIL' || g.status === 'UNKNOWN') failed.add(st);
  }
  return STAGES.map((s) =>
    s === 'RECEIVED' || s === 'DECIDED' ? 'done' : failed.has(s) ? 'failed' : ran.has(s) ? 'done' : 'not_run',
  );
}

const SR: Record<StageState, string> = {
  done: ' (complete)',
  current: ' (in progress)',
  todo: ' (not reached)',
  failed: ' (failed or unknown)',
  not_run: ' (not run)',
};

export function StageProgress({
  stage,
  decision,
  gates,
}: {
  stage: Stage;
  decision?: Decision | null;
  gates: GateResult[];
}) {
  const states = stageStates(stage, decision, gates);
  const idx = STAGES.indexOf(stage);
  return (
    <div className="stages">
      <ol className="stage-list" aria-label="Pipeline stages">
        {STAGES.map((s, i) => (
          <li key={s} className={`stage ${states[i]}`} aria-current={i === idx && decision == null ? 'step' : undefined}>
            <span className="stage-dot" aria-hidden="true" />
            <span className="stage-name">{s.replace(/_/g, ' ')}</span>
            {states[i] === 'not_run' && <span className="stage-note"> · not run</span>}
            <span className="sr-only">{SR[states[i]]}</span>
          </li>
        ))}
      </ol>
      {idx < 0 && <p className="bad small">Unknown stage reported by the server.</p>}
      <p className="decision-line">
        Decision: <DecisionBadge decision={decision} />
      </p>
    </div>
  );
}
