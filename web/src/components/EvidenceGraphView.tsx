import type { EdgeStatus, EvidenceEdge, EvidenceGraph, EvidenceNode, NodeKind } from '../api/types';
import { displayInline } from '../lib/text';
import { EdgeStatusBadge } from './Badges';
import { DigestText } from './Digest';
import { T } from './Text';

/**
 * Evidence graph (CONTRACTS §8). Every edge is drawn and listed; MISSING edges
 * are red and dashed, drawn on top, counted in an alert, and never hidden or
 * truncated. CHECKED / TRUSTED / TESTED use distinct colour AND line pattern
 * so they are distinguishable without colour.
 */

const MAX_NODES = 200;
const MAX_DRAWN_EDGES = 600;

const KIND_ORDER: NodeKind[] = [
  'nearcore_source',
  'formal_semantics',
  'theorem',
  'backend_semantics',
  'assumption',
  'artifact',
  'tcb_component',
  'test_suite',
  'measurement',
];
const COLUMN: Record<NodeKind, number> = {
  nearcore_source: 0,
  formal_semantics: 0,
  theorem: 1,
  backend_semantics: 1,
  assumption: 1,
  artifact: 2,
  tcb_component: 2,
  test_suite: 3,
  measurement: 3,
};
const KIND_LABEL: Record<NodeKind, string> = {
  nearcore_source: 'nearcore source',
  formal_semantics: 'formal semantics',
  theorem: 'theorem',
  backend_semantics: 'backend semantics',
  assumption: 'assumption',
  artifact: 'artifact',
  tcb_component: 'trusted base',
  test_suite: 'test suite',
  measurement: 'measurement',
};
const STATUS_ORDER: Record<EdgeStatus, number> = { checked: 0, trusted: 1, tested: 2, missing: 3 };
const VALID_STATUS = new Set<string>(['checked', 'trusted', 'tested', 'missing']);

const W = 196;
const H = 48;
const COL_GAP = 96;
const ROW_GAP = 18;
const PAD = 24;

interface Placed {
  node: EvidenceNode;
  x: number;
  y: number;
  col: number;
}

export function layout(g: EvidenceGraph) {
  const nodes = g.nodes.slice(0, MAX_NODES);
  const cols: EvidenceNode[][] = [[], [], [], []];
  for (const kind of KIND_ORDER) {
    for (const n of nodes) if (n.kind === kind) cols[COLUMN[kind]].push(n);
  }
  // Unknown kinds go in the last column rather than disappearing.
  for (const n of nodes) if (!(n.kind in COLUMN)) cols[3].push(n);
  const placed = new Map<string, Placed>();
  cols.forEach((list, col) =>
    list.forEach((node, row) => {
      if (!placed.has(node.id)) {
        placed.set(node.id, { node, col, x: PAD + col * (W + COL_GAP), y: PAD + 20 + row * (H + ROW_GAP) });
      }
    }),
  );
  const rows = Math.max(1, ...cols.map((c) => c.length));
  return {
    placed,
    width: PAD * 2 + 4 * W + 3 * COL_GAP,
    height: PAD * 2 + 20 + rows * (H + ROW_GAP),
  };
}

function edgePath(a: Placed, b: Placed): { d: string; mx: number; my: number } {
  const ay = a.y + H / 2;
  const by = b.y + H / 2;
  if (a.col === b.col) {
    const x = a.x + W;
    const bulge = 46 + Math.min(40, Math.abs(ay - by) / 6);
    return { d: `M${x},${ay} C${x + bulge},${ay} ${x + bulge},${by} ${x},${by}`, mx: x + bulge * 0.75, my: (ay + by) / 2 };
  }
  const forward = a.col < b.col;
  const x1 = forward ? a.x + W : a.x;
  const x2 = forward ? b.x : b.x + W;
  const dx = (x2 - x1) / 2;
  return { d: `M${x1},${ay} C${x1 + dx},${ay} ${x2 - dx},${by} ${x2},${by}`, mx: (x1 + x2) / 2, my: (ay + by) / 2 };
}

function Legend() {
  const items: [EdgeStatus, string][] = [
    ['checked', 'machine-checked (kernel proof, digest equality)'],
    ['trusted', 'approved trusted-base entry (not proven)'],
    ['tested', 'only tested (differential / fuzz) — not a proof'],
    ['missing', 'NO evidence'],
  ];
  return (
    <ul className="legend" aria-label="Edge legend">
      {items.map(([s, t]) => (
        <li key={s}>
          <svg width="44" height="12" aria-hidden="true">
            <line x1="2" y1="6" x2="42" y2="6" className={`edge edge-${s}`} />
          </svg>
          <EdgeStatusBadge status={s} /> <span className="small">{t}</span>
        </li>
      ))}
    </ul>
  );
}

export function EvidenceGraphView({ graph }: { graph: EvidenceGraph | null | undefined }) {
  if (!graph) {
    return (
      <p className="empty warn-box" role="status">
        No evidence graph has been recorded for this submission. Absence of a graph means nothing has
        been shown to connect the NEAR semantics to the certified artifacts.
      </p>
    );
  }
  const { placed, width, height } = layout(graph);
  // An edge with an unrecognised status is shown as MISSING evidence, never dropped.
  const edges: EvidenceEdge[] = graph.edges.map((e) =>
    VALID_STATUS.has(e.status) ? e : { ...e, status: 'missing', note: `[invalid status reported] ${String(e.note ?? '')}` },
  );
  const invalid = graph.edges.length - graph.edges.filter((e) => VALID_STATUS.has(e.status)).length;
  const missing = edges.filter((e) => e.status === 'missing');
  // Missing edges first so a draw cap can never drop them; drawn last (on top).
  const drawable = [...edges]
    .sort((a, b) => STATUS_ORDER[b.status] - STATUS_ORDER[a.status])
    .slice(0, MAX_DRAWN_EDGES)
    .reverse();
  const dangling = edges.filter((e) => !placed.has(e.from) || !placed.has(e.to));
  const counts = edges.reduce<Record<string, number>>((m, e) => ((m[e.status] = (m[e.status] ?? 0) + 1), m), {});
  const nodeLabel = (id: string) => {
    const p = placed.get(id);
    return p ? displayInline(p.node.label, 60) : `${displayInline(id, 40)} (unknown node)`;
  };

  return (
    <div className="evidence">
      {missing.length > 0 ? (
        <p className="missing-alert" role="alert">
          {missing.length} MISSING evidence edge{missing.length === 1 ? '' : 's'}: the chain from NEAR
          semantics to the certified artifacts is incomplete at these points.
        </p>
      ) : (
        <p className="small ok">No missing edges reported.</p>
      )}
      <p className="small">
        {(['checked', 'trusted', 'tested', 'missing'] as EdgeStatus[]).map((s) => (
          <span key={s} className="sp">
            <EdgeStatusBadge status={s} /> {counts[s] ?? 0}
          </span>
        ))}
        {invalid > 0 && <span className="bad"> · {invalid} edge(s) with invalid status (treated as missing evidence)</span>}
      </p>
      <Legend />
      <div className="graph-scroll">
        <svg
          viewBox={`0 0 ${width} ${height}`}
          width={width}
          height={height}
          role="img"
          aria-labelledby="eg-title eg-desc"
          className="graph"
        >
          <title id="eg-title">Evidence graph</title>
          <desc id="eg-desc">
            {`${placed.size} nodes and ${edges.length} edges; ${missing.length} missing. The table below lists every edge.`}
          </desc>
          <defs>
            {(['checked', 'trusted', 'tested', 'missing'] as EdgeStatus[]).map((s) => (
              <marker key={s} id={`arrow-${s}`} viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
                <path d="M0,0 L10,5 L0,10 z" className={`arrowhead arrow-${s}`} />
              </marker>
            ))}
          </defs>
          {['sources & semantics', 'theorems & assumptions', 'artifacts & trusted base', 'tests & measurements'].map((t, i) => (
            <text key={t} x={PAD + i * (W + COL_GAP)} y={PAD + 4} className="col-head">
              {t}
            </text>
          ))}
          {drawable.map((e, i) => {
            const a = placed.get(e.from);
            const b = placed.get(e.to);
            if (!a || !b) return null;
            const { d, mx, my } = edgePath(a, b);
            return (
              <g key={i} className={`edge-g edge-g-${e.status}`}>
                <path d={d} className={`edge edge-${e.status}`} markerEnd={`url(#arrow-${e.status})`}>
                  <title>{`${e.status.toUpperCase()} ${displayInline(e.kind, 40)}: ${nodeLabel(e.from)} → ${nodeLabel(e.to)}`}</title>
                </path>
                {e.status === 'missing' && (
                  <text x={mx} y={my - 4} className="edge-label-missing" textAnchor="middle">
                    MISSING
                  </text>
                )}
              </g>
            );
          })}
          {[...placed.values()].map(({ node, x, y }) => (
            <g key={node.id} className={`node node-${node.kind}`}>
              <rect x={x} y={y} width={W} height={H} rx={6} />
              <text x={x + 8} y={y + 18} className="node-kind">
                {KIND_LABEL[node.kind] ?? 'unknown kind'}
              </text>
              <text x={x + 8} y={y + 36} className="node-label">
                {displayInline(node.label, 26)}
              </text>
              <title>{displayInline(node.label, 200)}</title>
            </g>
          ))}
        </svg>
      </div>
      {graph.nodes.length > MAX_NODES && (
        <p className="note">{graph.nodes.length - MAX_NODES} nodes beyond the display limit are not drawn.</p>
      )}
      {dangling.length > 0 && (
        <p className="bad small">
          {dangling.length} edge(s) reference unknown nodes and cannot be drawn; they are listed below.
        </p>
      )}
      <EdgeTable edges={edges} nodeLabel={nodeLabel} />
    </div>
  );
}

function EdgeTable({ edges, nodeLabel }: { edges: EvidenceEdge[]; nodeLabel: (id: string) => string }) {
  const sorted = [...edges].sort((a, b) => STATUS_ORDER[b.status] - STATUS_ORDER[a.status]);
  return (
    <details className="edge-details" open={edges.some((e) => e.status === 'missing')}>
      <summary>All {edges.length} evidence edges (missing first)</summary>
      <div className="table-wrap">
        <table className="data">
          <thead>
            <tr>
              <th scope="col">Status</th>
              <th scope="col">From</th>
              <th scope="col">Relation</th>
              <th scope="col">To</th>
              <th scope="col">Evidence</th>
              <th scope="col">Note</th>
            </tr>
          </thead>
          <tbody>
            {sorted.map((e, i) => (
              <tr key={i} className={e.status === 'missing' ? 'row-missing' : undefined}>
                <td>
                  <EdgeStatusBadge status={e.status} />
                </td>
                <td>{nodeLabel(e.from)}</td>
                <td>
                  <code><T v={e.kind} max={40} /></code>
                </td>
                <td>{nodeLabel(e.to)}</td>
                <td className="small">
                  {e.evidence.length === 0
                    ? '—'
                    : e.evidence.slice(0, 4).map((d, j) => (
                        <div key={j}>
                          <DigestText d={d} />
                        </div>
                      ))}
                </td>
                <td className="small">
                  <T v={e.note} max={300} />
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </details>
  );
}
