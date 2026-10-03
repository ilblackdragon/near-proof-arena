/**
 * Vite dev-server middleware serving DEMO fixtures (ARENA_MOCK=1 only).
 * The pending fixture submission advances one stage per SSE tick so the live
 * progress UI can be exercised.
 */
import type { IncomingMessage, ServerResponse } from 'node:http';
import { STAGES } from '../src/api/types';
import { demoDataset, gates } from './fixtures';
import { MOCK_HEADER, route } from './api';

type Next = (err?: unknown) => void;

export function createMockMiddleware() {
  const ds = demoDataset();
  return (req: IncomingMessage, res: ServerResponse, next: Next) => {
    const url = req.url ?? '/';
    const r = route(ds, req.method ?? 'GET', url);
    if (r === null) return next();
    if (r === 'sse') {
      const id = decodeURIComponent(url.split('/')[3] ?? '');
      const sub = ds.submissions.find((s) => s.id === id);
      if (!sub) {
        res.statusCode = 404;
        return res.end();
      }
      res.writeHead(200, {
        'content-type': 'text/event-stream',
        'cache-control': 'no-store',
        connection: 'keep-alive',
        [MOCK_HEADER]: 'demo-fixtures',
      });
      res.write(`event: status\ndata: ${JSON.stringify({ stage: sub.stage, demo_fixture: true })}\n\n`);
      const timer = setInterval(() => {
        if (sub.decision != null) {
          res.write(`event: done\ndata: ${JSON.stringify({ decision: sub.decision })}\n\n`);
          clearInterval(timer);
          return res.end();
        }
        const i = STAGES.indexOf(sub.stage);
        sub.stage = STAGES[Math.min(i + 1, STAGES.length - 1)];
        sub.updated_at = new Date().toISOString();
        if (sub.stage === 'FORMAL_CHECKED') {
          sub.gates = gates({ PKG_WELLFORMED: 'PASS', BUILD_REPRODUCIBLE: 'PASS', ARTIFACT_BINDING: 'PASS', AXIOM_AUDIT: 'PASS' });
        }
        if (sub.stage === 'DECIDED') {
          sub.gates = gates({ PKG_WELLFORMED: 'PASS', BUILD_REPRODUCIBLE: 'PASS', ARTIFACT_BINDING: 'PASS', AXIOM_AUDIT: 'PASS', FORMAL_IMPL_CONNECTION: 'UNKNOWN' });
          sub.decision = 'INCONCLUSIVE';
          sub.accepted = false;
          sub.reason_codes = ['OBLIGATION_UNDISCHARGED'];
        }
        res.write(`event: stage\ndata: ${JSON.stringify({ stage: sub.stage })}\n\n`);
      }, 1500);
      req.on('close', () => clearInterval(timer));
      return;
    }
    res.statusCode = r.status;
    res.setHeader('content-type', 'application/json');
    res.setHeader(MOCK_HEADER, 'demo-fixtures');
    res.end(JSON.stringify(r.body));
  };
}
