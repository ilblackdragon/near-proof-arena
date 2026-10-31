#!/bin/bash
set -eu
W=/data/illia/nearproof/.claude/worktrees/agent-a8b3a000da794c665
B=/data/illia/nearproof-deps/l0-validate/b4
cd $W
R=docs/evidence/lean-chunk-completion/l0-row-validation
python3 tools/d3/l0_exercise.py evidence --map $B/map-float-x.json $B/map-r2-x.json \
  --ablate $B/ablate-float.json $B/ablate-r2.json $B/ablate-r2g.json --out $R/rows.json \
  --extra $B/extra3.json \
  --only L0-instr-float L0-W-012 L0-W-005 L0-W-006 L0-D2-020 L0-D2-023 L0-D2-025
python3 tools/d3/l0_exercise.py statuses --spec $R/third-pass-statuses.json --out $R/rows.json
python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore /data/illia/nearproof-deps/nearcore --output docs/research/lean-chunk-coverage.json
python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore /data/illia/nearproof-deps/nearcore --check docs/research/lean-chunk-coverage.json
python3 - <<'EOF'
import json, collections
d = json.load(open('docs/research/lean-chunk-coverage.json'))
print(collections.Counter(r['status'] for r in d['rows']))
ids = ["L0-D2-012", "L0-D2-019", "L0-same-layout", "L0-split-gate", "L0-guard-noResharding", "L0-D2-020", "L0-D2-023",
       "L0-D2-025", "L0-instr-float", "L0-W-012", "L0-W-005", "L0-W-006", "L0-D3-003", "L0-D3-013", "L0-D3-014",
       "L0-W-011", "L0-W-013", "L0-W-014", "L0-host-current_contract_code"]
for r in d['rows']:
    if r['id'] in ids:
        print(r['id'], r['status'], '|', r['remaining_work'][:100])
EOF
