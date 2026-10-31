#!/usr/bin/env python3
"""Deliberate-breakage controls for the cold native W13 adapter (`w13_cold.rs`).

For each case the honest pair must be accepted with verified facts. Then:

* `no_code`: witness.bin without its contract code. Only for cases that carry code. A cold
  validator has nothing to execute, so it must reject. A warm one would still accept (the
  compiled cache has the contract): this is the control that the adapter really is cold.
* `claim_epoch`: one byte of the claim's `epoch_id` (T1) flipped. Facts must not verify.
* `claim_tail`: the claim's last byte flipped (`genesis_chunk_extra` tag, T14). Facts must not verify.
* `post_root`: the witness's main-transition `post_state_root` zeroed. Native must reject.

  python3 cold_controls.py --native-command-file CMD.json --cases DIR [--limit N] --out OUT --jobs 8
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import shutil
import struct
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import blind_inputs  # noqa: E402


def envelope(wb):
    off, parts = 0, []
    for _ in range(2):
        (n,) = struct.unpack_from('<I', wb, off)
        parts.append(wb[off + 4:off + 4 + n])
        off += 4 + n
    (count,) = struct.unpack_from('<I', wb, off)
    return parts[0], parts[1], count


def pack(tag, sw, codes_count=0):
    return struct.pack('<I', len(tag)) + tag + struct.pack('<I', len(sw)) + sw + struct.pack('<I', codes_count)


def epoch_offset(cb):
    off = 0
    for _ in range(2):                    # format_id, statement_id
        (n,) = struct.unpack_from('<I', cb, off)
        off += 4 + n
    off += 4                              # protocol_version
    (n,) = struct.unpack_from('<I', cb, off)
    return off + 4 + n                    # after chain_id


def mutants(case):
    cb, wb = (case / 'claim.bin').read_bytes(), (case / 'witness.bin').read_bytes()
    tag, sw, count = envelope(wb)
    out = {}
    if count:
        out['no_code'] = (cb, pack(tag, sw))
    e = epoch_offset(cb)
    out['claim_epoch'] = (cb[:e] + bytes([cb[e] ^ 1]) + cb[e + 1:], wb)
    out['claim_tail'] = (cb[:-1] + bytes([cb[-1] ^ 1]), wb)
    a, z = blind_inputs.post_root_spans(sw)[0]
    rest = wb[4 + len(tag) + 4 + len(sw):]
    swz = sw[:a] + bytes(32) + sw[z:]
    out['post_root'] = (cb, struct.pack('<I', len(tag)) + tag + struct.pack('<I', len(swz)) + swz + rest)
    return out


def adapter(cmd, case, timeout):
    try:
        r = subprocess.run([*cmd, str(case)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {'adapter_exit': 'timeout', 'stderr_tail': ''}
    lines = r.stdout.strip().splitlines()
    if r.returncode != 0 or len(lines) != 1:
        return {'adapter_exit': r.returncode, 'stderr_tail': r.stderr[-400:]}
    return json.loads(lines[0])


def outcome(row):
    if 'adapter_exit' in row or row.get('adapter_error'):
        return 'error'
    if not row.get('facts_verified'):
        return 'facts_rejected'
    return row['verdict']


EXPECT = {'honest': {'accept'}, 'no_code': {'reject'}, 'claim_epoch': {'facts_rejected', 'error'},
          'claim_tail': {'facts_rejected', 'error'}, 'post_root': {'reject'}}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--native-command-file', type=Path, required=True)
    ap.add_argument('--cases', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--limit', type=int)
    ap.add_argument('--stride', type=int, default=1, help='sample: code-carrying cases + every Nth case')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--timeout', type=float, default=600)
    a = ap.parse_args()
    cmd = json.loads(a.native_command_file.read_text())
    a.out.mkdir(parents=True, exist_ok=False)
    cases = sorted(p for p in a.cases.iterdir() if (p / 'claim.bin').is_file())
    if a.stride > 1:
        # every case that carries code (the cold control needs it), plus every stride-th case
        cases = [c for i, c in enumerate(cases) if i % a.stride == 0 or envelope(
            (c / 'witness.bin').read_bytes())[2]]
    cases = cases[:a.limit]

    def run(case):
        rows = [dict(case=case.name, control='honest', **{'outcome': outcome(adapter(cmd, case, a.timeout))})]
        for name, (cb, wb) in mutants(case).items():
            d = a.out / 'mutants' / f'{case.name}-{name}'
            d.mkdir(parents=True)
            (d / 'claim.bin').write_bytes(cb)
            (d / 'witness.bin').write_bytes(wb)
            try:
                res = adapter(cmd, d, a.timeout)
            finally:
                shutil.rmtree(d)
            rows.append(dict(case=case.name, control=name, outcome=outcome(res),
                             native_error=(res.get('native_error') or '')[:300]))
        for r in rows:
            r['as_expected'] = r['outcome'] in EXPECT[r['control']]
        return rows

    with ThreadPoolExecutor(a.jobs) as pool:
        rows = [r for rs in pool.map(run, cases) for r in rs]
    table = {}
    for r in rows:
        table.setdefault(r['control'], Counter())[r['outcome']] += 1
    report = dict(cases=len(cases), adapter=cmd, table={k: dict(v) for k, v in table.items()},
                  unexpected=[r for r in rows if not r['as_expected']],
                  expected=dict((k, sorted(v)) for k, v in EXPECT.items()))
    (a.out / 'rows.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in rows))
    (a.out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('cases', 'table')} | {'unexpected': len(report['unexpected'])}, indent=2))
    return 0 if not report['unexpected'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
