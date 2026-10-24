#!/usr/bin/env python3
"""Measure SHA message geometry; capacities are research estimates, not proofs."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess


def pow2(n):
    return 1 << (n-1).bit_length() if n else 0


def capacity_policy(rows):
    policies = {}
    for family in ['sha_t', 'sha_r']:
        maxima = Counter()
        for row in rows:
            if row['export_returncode']:
                continue
            buckets = Counter()
            for blocks, count in row['families'][family]['block_histogram'].items():
                buckets[pow2(int(blocks))] += count
            for blocks, count in buckets.items():
                maxima[blocks] = max(maxima[blocks], count)
        slots = {blocks: pow2(count) for blocks, count in sorted(maxima.items())}
        policies[family] = {'block_capacity_to_message_slots': slots,
            'total_message_slots': sum(slots.values()),
            'total_compression_slots': sum(k*v for k,v in slots.items()),
            'selection': 'Corpus-derived candidate; freeze before independent held-out evaluation.'}
    return policies


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--fixtures', type=Path, required=True)
    p.add_argument('--exporter', type=Path, required=True)
    p.add_argument('--scratch', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    rows = []
    for claim in sorted(a.fixtures.glob('*/claim.bin')):
        case = claim.parent
        out = a.scratch/case.name
        out.mkdir(parents=True, exist_ok=True)
        run = subprocess.run([str(a.exporter), str(case), str(out)], capture_output=True, text=True, timeout=60)
        (out/'export.log').write_text(run.stdout+run.stderr)
        row = {'case': case.name, 'claim_sha256': hashlib.sha256(claim.read_bytes()).hexdigest(),
               'witness_sha256': hashlib.sha256((case/'witness.bin').read_bytes()).hexdigest(),
               'export_returncode': run.returncode}
        if run.returncode == 0:
            families = {}
            for family in ['sha_t', 'sha_r']:
                messages = json.loads((out/f'{family}.json').read_text())
                histogram = Counter((len(m['bytes'])+72)//64 for m in messages)
                count = len(messages)
                blocks = sum(k*v for k,v in histogram.items())
                families[family] = {'messages': count, 'blocks': blocks,
                    'length_classes': len({len(m['bytes']) for m in messages}),
                    'block_histogram': dict(sorted(histogram.items())),
                    'max_blocks_per_message': max(histogram, default=0),
                    'uniform_message_capacity_blocks': count*max(histogram, default=0),
                    'pow2_count_per_exact_block_class': sum(k*pow2(v) for k,v in histogram.items()),
                    'pow2_block_stream_capacity': pow2(blocks)}
            row['families'] = families
        rows.append(row)
        print(case.name, run.returncode, flush=True)
    report = {'status': 'GEOMETRY_ONLY', 'cases': rows,
        'candidate_reusable_policy': capacity_policy(rows),
        'exporter_sha256': hashlib.sha256(a.exporter.read_bytes()).hexdigest(),
        'limitations': ['D0a corpus only; not full NEAR coverage.',
            'Capacity figures exclude mask, padding, chaining and bus proof overhead.',
            'Per-case buckets are not yet a fixed public capacity policy.',
            'No proving latency, proof size or security claim.']}
    a.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
