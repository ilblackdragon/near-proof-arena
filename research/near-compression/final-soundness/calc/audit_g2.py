#!/usr/bin/env python3
"""Audit the recorded G2 artifact and exact query arithmetic; NOT a soundness proof.

No floating-point decision is used for the query-error target. Certificate
coverage means a pinned, non-excluded input exists, not that WHIR's use of the
certificate has been proved. --require-security fails until that proof exists.
"""
import argparse
import ast
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
GATE = ROOT / 'results/pq-stream-commit/g2-gate'
FORMAL = ROOT / 'final-soundness'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(gate=GATE, formal=FORMAL):
    manifest = json.loads((gate / 'MANIFEST.json').read_text())
    log = (gate / 'run.log').read_text()
    failures = []
    def check(condition, label):
        if not condition:
            failures.append(label)
    for name, expected in manifest['proofs_sha256'].items():
        check(digest(gate / name) == expected, f'proof digest: {name}')
        check((gate / name).stat().st_size == manifest['proof_bytes'][name.removesuffix('.proof')],
              f'proof length: {name}')
    for marker in manifest['required_log_lines']:
        check(marker in log, f'log marker: {marker}')
    for name, expected in manifest['certificate_files_sha256'].items():
        check(digest(formal / name) == expected, f'certificate file digest: {name}')
    certs = json.loads((formal / 'calc/dkt_certs_o2.json').read_text())
    excluded = set((formal / 'lean/DKTCertsO2_big.keys').read_text().splitlines())
    p = 15 * 2**27 + 1
    target = manifest['parameters']['query_bits']
    pow_bits = manifest['parameters']['query_pow_bits']
    reports = {}
    for role, prefix in [('parent', 'NV_PARENT_O2'), ('final', 'NV_FINAL_O2')]:
        matches = re.findall(r'^' + prefix + r' .*rounds\(n,k,A,q,first_order\)=(.*)$', log, re.M)
        if len(matches) != 1:
            raise ValueError(f'expected exactly one {prefix} record')
        rounds = ast.literal_eval(matches[0].replace('true', 'True').replace('false', 'False'))
        params = manifest['parameters'][role]
        check([r[3] for r in rounds] == params['queries'], f'{role}: manifest query counts')
        details = []
        for i, (n, k, a, q, first_order) in enumerate(rounds):
            fold = params['k1'] if i == 0 else params['k']
            check(0 < a <= n and k > 1 and q > 0, f'{role}/{i}: parameter range')
            check(n == 15 * k * 2**params['log_blowup'] if i == 0 else n == rounds[0][0],
                  f'{role}/{i}: keep-domain shape')
            if i + 1 < len(rounds):
                check(k == rounds[i + 1][1] * 2**fold, f'{role}/{i}: fold dimension')
            else:
                check(k == 2**(params['log_final'] + fold), f'{role}/{i}: final dimension')
            # Exact sufficient inequality for the query component, conditional
            # on the agreement/list model and correct independent sampling.
            query_ok = a**q * 2**target <= n**q
            check(query_ok, f'{role}/{i}: exact query target')
            check(a**(q-1) * 2**target > n**(q-1), f'{role}/{i}: minimal query count')
            subcodes = []
            for s in range(fold + 1):
                check(n % 2**s == 0 and k % 2**s == 0, f'{role}/{i}/{s}: divisibility')
                ns, ks = n // 2**s, k // 2**s
                threshold = (a * ns + n - 1) // n
                key = f'{ns},{ks},{threshold},1'
                if first_order:
                    present = key in certs and key not in excluded
                    check(present, f'{role}/{i}/{s}: non-excluded certificate {key}')
                    if present:
                        c = certs[key]
                        check(p > c['char_gt'], f'{role}/{i}/{s}: characteristic')
                        check(Fraction(c['E']) >= 0 and Fraction(c['list']) >= 1,
                              f'{role}/{i}/{s}: certificate values')
                    subcodes.append({'key': key, 'certificate_present': present})
                else:
                    johnson = ns * (ks - 1) < threshold**2
                    check(johnson, f'{role}/{i}/{s}: strict Johnson guard')
                    subcodes.append({'key': key, 'johnson_guard': johnson})
            with localcontext() as ctx:
                ctx.prec = 70
                bits = Decimal(pow_bits) + Decimal(q) * (Decimal(n) / Decimal(a)).ln() / Decimal(2).ln()
            details.append({'n': n, 'dimension': k, 'agreement': a, 'queries': q,
                            'fold': fold, 'first_order': first_order,
                            'query_component_bits_with_grinding': str(bits),
                            'exact_query_target_pass': query_ok, 'subcodes': subcodes})
        reports[role] = details
    # Validate the supplemental replay record when present. This checks saved
    # evidence, not a new execution of the prover or a security theorem.
    replay_path = gate / 'REPLAY-2026-10-21.json'
    replay_checked = None
    if replay_path.exists():
        before = len(failures)
        replay = json.loads(replay_path.read_text())
        replay_log = gate / replay['replay_log']
        replay_text = replay_log.read_text()
        check(replay['original_manifest_sha256'] == digest(gate / 'MANIFEST.json'),
              'replay: original manifest digest')
        check(digest(replay_log) == replay['replay_log_sha256'], 'replay: log digest')
        check(set(replay['proofs']) == set(manifest['proofs_sha256']), 'replay: proof set')
        for name, expected in manifest['proofs_sha256'].items():
            item = replay['proofs'].get(name, {})
            check(item.get('sha256') == expected, f'replay: proof digest {name}')
            check(item.get('bytes') == manifest['proof_bytes'][name.removesuffix('.proof')],
                  f'replay: proof length {name}')
            check(expected in replay_text, f'replay: logged proof digest {name}')
        for marker in manifest['required_log_lines']:
            check(marker in replay_text, f'replay: log marker {marker}')
        check(replay['binary_sha256'] in replay_text, 'replay: logged binary digest')
        replay_checked = len(failures) == before
    return {
        'independent_replay_record_checks_pass': replay_checked,
        'artifact_manifest_sha256': digest(gate / 'MANIFEST.json'),
        'run_log_sha256': digest(gate / 'run.log'),
        'artifact_checks_pass': not failures, 'failures': failures,
        'final_proof_bytes': (gate / 'FINAL.proof').stat().st_size,
        'rounds': reports,
        'security_established': False,
        'open_obligations': [
            'Actual family QROM potential, transition constants, extraction and replacement',
            'DKT-to-actual-WHIR list-regime transfer including batching and all per-move errors',
            'NV accepted-trace-to-execution theorem for the pinned program generator',
            'Coherent recursive hash model and quantified computational reduction',
            'Complete bound for the measured VK and every layer, including base relation',
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-security', action='store_true')
    args = parser.parse_args()
    report = audit()
    print(json.dumps(report, indent=2))
    if not report['artifact_checks_pass']:
        return 1
    return 2 if args.require_security and not report['security_established'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
