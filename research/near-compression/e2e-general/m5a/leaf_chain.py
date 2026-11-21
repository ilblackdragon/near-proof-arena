#!/usr/bin/env python3
"""B-T1: check the chain of a split case's template proofs (`leaf.sh`).

  leaf_chain.py OUT_DIR ORACLE_POST_ROOT

For each dump (`if`, `seg0`, `seg1`, …) the statement is read from the proof (`out/statement.json`,
written by the prover after native verification and the statement check) when present, else from
the trace generator's `stats.json`.  Public values (`Tmpl.lean`): 0–15 `prev_state_root` (16-bit
limbs), 16 `wsLen`, 17–34 / 35–52 the working-set roots A / B at depth 24 (18 limbs of 21 bits:
SHA-384 words), 53–68 `post_state_root`, 69 the change count.  Checks: every AIR of a proof that
reads public value i holds the same value (one statement per proof); IF's R_0 = seg0's R_in,
seg_k's R_out = seg_{k+1}'s R_in, the last segment's R_out = IF's R_n; `wsLen` equal across the
proofs; IF's post-state root = the Lean oracle's.
"""
import json
import os
import sys


def root16(v):
    return bytes(b for x in v for b in (x >> 8, x & 255)).hex()


def root21(v):
    out = b''
    for i in range(6):
        w = v[3 * i] + (v[3 * i + 1] << 21) + (v[3 * i + 2] << 42)
        out += w.to_bytes(8, 'big')
    return out.hex()


def statement(d):
    p = os.path.join(d, 'out', 'statement.json')
    if not os.path.exists(p):
        return None, None
    st = json.load(open(p))
    full = st['statement']
    for a in st['airs']:
        pv = a['public_values']
        assert pv == full[:len(pv)], '%s: AIR %s public values differ from the statement' % (d, a['name'])
    return full, st


def main():
    out, oracle = sys.argv[1], sys.argv[2]
    names = ['if'] + sorted((n for n in os.listdir(out) if n.startswith('seg') and n[3:].isdigit()),
                            key=lambda n: int(n[3:]))
    rec = {}
    for n in names:
        d = os.path.join(out, n)
        full, st = statement(d)
        src = 'proof'
        if full is None:
            full = None
            src = 'trace'
            s = json.load(open(os.path.join(d, 'stats.json')))
            rec[n] = dict(src=src, a=s['root_a'], b=s['root_b'], wslen=s['ws_len'], prev=s['pre_root'],
                          post=s['post_root'] if n == 'if' else None)
            continue
        r = dict(src=src, prev=root16(full[0:16]), wslen=full[16], a=root21(full[17:35]), b=root21(full[35:53]),
                 proof_bytes=st['proof_bytes'], vk_sha256=st['vk_sha256'])
        if n == 'if':
            r['post'] = root16(full[53:69])
            r['changes'] = full[69]
        rec[n] = r
    ok = True
    segs = names[1:]
    chain = [('if.R_0', rec['if']['a'], segs[0] + '.R_in', rec[segs[0]]['a'])]
    for x, y in zip(segs, segs[1:]):
        chain.append((x + '.R_out', rec[x]['b'], y + '.R_in', rec[y]['a']))
    chain.append((segs[-1] + '.R_out', rec[segs[-1]]['b'], 'if.R_n', rec['if']['b']))
    for a, va, b, vb in chain:
        good = va == vb
        ok &= good
        print('CHAIN %s = %s: %s (%s…)' % (a, b, 'OK' if good else 'MISMATCH', va[:16]))
    wl = set(r['wslen'] for r in rec.values())
    ok &= len(wl) == 1
    print('WSLEN %s: %s' % (sorted(wl), 'OK' if len(wl) == 1 else 'MISMATCH'))
    good = rec['if']['post'] == oracle
    ok &= good
    print('POST %s = oracle %s: %s' % (rec['if']['post'], oracle, 'OK' if good else 'MISMATCH'))
    for n in names:
        r = rec[n]
        print('PROOF %-5s from %s%s' % (n, r['src'], '' if r['src'] == 'trace' else
                                         ': %d B, vk sha256 %s' % (r['proof_bytes'], r['vk_sha256'][:16])))
    print('LEAF CHAIN', 'OK' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
