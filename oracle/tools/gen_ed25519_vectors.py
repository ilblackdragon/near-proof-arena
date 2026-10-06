#!/usr/bin/env python3
"""Build the Ed25519 / SHA-512 vector set in oracle/fixtures/v3/ed25519/.

  gen_ed25519_vectors.py inputs UPSTREAM_DIR STAGE_DIR
      Convert the fetched upstream files (see SOURCES.json) and generate the edge-case
      and SHA-512 vectors; writes STAGE_DIR/<name>.in.jsonl (id, pk, sig, msg + metadata).
  gen_ed25519_vectors.py merge STAGE_DIR OUT_DIR
      Merge nearcore's verdicts (STAGE_DIR/<name>.judged.jsonl, produced by
      `near-arena-oracle-v3-d1 ed25519-judge`) into OUT_DIR/<name>.jsonl.
  gen_ed25519_vectors.py crosscheck DIR
      Compare libsodium (PyNaCl) and OpenSSL (cryptography) against nearcore's verdicts
      and print the disagreement classes (they are NOT the reference).

Every verdict in the fixture files comes from nearcore (`verify_raw`, `sig_decodes`,
`verify`); upstream "result" fields are kept alongside as `upstream_*`.
"""
import hashlib
import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v3lib import ed25519 as E  # noqa: E402  (point helpers for crafting only)

P, L = E.P, E.L


def hx(b):
    return bytes(b).hex()


def line(id_, pk, sig, msg, **meta):
    d = {'id': id_, 'pk': hx(pk), 'sig': hx(sig), 'msg': hx(msg)}
    d.update(meta)
    return d


def enc_int(n):
    return n.to_bytes(32, 'little')


# ---------------------------------------------------------------- upstream converters

def rfc8032(path):
    txt = open(path, encoding='latin-1').read()
    sec = txt[txt.index('7.1.  Test Vectors for Ed25519\n', 3000):
              txt.index('7.2.  Test Vectors for Ed25519ctx\n', 3000)]
    out = []
    for name, body in re.findall(r'-----TEST ([^\n]+)\n(.*?)(?=-----TEST |\Z)', sec, re.S):
        fields, cur = {}, None
        for ln in body.split('\n'):
            s = ln.strip()
            m = re.match(r'(SECRET KEY|PUBLIC KEY|MESSAGE|SIGNATURE)', s)
            if m:
                cur = m.group(1)
                fields[cur] = ''
            elif cur and re.fullmatch(r'[0-9a-f]+', s):
                fields[cur] += s
        pk, msg, sig = (bytes.fromhex(fields[k]) for k in ('PUBLIC KEY', 'MESSAGE', 'SIGNATURE'))
        out.append(line(f'rfc8032-{name}', pk, sig, msg, upstream_result='valid'))
        # mutated: last message byte / first sig byte flipped
        m2 = (msg[:-1] + bytes([msg[-1] ^ 1])) if msg else b'\x00'
        out.append(line(f'rfc8032-{name}-msgmut', pk, sig, m2, upstream_result='mutated'))
    assert len(out) == 10, len(out)
    return out


def djb_sign_input(path):
    out = []
    for i, ln in enumerate(open(path)):
        f = ln.rstrip('\n').split(':')
        pk = bytes.fromhex(f[1])
        msg = bytes.fromhex(f[2])
        sm = bytes.fromhex(f[3])
        assert sm[64:] == msg
        out.append(line(f'djb-{i}', pk, sm[:64], msg, upstream_result='valid'))
    assert len(out) == 1024
    return out


def wycheproof(path):
    j = json.load(open(path))
    out, skipped = [], []
    for g in j['testGroups']:
        pk = bytes.fromhex(g['publicKey']['pk'])
        for t in g['tests']:
            sig, msg = bytes.fromhex(t['sig']), bytes.fromhex(t['msg'])
            meta = dict(upstream_result=t['result'], flags=t['flags'], comment=t['comment'])
            if len(sig) != 64 or len(pk) != 32:
                skipped.append({'tcId': t['tcId'], 'sig_len': len(sig), 'result': t['result'],
                                'comment': t['comment']})
                continue
            out.append(line(f"wycheproof-{t['tcId']}", pk, sig, msg, **meta))
    return out, skipped


def cctv(path):
    out = []
    for t in json.load(open(path)):
        out.append(line(f"cctv-{t['number']}", bytes.fromhex(t['key']), bytes.fromhex(t['sig']),
                        t['msg'].encode(), flags=t.get('flags') or []))
    return out


def speccheck(path):
    out = []
    for i, t in enumerate(json.load(open(path))):
        out.append(line(f'speccheck-{i}', bytes.fromhex(t['pub_key']),
                        bytes.fromhex(t['signature']), bytes.fromhex(t['message'])))
    return out


# ---------------------------------------------------------------- own edge cases

def torsion():
    """The 8 points of E[8] as affine pairs, T[i] = [i]T8."""
    rnd = random.Random(8)
    while True:
        y = rnd.randrange(P)
        A = E._decompress(enc_int(y))
        if A is None:
            continue
        t = E._mul(L, A)
        if E._mul(4, t) != E.IDENT:  # order exactly 8
            T = [E.IDENT]
            for _ in range(7):
                T.append(E._add(T[-1], t))
            assert E._add(T[-1], t) == E.IDENT
            assert len(set(T)) == 8
            return T


def edge(rnd):
    out = []
    T = torsion()
    B = E.BASE
    cmp_ = E._compress

    def keypair():
        a = rnd.randrange(1, L)
        return a, E._mul(a, B)

    def craft(a, Tc, Ab, msg, rnd_r=None):
        """(R, s) valid under cofactorless verification for A = [a]B + Tc encoded as Ab."""
        for _ in range(1000):
            r = rnd_r if rnd_r is not None else rnd.randrange(L)
            for t in T:
                R = E._add(E._mul(r, B), t)
                Rb = cmp_(R)
                k = int.from_bytes(hashlib.sha512(Rb + Ab + msg).digest(), 'little') % L
                if E._neg(E._mul(k, Tc)) == t:
                    return Rb + enc_int((r + k * a) % L)
        raise RuntimeError('craft failed')

    # -- small-order points, all their encodings
    for i, t in enumerate(T):
        cb = cmp_(t)
        encs = [('canon', cb), ('signflip', cb[:31] + bytes([cb[31] ^ 0x80]))]
        y = t[1]
        if y + P < 2**255:
            nb = enc_int(y + P)
            encs += [('noncanon', nb), ('noncanon-signflip', nb[:31] + bytes([nb[31] | 0x80]))]
        for en, Ab in encs:
            Dt = E._decompress(Ab)
            for m in range(3):
                msg = bytes([i, m]) * m
                if Dt is None:
                    out.append(line(f'edge-loA-{i}-{en}-{m}-nodecode', Ab, rnd.randbytes(64), msg,
                                    cls='low_order_A_nodecode'))
                    continue
                # small-order A, crafted valid sig (accept side)
                sig = craft(0, Dt, Ab, msg)
                out.append(line(f'edge-loA-{i}-{en}-{m}', Ab, sig, msg, cls='low_order_A_valid'))
                # same but wrong msg -> reject (unless [k]A happens to coincide)
                out.append(line(f'edge-loA-{i}-{en}-{m}-wrongmsg', Ab, sig, msg + b'!',
                                cls='low_order_A_wrongmsg'))
            # small-order R encoding with honest key: R' = [s]B - [k]A; craft s for R = t
            a, A = keypair()
            Abh = cmp_(A)
            msg = b'R small order ' + bytes([i])
            k = int.from_bytes(hashlib.sha512(Ab + Abh + msg).digest(), 'little') % L
            # want [s]B - [k]A == t: only possible for t = identity (s = k a)
            s = (k * a) % L
            out.append(line(f'edge-loR-{i}-{en}', Abh, Ab + enc_int(s), msg,
                            cls='low_order_R_' + ('identity_' if i == 0 else '') + en))
        # both A and R small order, s = 0
        for en, Ab in encs:
            out.append(line(f'edge-loAR-{i}-{en}', Ab, cmp_(E.IDENT) + bytes(32), b'',
                            cls='low_order_A_R_s0'))
            out.append(line(f'edge-loAR2-{i}-{en}', Ab, Ab + bytes(32), b'',
                            cls='low_order_A_R_s0'))

    # -- all non-canonical y encodings y + p for y in 0..18, both sign bits, with
    #    random / crafted signatures
    for y in range(19):
        for sb in (0, 1):
            Ab = enc_int(y + P + (sb << 255))
            A = E._decompress(Ab)
            out.append(line(f'edge-ncA-y{y}-s{sb}-rand', Ab, rnd.randbytes(32) + enc_int(rnd.randrange(L)),
                            b'nc', cls='noncanonical_A_' + ('decodes' if A else 'nodecode')))
            if A is not None and E._mul(8, A) == E.IDENT:
                out.append(line(f'edge-ncA-y{y}-s{sb}-valid', Ab, craft(0, A, Ab, b'nc'), b'nc',
                                cls='noncanonical_A_valid'))
            if A is not None:
                # same point, canonical encoding (x = 0 sign variants included)
                cb = cmp_(A)
                out.append(line(f'edge-ncA-y{y}-s{sb}-canon-rand', cb,
                                rnd.randbytes(32) + enc_int(rnd.randrange(L)), b'nc',
                                cls='canonical_of_noncanonical'))

    # -- x = 0 with sign bit set: y = 1 (identity) and y = p-1 (order 2)
    for nm, y in (('ident', 1), ('order2', P - 1)):
        Ab = enc_int(y + (1 << 255))
        tp = (0, y)
        for m in range(4):
            msg = bytes([m]) * m
            out.append(line(f'edge-x0sign-{nm}-{m}', Ab, craft(0, tp, Ab, msg), msg,
                            cls='x0_signbit_A_valid'))
        # R = identity / order-2 with sign bit (non-canonical R) -> must reject
        a, A = keypair()
        Abh = cmp_(A)
        Rb = Ab
        k = int.from_bytes(hashlib.sha512(Rb + Abh + b'').digest(), 'little') % L
        out.append(line(f'edge-x0sign-R-{nm}', Abh, Rb + enc_int((k * a) % L), b'',
                        cls='x0_signbit_R_reject'))

    # -- mixed-order A = [a]B + T[i] (accept side, crafted) and honest-style sig (reject 7/8)
    for i in range(1, 8):
        for rep in range(4):
            a, A0 = keypair()
            A = E._add(A0, T[i])
            Ab = cmp_(A)
            msg = rnd.randbytes(rep * 10)
            out.append(line(f'edge-mixA-{i}-{rep}', Ab, craft(a, T[i], Ab, msg), msg,
                            cls='mixed_order_A_valid'))
            prefix = rnd.randbytes(32)
            out.append(line(f'edge-mixA-{i}-{rep}-std', Ab, E.sign_with_scalar(a, prefix, Ab, msg),
                            msg, cls='mixed_order_A_stdsig'))

    # -- mixed-order R (R = [r]B + T[i]) with honest key: R' is always torsion-free, reject
    for i in range(1, 8):
        a, A = keypair()
        Ab = cmp_(A)
        r = rnd.randrange(L)
        Rb = cmp_(E._add(E._mul(r, B), T[i]))
        k = int.from_bytes(hashlib.sha512(Rb + Ab + b'm').digest(), 'little') % L
        out.append(line(f'edge-mixR-{i}', Ab, Rb + enc_int((r + k * a) % L), b'm',
                        cls='mixed_order_R'))

    # -- honest signatures and their scalar / encoding manipulations
    honest = []
    for h in range(40):
        a, A = keypair()
        Ab = cmp_(A)
        msg = rnd.randbytes(rnd.randrange(0, 200))
        sig = E.sign_with_scalar(a, rnd.randbytes(32), Ab, msg)
        honest.append((a, Ab, sig, msg))
        out.append(line(f'edge-honest-{h}', Ab, sig, msg, cls='honest'))
        s = int.from_bytes(sig[32:], 'little')
        Rb = sig[:32]
        for j, (nm, s2) in enumerate([('s+L', s + L), ('s+2L', s + 2 * L), ('s+8L', s + 8 * L),
                                      ('s+15L', s + 15 * L), ('s+kL-max', s + ((2**256 - 1 - s) // L) * L),
                                      ('s-bit253', s | (1 << 253)), ('s-bit254', s | (1 << 254)),
                                      ('s-bit255', s | (1 << 255)), ('L', L), ('L-1', L - 1),
                                      ('2^252', 2**252), ('2^253-1', 2**253 - 1),
                                      ('2^256-1', 2**256 - 1), ('s=0', 0)]):
            if s2 >= 2**256:
                continue
            out.append(line(f'edge-honest-{h}-{nm}', Ab, Rb + s2.to_bytes(32, 'little'), msg,
                            cls='scalar_' + nm))
        out.append(line(f'edge-honest-{h}-xflip', Ab[:31] + bytes([Ab[31] ^ 0x80]), sig, msg,
                        cls='pk_signflip'))
        out.append(line(f'edge-honest-{h}-Rflip', Ab, bytes(sig[:31]) + bytes([sig[31] ^ 0x80]) + sig[32:],
                        msg, cls='R_signflip'))
    # bit flips of two honest signatures
    for h in range(2):
        a, Ab, sig, msg = honest[h]
        if not msg:
            msg = b'x'
            sig = E.sign_with_scalar(a, b'p' * 32, Ab, msg)
        for bit in range(256):
            pk2 = bytearray(Ab)
            pk2[bit // 8] ^= 1 << (bit % 8)
            out.append(line(f'edge-flip{h}-pk-{bit}', pk2, sig, msg, cls='bitflip_pk'))
        for bit in range(512):
            s2 = bytearray(sig)
            s2[bit // 8] ^= 1 << (bit % 8)
            out.append(line(f'edge-flip{h}-sig-{bit}', Ab, s2, msg, cls='bitflip_sig'))
        for bit in range(min(64, 8 * len(msg))):
            m2 = bytearray(msg)
            m2[bit // 8] ^= 1 << (bit % 8)
            out.append(line(f'edge-flip{h}-msg-{bit}', Ab, sig, m2, cls='bitflip_msg'))

    # -- R = identity with honest key: s = k a (accept side), and non-canonical identity R
    for h in range(6):
        a, A = keypair()
        Ab = cmp_(A)
        msg = bytes([h]) * h
        for nm, Rb, c in (('canon', cmp_(E.IDENT), 'R_identity_valid'),
                          ('noncanon', enc_int(1 + P), 'R_identity_noncanon'),
                          ('signbit', enc_int(1 + (1 << 255)), 'R_identity_signbit')):
            k = int.from_bytes(hashlib.sha512(Rb + Ab + msg).digest(), 'little') % L
            out.append(line(f'edge-Rid-{h}-{nm}', Ab, Rb + enc_int((k * a) % L), msg, cls=c))

    # -- A = identity encodings with random signatures and with s s.t. R = [s]B
    for h in range(6):
        s = rnd.randrange(L)
        Rb = cmp_(E._mul(s, B))
        for nm, Ab in (('canon', cmp_(E.IDENT)), ('noncanon', enc_int(1 + P)),
                       ('signbit', enc_int(1 + (1 << 255))), ('noncanon-signbit', enc_int(1 + P + (1 << 255)))):
            out.append(line(f'edge-Aid-{h}-{nm}', Ab, Rb + enc_int(s), rnd.randbytes(h * 7),
                            cls='A_identity_valid'))
            out.append(line(f'edge-Aid-{h}-{nm}-rand', Ab, rnd.randbytes(32) + enc_int(rnd.randrange(L)),
                            b'', cls='A_identity_randsig'))

    # -- R with non-canonical y (y + p for y < 19) and honest key: never matches
    for y in range(19):
        a, A = keypair()
        Ab = cmp_(A)
        Rb = enc_int(y + P)
        k = int.from_bytes(hashlib.sha512(Rb + Ab).digest(), 'little') % L
        out.append(line(f'edge-ncR-{y}', Ab, Rb + enc_int((k * a) % L), b'', cls='noncanonical_R'))

    # -- random byte strings
    for h in range(300):
        out.append(line(f'edge-rand-{h}', rnd.randbytes(32), rnd.randbytes(64), rnd.randbytes(h % 50),
                        cls='random'))
    # random pk that decodes + random sig
    n = 0
    while n < 100:
        pk = rnd.randbytes(32)
        if E._decompress(pk) is None:
            continue
        sig = rnd.randbytes(32) + enc_int(rnd.randrange(L))
        out.append(line(f'edge-randpk-{n}', pk, sig, b'', cls='random_decodable_pk'))
        n += 1
    return out


def sha512_vectors(rnd):
    lens = list(range(0, 301)) + [rnd.randrange(0, 1001) for _ in range(200)] + [1000, 1024]
    out = []
    for i, n in enumerate(lens):
        m = rnd.randbytes(n)
        out.append({'id': f'sha512-{i}-len{n}', 'msg': hx(m),
                    'sha512': hashlib.sha512(m).hexdigest()})
    return out


def write_jsonl(path, rows):
    with open(path, 'w') as f:
        for r in rows:
            f.write(json.dumps(r, sort_keys=True) + '\n')


def cmd_inputs(up, stage):
    os.makedirs(stage, exist_ok=True)
    rnd = random.Random(20261005)
    write_jsonl(f'{stage}/rfc8032.in.jsonl', rfc8032(f'{up}/rfc8032.txt'))
    write_jsonl(f'{stage}/djb_sign_input.in.jsonl', djb_sign_input(f'{up}/sign.input'))
    w, skipped = wycheproof(f'{up}/ed25519_test.json')
    write_jsonl(f'{stage}/wycheproof.in.jsonl', w)
    json.dump(skipped, open(f'{stage}/wycheproof_skipped.json', 'w'), indent=1)
    write_jsonl(f'{stage}/cctv.in.jsonl', cctv(f'{up}/cctv_ed25519vectors.json'))
    write_jsonl(f'{stage}/speccheck.in.jsonl', speccheck(f'{up}/speccheck_cases.json'))
    write_jsonl(f'{stage}/edge.in.jsonl', edge(rnd))
    write_jsonl(f'{stage}/sha512.jsonl', sha512_vectors(rnd))


def cmd_merge(stage, outdir):
    os.makedirs(outdir, exist_ok=True)
    for fn in sorted(os.listdir(stage)):
        if not fn.endswith('.in.jsonl'):
            continue
        name = fn[:-len('.in.jsonl')]
        ins = [json.loads(x) for x in open(f'{stage}/{fn}')]
        ver = {j['id']: j for j in map(json.loads, open(f'{stage}/{name}.judged.jsonl'))}
        assert len(ver) == len(ins), name
        rows = []
        for r in ins:
            v = ver[r['id']]
            r.update(sig_decodes=v['sig_decodes'], verify=v['verify'], verify_raw=v['verify_raw'])
            rows.append(r)
        write_jsonl(f'{outdir}/{name}.jsonl', rows)
        print(name, len(rows), 'accept', sum(r['verify_raw'] for r in rows))


def cmd_crosscheck(d):
    import glob
    import collections
    from nacl.signing import VerifyKey
    from nacl.exceptions import BadSignatureError
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
    from cryptography.exceptions import InvalidSignature

    def sodium(pk, sig, msg):
        try:
            VerifyKey(pk).verify(msg, sig)
            return True
        except (BadSignatureError, ValueError, Exception):
            return False

    def ossl(pk, sig, msg):
        try:
            Ed25519PublicKey.from_public_bytes(pk).verify(sig, msg)
            return True
        except (InvalidSignature, ValueError, Exception):
            return False

    tot = collections.Counter()
    for f in sorted(glob.glob(f'{d}/*.jsonl')):
        name = os.path.basename(f)
        for j in map(json.loads, open(f)):
            if 'verify_raw' not in j:
                continue
            pk, sig, msg = (bytes.fromhex(j[k]) for k in ('pk', 'sig', 'msg'))
            near = j['verify_raw']
            klass = j.get('cls') or ','.join(j.get('flags') or []) or '-'
            for lib, fn in (('libsodium', sodium), ('openssl', ossl)):
                v = fn(pk, sig, msg)
                if v != near:
                    tot[(lib, name, klass, f'near={near}', f'{lib}={v}')] += 1
    for k, c in sorted(tot.items()):
        print(c, *k)


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'inputs':
        cmd_inputs(sys.argv[2], sys.argv[3])
    elif cmd == 'merge':
        cmd_merge(sys.argv[2], sys.argv[3])
    elif cmd == 'crosscheck':
        cmd_crosscheck(sys.argv[2])
