"""E2E negative tests against a completed run (each check is a fresh verifier process).

usage: negatives.py RUN_DIR CASE_DIR OTHER_CASE_DIR [--wrong-witness]
Writes RUN_DIR/negatives/*.log and RUN_DIR/NEGATIVES.json; exits nonzero if anything is accepted
that must be rejected, or if the untouched packet is rejected.
"""
import json, os, pathlib, shutil, subprocess, sys, tempfile

run, case, other = map(pathlib.Path, sys.argv[1:4])
wrong_witness = '--wrong-witness' in sys.argv
root = pathlib.Path(__file__).resolve().parents[4]
air = root / 'examples/np-udr-stark-v2/source/near-air-v3.json'
B = pathlib.Path(os.environ.get('PROVER', run / 'tools/prover'))
C = run / 'tools'
REF = os.environ.get('REFERENCE_CHECKER', '/data/illia/nearproof/spec/lean/v3/.lake/build/bin/nearspec-v3-check')
pin = (run / 'SETUP.sha256').read_text().strip()
packet = (run / 'FINAL.bundle').read_bytes()
outdir = run / 'negatives'
outdir.mkdir(exist_ok=True)
env = dict(os.environ, RAYON_NUM_THREADS=os.environ.get('RAYON_NUM_THREADS', '8'))
results = {}

def verify(name, claim, bundle_bytes, setup_pin=pin, expect_ok=False, setup_bytes=None, reason=None):
    """`setup_bytes`: verify against this setup (pinned by `setup_pin`) instead of the run's.
    `reason`: a rejection only passes if the verifier's output contains it (the check that
    must fire, not some later one)."""
    with tempfile.TemporaryDirectory(prefix='e2e-neg-', dir='/data/illia/nearproof-deps') as d:
        b = pathlib.Path(d) / 'FINAL.bundle'
        b.write_bytes(bundle_bytes)
        s = run / 'SETUP.json'
        if setup_bytes is not None:
            s = pathlib.Path(d) / 'SETUP.json'
            s.write_bytes(setup_bytes)
        r = subprocess.run([str(B), 'verify', str(air), str(claim), str(C / 'statepublic'),
                            str(s), setup_pin, str(b)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600, env=env)
    (outdir / f'{name}.log').write_bytes(r.stdout)
    ok = r.returncode == 0 and b'INDEPENDENT_VERIFY_OK' in r.stdout
    last = r.stdout.decode(errors='replace').strip().splitlines()[-3:]
    passed = ok == expect_ok and (ok or reason is None or reason.encode() in r.stdout)
    results[name] = {'accepted': ok, 'expected': 'accept' if expect_ok else 'reject',
                     'pass': passed, 'tail': last}
    if reason is not None:
        results[name]['required_reason'] = reason
    print(('PASS ' if passed else 'FAIL ') + name + (' accepted' if ok else ' rejected'))

claim = case / 'claim.bin'
verify('untouched', claim, packet, expect_ok=True)

# --- mutated public outputs (the claim: chunk-header outputs + trusted facts) ---
cb = (case / 'claim.bin').read_bytes()
with tempfile.TemporaryDirectory(prefix='e2e-claims-', dir='/data/illia/nearproof-deps') as d:
    d = pathlib.Path(d)
    for frac in (0.02, 0.25, 0.5, 0.75, 0.98):
        i = int(len(cb) * frac)
        m = bytearray(cb); m[i] ^= 0x01
        p = d / f'claim-{i}.bin'; p.write_bytes(bytes(m))
        # The expected verdict is the reference relation's: the Lean checker on (mutated claim,
        # original witness). A byte the relation does not bind leaves a true statement, which the
        # proof must then accept; any other mutation must be rejected.
        cdir = d / f'case-{i}'; cdir.mkdir()
        shutil.copy(p, cdir / 'claim.bin'); shutil.copy(case / 'witness.bin', cdir / 'witness.bin')
        ref = subprocess.run([REF, str(cdir)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
        ref_accept = b'"verdict": "accept"' in ref.stdout
        verify(f'claim_byte_{i}_flipped' + ('_ref_accepts' if ref_accept else ''), p, packet, expect_ok=ref_accept)
    shutil.copy(other / 'claim.bin', d / 'other.bin')
    verify('claim_of_other_chunk', d / 'other.bin', packet)

# --- mutated proof bytes ---
n = int.from_bytes(packet[8:16], 'little')
body = 16 + n
v2 = packet[:8] == b'NPQCH02\0'
if v2:
    m_u = int.from_bytes(packet[body:body + 4], 'little')
    u_off = body + 4
    proof_off = u_off + 48 * m_u
else:
    proof_off = body
def flip(pos, name):
    m = bytearray(packet); m[pos] ^= 0x01
    verify(name, claim, bytes(m))
if n:
    flip(16, 'hint_byte_flipped')
if v2:
    flip(u_off + 1, 'base_point_u_flipped')
    flip(u_off + 48 * m_u - 2, 'base_point_u_last_flipped')
plen = len(packet) - proof_off
for frac in (0.0, 0.1, 0.33, 0.5, 0.66, 0.9):
    flip(proof_off + int(plen * frac) + (8 if frac == 0.0 else 0), f'proof_byte_{int(frac*100)}pct_flipped')
flip(len(packet) - 1, 'proof_last_byte_flipped')
verify('trailing_byte', claim, packet + b'\0')
verify('truncated_proof', claim, packet[:-100])
verify('truncated_to_hint', claim, packet[:16])
verify('untrusted_setup_pin', claim, packet, setup_pin='0' * 64)

# --- obligation H (2026-11-03): FINAL heights pinned by the setup, checked by V_d first ---
setup_json = json.loads((run / 'SETUP.json').read_bytes())
if setup_json.get('final_heights'):
    import hashlib
    hs = setup_json['final_heights']
    a = 1  # the largest AIR (log 21): the review #1/#3 target
    log, tight = hs[a]
    def tampered(t):
        with tempfile.TemporaryDirectory(prefix='e2e-th-', dir='/data/illia/nearproof-deps') as d:
            o = pathlib.Path(d) / 'b'
            subprocess.run([str(B), 'tamper-height', str(run / 'SETUP.json'), str(run / 'FINAL.bundle'),
                            str(a), str(t), str(o)], check=True, stdout=subprocess.DEVNULL, env=env)
            return o.read_bytes()
    verify('proof_tight_height_plus4', claim, tampered(tight + 4), reason='differs from the pinned')
    verify('proof_tight_height_max_review1', claim, tampered(1 << log), reason='differs from the pinned')
    def repinned(s):
        b = json.dumps(s, separators=(',', ':')).encode()
        return b, hashlib.sha256(b).hexdigest()
    s = json.loads((run / 'SETUP.json').read_bytes()); s['final_heights'][a][1] = tight + 4
    b, h = repinned(s)
    verify('setup_heights_changed_repinned', claim, packet, setup_pin=h, setup_bytes=b, reason='differs from the pinned')
    s = json.loads((run / 'SETUP.json').read_bytes()); del s['final_heights']
    b, h = repinned(s)
    verify('setup_heights_removed_repinned', claim, packet, setup_pin=h, setup_bytes=b, reason='must pin the FINAL trace heights')
    # control: the same re-serialization of the unchanged setup, re-pinned, accepts
    b, h = repinned(json.loads((run / 'SETUP.json').read_bytes()))
    verify('setup_reserialized_repinned_control', claim, packet, setup_pin=h, setup_bytes=b, expect_ok=True)

# --- wrong witness: a base proof of a witness the AIR rejects (prover precheck skipped) ---
if wrong_witness:
    with tempfile.TemporaryDirectory(prefix='e2e-ww-', dir='/data/illia/nearproof-deps') as d:
        d = pathlib.Path(d)
        shutil.copytree(run / 'dump', d / 'dump')
        # head row 10, column 20: a constrained cell (constraint 38 of `head` fails); see
        # precheck_mutations.py for cells the AIR leaves free (e.g. last-active-row transition columns)
        t = d / 'dump' / 'head.bin'
        m = bytearray(t.read_bytes()); w = int.from_bytes(m[4:8], 'little'); off = 8 + 4 * (10 * w + 20)
        m[off] ^= 0x01; t.write_bytes(bytes(m))
        k = root / 'research/near-compression/final-soundness'
        r = subprocess.run([str(B), 'base', str(air), str(d / 'dump'), str(d / 'out'),
                            str(k / 'calc/dkt_certs_o2.json'), str(k / 'lean/DKTCertsO2_big.keys')],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=3600,
                           env=dict(env, NEARPROOF_NEGATIVE_SKIP_PRECHECK='1'))
        (outdir / 'wrong_witness_base.log').write_bytes(r.stdout)
        ok = r.returncode == 0 and b'BASE_VERIFIED' in r.stdout
        tail = r.stdout.decode(errors='replace').strip().splitlines()[-3:]
        results['wrong_witness_base_proof'] = {'accepted': ok, 'expected': 'reject', 'pass': not ok, 'tail': tail}
        print(('PASS ' if not ok else 'FAIL ') + 'wrong_witness_base_proof ' + ('accepted' if ok else 'rejected'))
        # the honest prover's own check also refuses it
        r = subprocess.run([str(B), 'base', str(air), str(d / 'dump'), str(d / 'out2'),
                            str(k / 'calc/dkt_certs_o2.json'), str(k / 'lean/DKTCertsO2_big.keys')],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=3600, env=env)
        (outdir / 'wrong_witness_precheck.log').write_bytes(r.stdout)
        ok = r.returncode == 0
        results['wrong_witness_prover_precheck'] = {'accepted': ok, 'expected': 'reject', 'pass': not ok,
                                                     'tail': r.stdout.decode(errors='replace').strip().splitlines()[-2:]}
        print(('PASS ' if not ok else 'FAIL ') + 'wrong_witness_prover_precheck ' + ('accepted' if ok else 'rejected'))

(run / 'NEGATIVES.json').write_text(json.dumps(results, indent=2) + '\n')
bad = [k for k, v in results.items() if not v['pass']]
print('NEGATIVES', 'ALL_PASS' if not bad else f'FAILED {bad}', len(results))
sys.exit(1 if bad else 0)
