"""D-5 negatives for a tree-wrap packet (each check is a fresh `tree-verify` process).

usage: tree_negatives.py RUN_DIR CLAIM OTHER_CLAIM [OTHER_RUN_DIR]
Writes RUN_DIR/negatives/*.log and RUN_DIR/NEGATIVES.json; exits nonzero if anything that must be
rejected is accepted, or if the untouched packet is rejected.
"""
import json, os, pathlib, subprocess, sys, tempfile

run, claim, other = map(pathlib.Path, sys.argv[1:4])
other_run = pathlib.Path(sys.argv[4]) if len(sys.argv) > 4 else None
root = pathlib.Path(__file__).resolve().parents[4]
air = root / 'examples/np-udr-stark-v2/source/near-air-v3.json'
B = os.environ['PROVER']
pin = (run / 'SETUP.sha256').read_text().strip()
packet = (run / 'WRAP.bundle').read_bytes()
setup = (run / 'SETUP.json').read_bytes()
out = run / 'negatives'
out.mkdir(exist_ok=True)
env = dict(os.environ, RAYON_NUM_THREADS='1')
results = {}


def verify(name, claim_path, bundle, setup_bytes=setup, setup_pin=pin, expect_ok=False):
    with tempfile.TemporaryDirectory(prefix='tree-neg-', dir='/data/illia/nearproof-deps') as d:
        b = pathlib.Path(d) / 'WRAP.bundle'
        b.write_bytes(bundle)
        s = pathlib.Path(d) / 'SETUP.json'
        s.write_bytes(setup_bytes)
        r = subprocess.run([B, 'tree-verify', str(air), str(claim_path), str(s), setup_pin, str(b)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600, env=env)
    (out / f'{name}.log').write_bytes(r.stdout)
    ok = r.returncode == 0 and b'INDEPENDENT_TREE_VERIFY_OK' in r.stdout
    results[name] = {'accepted': ok, 'expected_accept': expect_ok, 'pass': ok == expect_ok,
                     'last': r.stdout.decode(errors='replace').strip().splitlines()[-1:]}
    print(('PASS ' if ok == expect_ok else 'FAIL ') + name, results[name]['last'])


def flip(b, i):
    b = bytearray(b)
    b[i] ^= 1
    return bytes(b)


verify('control', claim, packet, expect_ok=True)
verify('other_claim', other, packet)
n = int.from_bytes(packet[8:16], 'little')
cls = int.from_bytes(packet[16 + n:20 + n], 'little')
body = 16 + n + 8 + 48 * int.from_bytes(packet[20 + n:24 + n], 'little')
verify('flip_hint', claim, flip(packet, 16))
for c in range(3):
    if c != cls:
        # the other template classes (another base parameter set for ctx; D_wrap binds the class)
        verify(f'class_{c}', claim, packet[:16 + n] + c.to_bytes(4, 'little') + packet[20 + n:])
verify('class_out_of_range', claim, packet[:16 + n] + (7).to_bytes(4, 'little') + packet[20 + n:])
verify('flip_u', claim, flip(packet, 16 + n + 8))
for k, off in enumerate([body + 10, body + 2000, len(packet) // 2, len(packet) - 40]):
    verify(f'flip_proof_{k}', claim, flip(packet, off))
verify('truncated', claim, packet[:-1])
verify('magic', claim, b'NPQTW01\0' + packet[8:])
verify('wrong_pin', claim, packet, setup_pin='0' * 64)
s = json.loads(setup)
s['level'] += 1
sb = json.dumps(s, separators=(',', ':')).encode()
import hashlib
verify('setup_level_repinned', claim, packet, setup_bytes=sb, setup_pin=hashlib.sha256(sb).hexdigest())
s = json.loads(setup)
s['program'][100][0] ^= 1
sb = json.dumps(s, separators=(',', ':')).encode()
verify('setup_program_repinned', claim, packet, setup_bytes=sb, setup_pin=hashlib.sha256(sb).hexdigest())
s = json.loads(setup)
s['final_heights'][1][1] += 4
sb = json.dumps(s, separators=(',', ':')).encode()
verify('setup_heights_repinned', claim, packet, setup_bytes=sb, setup_pin=hashlib.sha256(sb).hexdigest())
if other_run is not None:
    # the other chunk's packet (same setup) against this chunk's claim, and vice versa
    verify('other_packet_this_claim', claim, (other_run / 'WRAP.bundle').read_bytes())
(run / 'NEGATIVES.json').write_text(json.dumps(results, indent=1) + '\n')
bad = [k for k, v in results.items() if not v['pass']]
print(f'TREE_NEGATIVES {len(results) - len(bad)}/{len(results)} pass', bad)
sys.exit(1 if bad else 0)
