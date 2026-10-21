"""Integration negatives against a completed run; each invokes the independent verifier."""
import pathlib
import subprocess
import sys
import tempfile

binary, air, claim, helper, run = sys.argv[1:]
run = pathlib.Path(run)
pin = (run / 'SETUP.sha256').read_text().strip()
packet = (run / 'FINAL.bundle').read_bytes()
with tempfile.TemporaryDirectory(prefix='chunk-packet-tests-') as directory:
    directory = pathlib.Path(directory)
    changed = bytearray(packet)
    changed[-1] ^= 1
    cases = {'changed_proof': bytes(changed), 'trailing_bytes': packet + b'\x00',
             'truncated_hint': packet[:16]}
    for name, contents in cases.items():
        path = directory / name
        path.write_bytes(contents)
        result = subprocess.run([binary, 'verify', air, claim, helper,
                                 str(run / 'SETUP.json'), pin, str(path)],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        (run / f'negative-{name}.log').write_bytes(result.stdout)
        assert result.returncode != 0, f'{name} accepted'
        print(f'REJECTED {name}')
    result = subprocess.run([binary, 'verify', air, claim, helper,
                             str(run / 'SETUP.json'), '0' * 64, str(run / 'FINAL.bundle')],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    (run / 'negative-setup-pin.log').write_bytes(result.stdout)
    assert result.returncode != 0, 'untrusted setup accepted'
    print('REJECTED untrusted_setup')
