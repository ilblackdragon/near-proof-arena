"""Which single-cell witness mutations does the base prover's precheck (all constraints, all bus
balances) reject? usage: precheck_mutations.py RUN_DIR PROVER TABLE:ROW:COL[:XOR] ...
Prints PRECHECK_REJECTED / PRECHECK_ACCEPTED per mutation (the run is stopped after precheck)."""
import pathlib, shutil, subprocess, sys, tempfile
run, prover = pathlib.Path(sys.argv[1]), sys.argv[2]
root = pathlib.Path(__file__).resolve().parents[4]
air = root / 'examples/np-udr-stark-v2/source/near-air-v3.json'
k = root / 'research/near-compression/final-soundness'
for spec in sys.argv[3:]:
    parts = spec.split(':')
    table, row, col = parts[0], int(parts[1]), int(parts[2])
    xor = int(parts[3]) if len(parts) > 3 else 1
    with tempfile.TemporaryDirectory(prefix='e2e-pre-', dir='/data/illia/nearproof-deps') as d:
        d = pathlib.Path(d)
        shutil.copytree(run / 'dump', d / 'dump')
        f = d / 'dump' / f'{table}.bin'
        b = bytearray(f.read_bytes())
        w = int.from_bytes(b[4:8], 'little')
        off = 8 + 4 * (row * w + col)
        v = int.from_bytes(b[off:off + 4], 'little') ^ xor
        b[off:off + 4] = v.to_bytes(4, 'little')
        f.write_bytes(bytes(b))
        p = subprocess.Popen([prover, 'base', str(air), str(d / 'dump'), str(d / 'out'),
                              str(k / 'calc/dkt_certs_o2.json'), str(k / 'lean/DKTCertsO2_big.keys')],
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        out = []
        verdict = 'PRECHECK_REJECTED'
        for line in p.stdout:
            out.append(line)
            if line.startswith('PRECHECK OK'):
                verdict = 'PRECHECK_ACCEPTED'
                p.kill()
                break
        p.wait()
        tail = [l.strip() for l in out if 'panicked' in l or 'constraint' in l.lower() or 'bus' in l.lower()][-1:]
        print(verdict, spec, f'width={w}', tail)
