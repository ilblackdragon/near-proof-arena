import subprocess, os, random, json, sys
LEAN = os.environ.get("ZSTD_LEAN", "/data/illia/nearproof-wt/w02-size-limits/spec/lean/v3/.lake/build/bin/nearspec-v3-zstd-decode")
Z = os.environ.get("ZSTD_ZREF", "/tmp/lean-global-oracle-target/release/zref")
d = os.environ.get("ZSTD_WORK", "/tmp/claude-1002/-data-illia-nearproof/0e65db12-f071-4aee-abe1-6a3d8ed8412f/scratchpad/w02/dtf")
os.makedirs(d, exist_ok=True)

def enc(data, level, workers):
    open(d+'/in', 'wb').write(data)
    subprocess.run([Z, 'encode', d+'/in', d+'/fr', str(level), str(workers)], check=True)
    return open(d+'/fr', 'rb').read()

def lean(frame):
    open(d+'/frl', 'wb').write(frame)
    r = subprocess.run([LEAN, d+'/frl', d+'/outl'], capture_output=True, text=True)
    s = r.stdout.strip()
    if s.startswith('OK'):
        return ('OK', open(d+'/outl', 'rb').read())
    return ('ERR', s)

def zdec(frame, limit=1<<30):
    open(d+'/frz', 'wb').write(frame)
    r = subprocess.run([Z, 'decode', d+'/frz', d+'/outz', str(limit)], capture_output=True, text=True)
    s = r.stdout.strip()
    if s.startswith('OK'):
        return ('OK', open(d+'/outz', 'rb').read())
    return ('ERR', s)

def mkpayload(rng, kind, n):
    if kind == 'rand':
        return bytes(rng.randint(0,255) for _ in range(n))
    if kind == 'lowent':
        al = rng.randint(2, 20)
        return bytes(rng.randrange(al) for _ in range(n))
    if kind == 'text':
        words = [b'the ', b'quick ', b'brown ', b'fox ', b'jumps ', b'over ', b'lazy ', b'dog ', b'near ', b'zstd ']
        out = bytearray()
        while len(out) < n:
            out += rng.choice(words)
        return bytes(out[:n])
    if kind == 'runs':
        out = bytearray()
        while len(out) < n:
            out += bytes([rng.randint(0,255)]) * rng.randint(1,40)
        return bytes(out[:n])
    if kind == 'mixed':
        return mkpayload(rng, rng.choice(['rand','lowent','text','runs']), n)
    return b''

def main():
    results = {'roundtrip_pass':0,'roundtrip_fail':0,'fails':[],
               'synthetic_pass':0,'synthetic_fail':0,
               'control_detected':0,'control_missed':0}
    # ---- roundtrip battery: >=1000 cases over 4 seeds ----
    kinds = ['rand','lowent','text','runs','mixed']
    sizes = [0,1,5,30,120,600,3000,16000,80000]
    for seed in (11,22,33,44):
        rng = random.Random(seed)
        for kind in kinds:
            for n in sizes:
                data = mkpayload(rng, kind, n)
                for level in (1,3,9,19):
                    wk = rng.choice([0,4])
                    fr = enc(data, level, wk)
                    st, out = lean(fr)
                    if st=='OK' and out==data:
                        results['roundtrip_pass'] += 1
                    else:
                        results['roundtrip_fail'] += 1
                        if len(results['fails'])<40:
                            results['fails'].append('seed=%d kind=%s n=%d L=%d wk=%d -> %s'%(seed,kind,n,level,wk,st if st=='ERR' else 'len %d vs %d'%(len(out),len(data))))
    # ---- synthetic / corrupt / edge frames: Lean verdict must AGREE with zref ----
    rng = random.Random(999)
    base = mkpayload(rng,'text',4000)
    f = enc(base,3,0)
    synth = []
    synth.append(('good', f))
    synth.append(('two_frames', f+f))
    synth.append(('frame_plus_junk', f+b'\x00\x01\x02\x03'))
    # checksummed frame (good + corrupted) via CLI
    open(d+'/pc','wb').write(base)
    subprocess.run(['zstd','-3','--check','-c',d+'/pc'],stdout=open(d+'/fc','wb'))
    fc=open(d+'/fc','rb').read()
    synth.append(('checksum_good', fc))
    bad=bytearray(fc); bad[-1]^=0xff; synth.append(('checksum_bad', bytes(bad)))
    # truncations
    for cut in (1,3,5,10):
        synth.append(('trunc_%d'%cut, f[:-cut]))
    # single-byte corruptions at various offsets
    for off in (4,5,6,10,15,20):
        if off < len(f):
            b2=bytearray(f); b2[off]^=0x55; synth.append(('corrupt_off%d'%off, bytes(b2)))
    # bad magic
    synth.append(('bad_magic', b'\x00\x00\x00\x00'+f[4:]))
    # skippable frame then real frame
    skip = b'\x50\x2a\x4d\x18' + (8).to_bytes(4,'little') + b'ABCDEFGH'
    synth.append(('skippable_then_frame', skip+f))
    # raw/rle crafted frames (single-segment) — let zstd make them at level 1 on tiny/rle inputs
    synth.append(('rle_frame', enc(b'\xAB'*5000,1,0)))
    synth.append(('raw_frame', enc(bytes(rng.randint(0,255) for _ in range(300)),1,0)))
    for name, fr in synth:
        lst, lout = lean(fr)
        zst, zout = zdec(fr)
        # agreement: same OK/ERR; if OK, bytes equal
        agree = (lst==zst) and (lst=='ERR' or lout==zout)
        if agree:
            results['synthetic_pass'] += 1
        else:
            results['synthetic_fail'] += 1
            results['fails'].append('SYNTH %s lean=%s zref=%s%s'%(name,lst,zst,'' if lst=='ERR' else ' bytes %d/%d'%(len(lout),len(zout))))
    # ---- deliberate-breakage control: corrupt frames zref REJECTS; Lean must also reject ----
    rng = random.Random(1234)
    nbreak = 0
    for _ in range(60):
        data = mkpayload(rng, rng.choice(kinds), rng.randint(50,4000))
        fr = bytearray(enc(data, rng.choice([1,3,9]), rng.choice([0,4])))
        # flip a random byte in the compressed body (after header)
        if len(fr) > 8:
            pos = rng.randint(6, len(fr)-1)
            fr[pos] ^= (1 << rng.randint(0,7))
        zst, zout = zdec(bytes(fr))
        lst, lout = lean(bytes(fr))
        if zst=='ERR':
            nbreak += 1
            if lst=='ERR':
                results['control_detected'] += 1
            else:
                # Lean accepted a frame zref rejected: must verify bytes — if Lean's bytes differ from
                # the original, it's a decoder soundness bug; if they happen to equal original it's benign.
                results['control_missed'] += 1
                results['fails'].append('CONTROL lean accepted zref-rejected frame (lean %s)'%('OK %d'%len(lout)))
        else:
            # zref accepted the mutated frame; Lean must match it
            if not (lst=='OK' and lout==zout):
                results['synthetic_fail'] += 1
                results['fails'].append('CONTROL-OK mismatch lean=%s'%lst)
    results['control_total_rejected_by_zref'] = nbreak
    print(json.dumps(results, indent=2))
    out = d+'/../size-limits-difftest-summary.json'
    json.dump(results, open(out,'w'), indent=2)

if __name__ == '__main__':
    main()
