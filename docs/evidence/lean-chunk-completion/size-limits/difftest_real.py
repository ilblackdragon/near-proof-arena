import subprocess, os, glob, struct, json, random
LEAN = os.environ.get("ZSTD_LEAN", "/data/illia/nearproof-wt/w02-size-limits/spec/lean/v3/.lake/build/bin/nearspec-v3-zstd-decode")
Z = os.environ.get("ZSTD_ZREF", "/tmp/lean-global-oracle-target/release/zref")
d = os.environ.get("ZSTD_WORK", "/tmp/claude-1002/-data-illia-nearproof/0e65db12-f071-4aee-abe1-6a3d8ed8412f/scratchpad/w02/dtr")
os.makedirs(d, exist_ok=True)

def state_witness_of(path):
    raw = open(path, 'rb').read()
    off = 0
    tl = struct.unpack('<I', raw[off:off+4])[0]; off += 4
    if raw[off:off+tl] != b'near-arena-witness-v3':
        return None
    off += tl
    swl = struct.unpack('<I', raw[off:off+4])[0]; off += 4
    return raw[off:off+swl]

def main():
    cases = []
    for base in ['/data/illia/nearproof-deps/corpora/d3c7','/data/illia/nearproof-deps/corpora/d3c8',
                 '/data/illia/nearproof-deps/corpora/d3c9','/data/illia/nearproof-deps/corpora/d3c10',
                 '/data/illia/nearproof-deps/corpora/d1run','/data/illia/nearproof-deps/corpora/d2corpus.v2']:
        cases += glob.glob(base+'/**/witness.bin', recursive=True)
    random.Random(2026).shuffle(cases)
    res = {'real_pass':0,'real_fail':0,'levels':{},'fails':[],'total':0}
    n = 0
    for w in cases:
        if n >= 1200: break
        sw = state_witness_of(w)
        if sw is None or len(sw) == 0: continue
        # 4 encodings (zstd 1.5.6): level 1 w4 (nearcore's), plus 3,9 and w0 variety across cases
        for (lvl, wk) in [(1,4),(3,0),(9,4)]:
            open(d+'/sw','wb').write(sw)
            subprocess.run([Z,'encode',d+'/sw',d+'/fr',str(lvl),str(wk)], check=True)
            fr = open(d+'/fr','rb').read()
            open(d+'/frl','wb').write(fr)
            r = subprocess.run([LEAN, d+'/frl', d+'/outl'], capture_output=True, text=True)
            s = r.stdout.strip()
            ok = s.startswith('OK') and open(d+'/outl','rb').read() == sw
            res['total'] += 1
            key = 'L%d_w%d' % (lvl, wk)
            res['levels'].setdefault(key, [0,0])
            if ok:
                res['real_pass'] += 1; res['levels'][key][0] += 1
            else:
                res['real_fail'] += 1; res['levels'][key][1] += 1
                if len(res['fails']) < 20:
                    res['fails'].append('%s L=%d w=%d swlen=%d -> %s' % (os.path.basename(os.path.dirname(w)), lvl, wk, len(sw), s))
        n += 1
    res['distinct_witnesses'] = n
    print(json.dumps(res, indent=2))
    json.dump(res, open(d+'/../size-limits-real-difftest.json','w'), indent=2)

if __name__ == '__main__':
    main()
