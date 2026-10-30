import subprocess, os, json
LEAN = os.environ.get("ZSTD_LEAN", "/data/illia/nearproof-wt/w02-size-limits/spec/lean/v3/.lake/build/bin/nearspec-v3-zstd-decode")
Z = os.environ.get("ZSTD_ZREF", "/tmp/lean-global-oracle-target/release/zref")
d = os.environ.get("ZSTD_WORK", "/tmp/claude-1002/-data-illia-nearproof/0e65db12-f071-4aee-abe1-6a3d8ed8412f/scratchpad/w02/bnd2")
os.makedirs(d, exist_ok=True)
CAP = 50331648   # 48 MiB encoded cap (MAX_COMPRESSED_STATE_WITNESS_SIZE)
DEC = 67108864   # 64 MiB decode cap (MAX_UNCOMPRESSED_STATE_WITNESS_SIZE)

def lean(frame_path, encCap=None, decCap=None):
    a = [LEAN, frame_path, '-']
    if encCap is not None: a.append(str(encCap))
    if decCap is not None: a.append(str(decCap))
    return subprocess.run(a, capture_output=True, text=True, timeout=1800).stdout.strip()

out = {}
# encoded-length boundary: a frame of exactly CAP and CAP+1 bytes (contents start with the zstd
# magic; the length check fires at CAP+1 before any decode, matching nearcore validate.rs:82-88).
for nm, ln in [('enc.at48', CAP), ('enc.over48', CAP+1)]:
    # magic + FHD(0) + window-desc(0 => 1 KiB window) + a last raw block header claiming 2 MB
    # (> block max) so decode fails fast AFTER the length check; padded to the exact length.
    bh = ((2000000 << 3) | (0 << 1) | 1)   # last=1, raw(type 0), size=2_000_000
    hdr = b'\x28\xb5\x2f\xfd' + b'\x00' + b'\x00' + bh.to_bytes(3, 'little')
    buf = hdr + b'\x00' * (ln - len(hdr))
    open(d+'/'+nm, 'wb').write(buf)
    out[nm] = {'encoded_len': ln, 'lean': lean(d+'/'+nm, CAP, DEC)}
# decoded-size boundary: RLE frame decoding to exactly DEC and DEC+1; the 64 MiB cut-off must fire
# at DEC+1. zref is the reference verdict.
for nm, n in [('dec.at64', DEC), ('dec.over64', DEC+1)]:
    open(d+'/raw', 'wb').write(b'\x00'*n)
    subprocess.run([Z, 'encode', d+'/raw', d+'/f'+nm, '1', '0'], check=True)
    fp = d+'/f'+nm
    # zref reference with the same limit
    zr = subprocess.run([Z, 'decode', fp, d+'/z'+nm, str(DEC)], capture_output=True, text=True).stdout.strip()
    out[nm] = {'decoded_len': n, 'encoded_len': os.path.getsize(fp),
               'lean': lean(fp, CAP, DEC), 'zref': zr}
print(json.dumps(out, indent=2))
json.dump(out, open(d+'/../size-limits-boundaries.json', 'w'), indent=2)
