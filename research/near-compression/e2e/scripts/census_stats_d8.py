"""E2E-D D-8: per-table statistics of a heights census (census_d8.sh output).
usage: census_stats_d8.py CENSUS_DIR
Prints, per table, the compact-log distribution, the padding kind (zero / non-zero), and the TAPE
(public-message table) log and width distribution, which a class must match exactly (cached TAPE)."""
import collections, json, math, pathlib, sys

P = 0x78000001
ORDER = ["sha_t", "sha_r", "node", "head", "val", "walk", "uniq", "ups", "chacha", "rng", "shuf", "codec", "scandist",
         "proc", "mem", "cmp", "rcpt", "acct", "akey", "bnd", "srcp", "size", "qv", "mrk", "sort"]
BUS_OFFSET = 128


def tape_shape(pubmsgs):
    """(log, width, rows) of the TAPE harness table (pq-state-port `harness`)."""
    net = collections.Counter()
    for bus, send, msg in pubmsgs:
        k = (bus + BUS_OFFSET, tuple(msg))
        net[k] = (net[k] + (1 if send else P - 1)) % P
    nz = [k for k, c in net.items() if c != 0]
    keys = sorted({(k[0], len(k[1])) for k in net})
    wmsg = max([k[1] for k in keys] + [1])
    width = wmsg + 1 + max(1, len(keys))
    rows = len(nz)
    h = max(4, 1 << max(0, math.ceil(math.log2(max(rows, 1)))))
    return int(math.log2(h)), width, rows


def load(root):
    out = {}
    for d in sorted(pathlib.Path(root).iterdir()):
        f = d / 'heights.json'
        if not f.exists():
            continue
        h = json.loads(f.read_text())
        h['TAPE'] = dict(zip(('log', 'width', 'rows'), tape_shape(json.loads((d / 'pubmsgs.json').read_text()))))
        out[d.name] = h
    return out


def padkind(H):
    """table -> 'zero' if every chunk with a padding row pads with zeros, 'nonzero' otherwise."""
    kind = {}
    for t in ORDER:
        nz = any(h[t]['used_rows'] < (1 << h[t]['classical_log']) and not h[t]['pad_zero'] for h in H.values())
        kind[t] = 'nonzero' if nz else 'zero'
    return kind


if __name__ == '__main__':
    H = load(sys.argv[1])
    print('chunks', len(H))
    kind = padkind(H)
    for t in ORDER:
        c = collections.Counter(h[t]['log'] for h in H.values())
        mx = max(h[t]['last_nonzero'] if kind[t] == 'zero' else h[t]['used_rows'] for h in H.values())
        print(f"{t:9s} w={H[next(iter(H))][t]['width']:4d} pad={kind[t]:7s} maxLog={H[next(iter(H))][t]['max_log']:2d} compact logs {dict(sorted(c.items()))} max rows {mx}")
    c = collections.Counter((h['TAPE']['log'], h['TAPE']['width']) for h in H.values())
    print('TAPE (log, width):', dict(sorted(c.items())))
