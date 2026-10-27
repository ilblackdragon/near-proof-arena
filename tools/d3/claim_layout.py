#!/usr/bin/env python3
"""claim_layout.py [--summary] CLAIM.BIN...: print the shard layout encoded in each claim.

Heuristic scan: the first well-formed borsh `ShardLayout` V2/V3 in the claim bytes (boundary
accounts, then `shard_ids` of length boundaries + 1). For V2 it also decodes `shards_split_map` and
`shards_parent_map`. With `--summary` (paths read from stdin when no CLAIM.BIN is given) it prints
counts of `V2`, `V2+parent_map`, `V3` and `none`, which is how a corpus is checked for layouts that
carry a V2 parent map."""
import collections, struct, sys


def scan(b):
    u32 = lambda j: struct.unpack_from('<I', b, j)[0]
    u64 = lambda j: struct.unpack_from('<Q', b, j)[0]
    for i in range(len(b) - 5):
        if b[i] not in (2, 3):
            continue
        try:
            n = u32(i + 1)
            if not 1 <= n <= 64:
                continue
            j = i + 5; accs = []; ok = True
            for _ in range(n):
                l = u32(j)
                if not 1 <= l <= 64:
                    ok = False; break
                s = b[j + 4:j + 4 + l]
                if len(s) != l or not all(32 < c < 127 for c in s):
                    ok = False; break
                accs.append(s.decode()); j += 4 + l
            if not ok or u32(j) != n + 1:
                continue
            j += 4
            ids = [u64(j + 8 * k) for k in range(n + 1)]; j += 8 * (n + 1)
            if b[i] == 3:
                return {"version": 3, "boundaries": accs, "shard_ids": ids}
            j += 4 + 16 * u32(j)          # id_to_index_map
            j += 4 + 16 * u32(j)          # index_to_id_map
            split = None
            if b[j] == 1:
                j += 1; k = u32(j); j += 4; split = {}
                for _ in range(k):
                    key = u64(j); c = u32(j + 8)
                    split[key] = [u64(j + 12 + 8 * t) for t in range(c)]; j += 12 + 8 * c
            else:
                j += 1
            parent = None
            if b[j] == 1:
                j += 1; k = u32(j); j += 4
                parent = {u64(j + 16 * t): u64(j + 16 * t + 8) for t in range(k)}
            return {"version": 2, "boundaries": accs, "shard_ids": ids, "split_map": split,
                    "parent_map": parent}
        except struct.error:
            continue
    return None


def main():
    args = sys.argv[1:]
    summary = "--summary" in args
    paths = [a for a in args if a != "--summary"] or [l.strip() for l in sys.stdin if l.strip()]
    counts = collections.Counter()
    for p in paths:
        if not p.endswith(".bin"):
            p = p.rstrip("/") + "/claim.bin"
        lay = scan(open(p, "rb").read())
        if summary:
            key = "none" if lay is None else ("V3" if lay["version"] == 3 else
                                               ("V2+parent_map" if lay["parent_map"] is not None else "V2"))
            counts[key] += 1
        else:
            print(p, lay)
    if summary:
        print(dict(counts))


if __name__ == "__main__":
    main()
