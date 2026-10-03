#!/usr/bin/env python3
"""TreeDigest (docs/CONTRACTS.md §1; same algorithm as arena_types::tree_digest)
over the git-TRACKED files under one or more directories.

  tree_digest.py [--relative-to DIR] PATH...

Entries are [relative_path, "file"|"exec", "sha256:<hex>"], sorted by path
bytes, serialized as JCS (compact JSON, no whitespace), then sha256. Paths are
relative to the repository root unless --relative-to is given (then relative
to that directory, which reproduces `arena-admin tree-digest DIR` on a clean
checkout of DIR). Only tracked files are hashed, so build outputs (.lake/,
target/) never enter the digest. Symlinks are rejected.
"""
import hashlib, json, os, subprocess, sys

def main():
    args = sys.argv[1:]
    rel = None
    if args[:1] == ["--relative-to"]:
        rel, args = args[1], args[2:]
    repo = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                          check=True).stdout.strip()
    entries = []
    for p in args:
        out = subprocess.run(["git", "-C", repo, "ls-files", "-s", "--", os.path.relpath(os.path.abspath(p), repo)],
                             capture_output=True, text=True, check=True).stdout
        for line in out.splitlines():
            meta, path = line.split("\t", 1)
            mode = meta.split()[0]
            if mode not in ("100644", "100755"):
                sys.exit(f"unsupported entry {path} (mode {mode})")
            data = open(os.path.join(repo, path), "rb").read()
            shown = os.path.relpath(os.path.join(repo, path), os.path.abspath(rel)) if rel else path
            entries.append([shown, "exec" if mode == "100755" else "file",
                            "sha256:" + hashlib.sha256(data).hexdigest()])
    if not entries:
        sys.exit("no tracked files")
    entries.sort(key=lambda e: e[0].encode())
    jcs = json.dumps(entries, separators=(",", ":"), ensure_ascii=False).encode()
    print("sha256:" + hashlib.sha256(jcs).hexdigest())

if __name__ == "__main__":
    main()
