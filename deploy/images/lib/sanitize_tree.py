#!/usr/bin/env python3
"""Make a flattened image tree satisfy the CONTRACTS §1 tree rules.

* paths must be unique under case folding: of each colliding group keep the
  all-lowercase name (else the lexicographically first) and delete the rest
  (directories may not collide);
* no setuid/setgid/sticky bits on regular files; owner-writable everything
  (so the build can clean up);
* symlinks/devices/fifos/sockets are an error (flatten with --dereference).

Writes the removed paths to `<root>.case-removed`.
"""
import os
import stat
import sys

root = sys.argv[1]
removed = []
for d, dirs, files in os.walk(root):
    groups = {}
    for n in dirs + files:
        groups.setdefault(n.casefold(), []).append(n)
    for g in groups.values():
        if len(g) < 2:
            continue
        keep = min(g, key=lambda n: (n != n.lower(), n))
        for n in g:
            if n == keep:
                continue
            p = os.path.join(d, n)
            if os.path.isdir(p) and not os.path.islink(p):
                sys.exit(f"case collision on directory {p}")
            os.remove(p)
            removed.append(os.path.relpath(p, root))
            if n in files:
                files.remove(n)
    for n in files:
        p = os.path.join(d, n)
        st = os.lstat(p)
        if not stat.S_ISREG(st.st_mode):
            sys.exit(f"not a regular file: {p}")
        mode = stat.S_IMODE(st.st_mode)
        new = (mode & ~0o7000) | 0o200
        if new != mode:
            os.chmod(p, new)
    for n in dirs:
        p = os.path.join(d, n)
        if os.path.islink(p):
            sys.exit(f"symlink: {p}")
        os.chmod(p, stat.S_IMODE(os.lstat(p).st_mode) | 0o700)
with open(root + ".case-removed", "w") as f:
    f.write("\n".join(sorted(removed)))
