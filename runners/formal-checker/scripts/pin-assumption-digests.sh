#!/usr/bin/env bash
# Pin security/assumptions/*.json `lean_decl_digest` to the structural content
# hash (decl-hash, the same hash the NDJSON audit compares) of each
# `lean_decl` in the pinned formal-core. Deterministic; re-run after any
# formal-core change and commit the result (a changed digest is a governed change).
set -euo pipefail
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
tc="$(cat "$repo/runners/formal-checker/lean-toolchain" | sed 's|leanprover/lean4:|leanprover--lean4---|')"
sysroot="${ARENA_LEAN_SYSROOT:-$HOME/.elan/toolchains/$tc}"
export4="${ARENA_LEAN4EXPORT:-${ARENA_FC_HOME:-$HOME/.cache/arena-formal-checker}/$tc/bin/lean4export}"
(cd "$repo/formal-core" && PATH="$sysroot/bin:$PATH" lake build ArenaCore >/dev/null)
mapfile -t decls < <(python3 -c 'import json,glob,sys
for f in sorted(glob.glob(sys.argv[1]+"/security/assumptions/*.json")): print(json.load(open(f))["lean_decl"])' "$repo")
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
PATH="$sysroot/bin:$PATH" LEAN_PATH="$repo/formal-core/.lake/build/lib/lean:$sysroot/lib/lean" \
  "$export4" ArenaCore -- "${decls[@]}" > "$tmp"
(cd "$repo" && cargo build -q -p arena-formal-checker --bin decl-hash)
"$repo/target/debug/decl-hash" --export "$tmp" "${decls[@]}" | python3 -c '
import json, glob, sys
h = dict(l.split() for l in sys.stdin if l.strip())
for f in sorted(glob.glob(sys.argv[1] + "/security/assumptions/*.json")):
    d = json.load(open(f))
    d["lean_decl_digest"] = h[d["lean_decl"]]
    open(f, "w").write(json.dumps(d, indent=2, ensure_ascii=False) + "\n")
    print(f, d["lean_decl"], d["lean_decl_digest"])' "$repo"
