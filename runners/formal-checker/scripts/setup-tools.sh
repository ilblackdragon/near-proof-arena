#!/usr/bin/env bash
# Install the pinned Lean toolchain and build the formal checker's helper tools.
# Idempotent. Output layout: $ARENA_FC_HOME/<toolchain-dir>/bin/{lean4export,nanoda_bin,arena-audit}
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLCHAIN="$(tr -d '[:space:]' < "$HERE/lean-toolchain")"
TCDIR="$(echo "$TOOLCHAIN" | sed -e 's#/#--#g' -e 's#:#---#g')"
FC_HOME="${ARENA_FC_HOME:-$HOME/.cache/arena-formal-checker}"
OUT="$FC_HOME/$TCDIR"
SRC="$FC_HOME/src"
mkdir -p "$OUT/bin" "$SRC"

toml_get() { # section key
  awk -v s="[$1]" -v k="$2" '$0==s{f=1;next} /^\[/{f=0} f && $1==k {gsub(/"/,"",$3); print $3}' "$HERE/tools.toml"
}

if ! command -v elan >/dev/null && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
fi
ELAN="$(command -v elan || echo "$HOME/.elan/bin/elan")"
"$ELAN" toolchain install "$TOOLCHAIN" >/dev/null 2>&1 || true
SYSROOT="${ELAN_HOME:-$HOME/.elan}/toolchains/$TCDIR"
test -x "$SYSROOT/bin/lean" || { echo "toolchain $TOOLCHAIN not installed" >&2; exit 1; }
export PATH="$SYSROOT/bin:$PATH"

fetch() { # name repo rev
  local d="$SRC/$1-$3"
  if [ ! -d "$d/.git" ]; then
    git clone -q "$2" "$d"
  fi
  git -C "$d" fetch -q origin "$3" 2>/dev/null || true
  git -C "$d" checkout -q "$3"
  echo "$d"
}

# lean4export: built with *our* toolchain (its own lean-toolchain is overridden).
D="$(fetch lean4export "$(toml_get lean4export repo)" "$(toml_get lean4export rev)")"
echo "$TOOLCHAIN" > "$D/lean-toolchain"
(cd "$D" && lake build lean4export)
install -m 0755 "$D/.lake/build/bin/lean4export" "$OUT/bin/lean4export"

# nanoda (optional independent kernel)
if command -v cargo >/dev/null; then
  D="$(fetch nanoda_lib "$(toml_get nanoda repo)" "$(toml_get nanoda rev)")"
  (cd "$D" && cargo build --release -j "${CARGO_JOBS:-8}" --bin nanoda_bin)
  install -m 0755 "$D/target/release/nanoda_bin" "$OUT/bin/nanoda_bin"
fi

# lean4lean (optional independent kernel), rebuilt against our toolchain.
D="$(fetch lean4lean "$(toml_get lean4lean repo)" "$(toml_get lean4lean rev)")"
echo "$TOOLCHAIN" > "$D/lean-toolchain"
BATT="$(toml_get lean4lean batteries_rev)"
git -C "$D" checkout -q -- lakefile.toml lake-manifest.json 2>/dev/null || true
sed -i -E "/name = \"batteries\"/,/rev =/ s/^rev = .*/rev = \"$BATT\"/" "$D/lakefile.toml"
rm -f "$D/lake-manifest.json"
if (cd "$D" && lake build lean4lean); then
  install -m 0755 "$D/.lake/build/bin/lean4lean" "$OUT/bin/lean4lean"
else
  echo "WARNING: lean4lean failed to build for $TOOLCHAIN; it will be reported as not run" >&2
fi

# arena-audit (judge-owned)
(cd "$HERE/lean/ArenaAudit" && lake build arena-audit)
install -m 0755 "$HERE/lean/ArenaAudit/.lake/build/bin/arena-audit" "$OUT/bin/arena-audit"

echo "tools installed in $OUT/bin (toolchain $TOOLCHAIN)"
