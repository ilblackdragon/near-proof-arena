#!/bin/sh
# Emit a MALICIOUS tar to stdout for this case. The e2e driver uploads these
# bytes directly (not a tar of the directory). Requires GNU tar features for
# some kinds; documented per case. No network.
set -eu
KIND="${1:-$(cat "$(dirname "$0")/archive-kind")}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/pkg/source" "$TMP/pkg/formal" "$TMP/pkg/build-recipe"
cat > "$TMP/pkg/candidate.toml" <<'EOF'
schema = "arena-candidate-v1"
name = "archive-attack"
agent = "adversarial-suite"
challenge = "CHALLENGE_PLACEHOLDER"
backend_family = "archive"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 4 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out/verify"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
EOF
echo '#!/bin/sh' > "$TMP/pkg/build-recipe/build.sh"
echo 'int main(void){return 0;}' > "$TMP/pkg/source/verify.c"
echo 'theorem Candidate.certificate : True := trivial' > "$TMP/pkg/formal/Candidate.lean"

case "$KIND" in
  zipslip)
    # entry with a traversal path
    ( cd "$TMP/pkg" && tar -cf - . ) > "$TMP/base.tar"
    # append an evil member with a ../ path
    echo evil > "$TMP/evil"
    tar -rf "$TMP/base.tar" --transform='s,.*,../../../../tmp/zipslip-escape,' "$TMP/evil" 2>/dev/null \
      || tar -rf "$TMP/base.tar" -C "$TMP" --xform='s,evil,../../../../tmp/zipslip-escape,' evil
    cat "$TMP/base.tar" ;;
  symlink)
    ln -s /etc/passwd "$TMP/pkg/source/leak"
    ( cd "$TMP" && tar -cf - pkg ) ;;
  hardlink)
    : > "$TMP/outside"; ln "$TMP/outside" "$TMP/pkg/source/hard" 2>/dev/null || true
    ( cd "$TMP" && tar -cf - --hard-dereference=0 pkg ../outside 2>/dev/null || tar -cf - pkg ) ;;
  device)
    # include a device node reference (needs tar; node creation may need root,
    # so synthesize via tar's --mtime trick is not possible; try mknod in TMP)
    mknod "$TMP/pkg/source/dev0" c 1 3 2>/dev/null || true
    ( cd "$TMP" && tar -cf - pkg ) ;;
  bomb)
    # 1 GiB of zeros in one entry; compresses tiny, expands past the cap
    dd if=/dev/zero of="$TMP/pkg/source/zeros" bs=1M count=1024 2>/dev/null
    ( cd "$TMP" && tar -cf - pkg | zstd -19 ) ;;
  *) echo "unknown kind $KIND" >&2; exit 2 ;;
esac
