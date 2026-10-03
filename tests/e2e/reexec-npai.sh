#!/usr/bin/env bash
# End to end for the approved-interpreter route (verify_route = "npai-v1"):
# submit examples/reexec-npai to the real server + Firecracker worker against
# the signed NEAR challenge and expect
#
#   * ADMITTED at formal tier, every gate PASS (no DEMO_ONLY);
#   * the verifier executed by the worker is the judge's npai-verify on the
#     build's out/verifier.npai, whose digest the statement pins;
#   * evidence edge artifact:verifier_bytecode -implements-> statement CHECKED
#     (FORMAL_IMPL_CONNECTION on route (a)), not trusted.
#
# Same infrastructure as tests/e2e/milestone-d.sh (shared Postgres, docker +
# KVM, toolchain and lean-checker images, near-arena-oracle). Results go to
# docs/e2e-results/reexec-npai/ (override with ARENA_E2E_RESULTS).
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
PG="${ARENA_E2E_PG:-postgres://arena:arena@127.0.0.1:55471}"
DB="${ARENA_E2E_DB:-arena_e2e_reexec_npai}"
PORT="${ARENA_E2E_PORT:-18591}"
WPORT=$((PORT + 1))
WORK="${ARENA_E2E_WORK:-$(mktemp -d "${TMPDIR:-/tmp}/arena-e2e-npai.XXXXXX")}"
RESULTS="${ARENA_E2E_RESULTS:-$REPO/docs/e2e-results/reexec-npai}"
NEAR="${ARENA_E2E_NEAR:-chl_3be93793610370275ae40f36a475f01f}"
TC_IMAGES="${ARENA_TOOLCHAIN_IMAGES:-/data/illia/nearproof-deps/toolchain-images}"
LEAN_IMAGES="${LEAN_CHECKER_IMAGES:-/data/illia/nearproof-deps/lean-checker/images}"
FC_DEPS="${ARENA_FC_DEPS:-/data/illia/nearproof-deps/firecracker-rc}"
ORACLE="${ARENA_NEAR_ORACLE:-$REPO/oracle/target/debug/near-arena-oracle}"
TIMEOUT="${ARENA_E2E_TIMEOUT:-5400}"
mkdir -p "$WORK" "$RESULTS"

say() { printf '\n== %s\n' "$*"; }
die() { echo "E2E FAIL: $*" >&2; exit 1; }
case "$DB" in arena_e2e_*) ;; *) die "refusing to manage database $DB";; esac
pg_admin() {
  if command -v psql >/dev/null 2>&1; then psql "$PG/postgres" -v ON_ERROR_STOP=1 -q "$@"
  else docker exec -i "${ARENA_E2E_PG_CONTAINER:-arena-pg}" psql -U arena -d postgres -v ON_ERROR_STOP=1 -q "$@"; fi
}
newest() { ls -t "$1"/*.json | head -1 | xargs basename | sed 's/\.json$//'; }

export RUSTC_WRAPPER="${RUSTC_WRAPPER:-sccache}"
say "build"
( cd "$REPO" && cargo build -q -j 8 -p arena-server -p arena-worker -p arena-cli -p arena-formal-checker )
# The judge's interpreter runs inside the microVM: a static (musl) build, as
# deployed (deploy/hardened/env/worker.env.example).
( cd "$REPO" && cargo build -q --release -p arena-npai --bin npai-verify --target x86_64-unknown-linux-musl )
NPAI_VERIFY="${ARENA_NPAI_VERIFY:-$REPO/target/x86_64-unknown-linux-musl/release/npai-verify}"
BIN="$REPO/target/debug"
[ -x "$ORACLE" ] || die "no near-arena-oracle at $ORACLE"
[ -x "$NPAI_VERIFY" ] || die "no npai-verify at $NPAI_VERIFY"

say "NEAR challenge $NEAR: checker identity of the production lean-checker image"
LEAN_IMG="$LEAN_IMAGES/$(newest "$LEAN_IMAGES")"
IDENT=$(env ARENA_LEAN_SYSROOT="$LEAN_IMG/arena/tc" ARENA_LEAN4EXPORT="$LEAN_IMG/arena/tools/lean4export" \
  ARENA_NANODA="$LEAN_IMG/arena/tools/nanoda_bin" ARENA_LEAN4LEAN="$LEAN_IMG/arena/tools/lean4lean" \
  ARENA_AUDIT_BIN="$LEAN_IMG/arena/tools/arena-audit" "$BIN/formal-check" --print-image-digest)
PINNED=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["toolchain_policy"]["checker_image"])' "$REPO/challenges/$NEAR.json")
echo "lean-checker image $(basename "$LEAN_IMG"), identity $IDENT; $NEAR pins $PINNED"
[ "$PINNED" = "$IDENT" ] || die "the signed $NEAR pins a different checker image (no local successor in this script)"
CH="$WORK/challenges"
rm -rf "$CH"; mkdir -p "$CH"
cp "$REPO/challenges/"*.json "$REPO/challenges/"*.sig "$REPO/challenges/"*.pub "$CH/"

say "database $DB"
pg_admin -c "DROP DATABASE IF EXISTS $DB WITH (FORCE)" -c "CREATE DATABASE $DB" >/dev/null
DBURL="$PG/$DB"
"$BIN/arena-server" migrate --database-url "$DBURL" >"$WORK/migrate.log" 2>&1 || { cat "$WORK/migrate.log"; die migrate; }

PIDS=()
cleanup() {
  for p in "${PIDS[@]:-}"; do [ -n "$p" ] && kill "$p" 2>/dev/null || true; done
  wait 2>/dev/null || true
  [ "${KEEP:-0}" = 1 ] || pg_admin -c "DROP DATABASE IF EXISTS $DB WITH (FORCE)" >/dev/null 2>&1 || true
}
trap cleanup EXIT

AGENT_TOKEN="e2e-agent-$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \n')"
say "arena-server on 127.0.0.1:$PORT"
mkdir -p "$WORK/objects"
env ARENA_DATABASE_URL="$DBURL" ARENA_BIND_ADDR="127.0.0.1:$PORT" ARENA_WORKER_API_BIND_ADDR="127.0.0.1:$WPORT" \
  ARENA_ADMIN_TOKEN=e2e-admin ARENA_BOOTSTRAP_AGENT_TOKEN="$AGENT_TOKEN" \
  ARENA_LEASE_SECS=900 ARENA_RETRY_BACKOFF_SECS=1 ARENA_QUOTA_SUBMISSIONS_PER_DAY=50 ARENA_QUOTA_ACTIVE_RUNS=4 \
  ARENA_RATE_LIMIT_PER_MINUTE=600 \
  "$BIN/arena-server" serve --dev --object-store-dir "$WORK/objects" --challenges-dir "$CH" \
    --governance-pubkey-file "$REPO/challenges/governance-dev.pub,$REPO/challenges/governance-local.pub" \
    --security-dir "$REPO/security" >"$WORK/server.log" 2>&1 &
PIDS+=($!)
for _ in $(seq 1 100); do curl -sf "http://127.0.0.1:$PORT/healthz" >/dev/null 2>&1 && break; sleep 0.2; done
curl -sf "http://127.0.0.1:$PORT/v1/challenges/$NEAR" >/dev/null || { tail -40 "$WORK/server.log"; die "challenge not registered"; }

say "Firecracker worker (tier cap formal)"
FC_TOKEN=$("$BIN/arena-server" create-worker --database-url "$DBURL" --name e2e-fc --sandbox firecracker --tier-cap formal | sed -n 's/^token //p')
CLEAN="$WORK/clean"
rm -rf "$CLEAN"; mkdir -p "$CLEAN"
( cd "$REPO" && git ls-files -- formal-core spec/lean oracle/fixtures/public | tar -cf - -T - ) | tar -xf - -C "$CLEAN"
TC=$(newest "$TC_IMAGES")
env -i PATH="$PATH" HOME="$HOME" \
  ARENA_SERVER_URL="http://127.0.0.1:$WPORT" ARENA_WORKER_TOKEN="$FC_TOKEN" \
  ARENA_WORKER_ID=e2e-fc-npai ARENA_WORK_DIR="$WORK/fc-worker" ARENA_SANDBOX_BACKEND=firecracker \
  ARENA_FC_DEPS="$FC_DEPS" \
  ARENA_IMAGES_DIR="$TC_IMAGES" ARENA_BUILD_TOOLCHAIN_IMAGE="sha256:$TC" \
  ARENA_BUILD_MOUNTS="$LEAN_IMG/arena/tc:/opt/lean" \
  ARENA_BUILD_PATH="/opt/lean/bin:/usr/local/rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:/usr/local/cargo/bin:/usr/local/bin:/usr/bin:/bin" \
  ARENA_FORMAL_REPO="$CLEAN" ARENA_FORMAL_CONFIGS_DIR="$REPO/runners/formal-checker/challenges" \
  ARENA_LEAN_CHECKER_IMAGES="$LEAN_IMAGES" ARENA_NPAI_VERIFY="$NPAI_VERIFY" \
  ${ARENA_INTERP_REF:+ARENA_INTERP_REF="$ARENA_INTERP_REF"} \
  ARENA_NEAR_ORACLE="$ORACLE" ARENA_WORKLOAD_GENERATORS="$REPO/spec/workloads/near-transfer-receipt-v1" \
  ARENA_FIXTURES_DIRS="$CLEAN/oracle/fixtures/public" ARENA_CONFORMANCE_SAMPLES=3 \
  ARENA_LEASE_SECONDS=900 ARENA_POLL_MS=500 ARENA_HEARTBEAT_MS=10000 \
  "$BIN/arena-worker" >"$WORK/fc-worker.log" 2>&1 &
PIDS+=($!)

export ARENA_URL="http://127.0.0.1:$PORT" ARENA_TOKEN="$AGENT_TOKEN"
say "submit examples/reexec-npai"
D="$WORK/cand-reexec-npai"; rm -rf "$D"; mkdir -p "$D"
( cd "$REPO/examples/reexec-npai" && git ls-files | tar -cf - -T - ) | tar -xf - -C "$D"
sed -i "s/^challenge = .*/challenge = \"$NEAR\"/" "$D/candidate.toml"
"$BIN/arena" submit "$D" --challenge "$NEAR" --json >"$WORK/submit.json" || { cat "$WORK/submit.json"; die submit; }
SUB=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["id"])' "$WORK/submit.json")
echo "submission $SUB"
deadline=$(( $(date +%s) + TIMEOUT ))
while :; do
  "$BIN/arena" status "$SUB" --json >"$RESULTS/reexec-npai.submission.json" 2>/dev/null || true
  stage=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("stage",""))' "$RESULTS/reexec-npai.submission.json" 2>/dev/null || echo "?")
  [ "$stage" = DECIDED ] && break
  [ "$(date +%s)" -gt "$deadline" ] && { tail -30 "$WORK/fc-worker.log"; die "timed out at stage $stage"; }
  sleep 10
done
"$BIN/arena" report "$SUB" -o "$RESULTS/reexec-npai.report.json" >/dev/null 2>&1 || true
grep -E "npai|verifier.npai|FORMAL" "$WORK/fc-worker.log" | tail -40 >"$RESULTS/worker-excerpt.log" || true

say "assertions + summary"
python3 - "$RESULTS" "$NEAR" "$SUB" "$IDENT" "$(basename "$LEAN_IMG")" "$TC" "$FC_DEPS" "$REPO" <<'EOF'
import json, sys, os, datetime, hashlib
res, chal, sub, ident, leanimg, tc, fcdeps, repo = sys.argv[1:9]
V = json.load(open(os.path.join(res, "reexec-npai.submission.json")))
rep = os.path.join(res, "reexec-npai.report.json")
Rp = json.load(open(rep)) if os.path.exists(rep) else {}
fails, lines = [], []
def check(c, m):
    lines.append(("- [x] " if c else "- [ ] **FAIL** ") + m)
    print(("ok   " if c else "FAIL ") + m)
    if not c: fails.append(m)
def find_graph(o):
    if isinstance(o, dict):
        if "edges" in o and "nodes" in o: return o
        for v in o.values():
            g = find_graph(v)
            if g: return g
    if isinstance(o, list):
        for v in o:
            g = find_graph(v)
            if g: return g
    return None
G = find_graph(V) or find_graph(Rp) or {"nodes": [], "edges": []}
gates = {g["gate"]: g for g in V["gates"]}
check(V["decision"] == "ADMITTED" and V["accepted"] is True, f"ADMITTED (accepted) [decision {V['decision']}]")
check(V["tier"] == "formal", "evaluated at formal tier (Firecracker)")
check(all(g["status"] in ("PASS", "NOT_APPLICABLE") for g in V["gates"]), "every gate PASS")
check(all("DEMO_ONLY" not in g["reason_codes"] for g in V["gates"]), "no DEMO_ONLY")
for g in ("ARTIFACT_BINDING", "FORMAL_SEMANTIC_SOUNDNESS", "FORMAL_SEMANTIC_COMPLETENESS",
          "FORMAL_CRYPTO_SOUNDNESS", "FORMAL_IMPL_CONNECTION", "AXIOM_AUDIT"):
    check(gates.get(g, {}).get("status") == "PASS", f"{g} PASS")
img = hashlib.sha256(open(os.path.join(repo, "examples/reexec-npai/out/verifier.npai"), "rb").read()).hexdigest()
ab = gates.get("ARTIFACT_BINDING", {}).get("summary", "")
check(img in ab, f"ARTIFACT_BINDING pins the npai-v1 bytecode sha256 {img}")
impl = [e for e in G["edges"] if e["from"] == "artifact:verifier_bytecode" and e["kind"] == "implements"]
check(len(impl) == 1 and impl[0]["status"] == "checked", "evidence edge artifact:verifier_bytecode -implements-> statement is CHECKED (not trusted)")
node = [n for n in G["nodes"] if n["id"] == "artifact:verifier_bytecode"]
check(bool(node) and node[0].get("digest") == "sha256:" + img, "bytecode node digest = sha256(out/verifier.npai)")
check(not any(e["kind"] == "implements" and e["status"] == "trusted" for e in G["edges"]), "no trusted implements edge (no compiler in the connection)")
md = ["# reexec-npai e2e — approved-interpreter route (npai-v1), Firecracker", "",
      f"Run: {datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')} on the shared dev host. Generated by `tests/e2e/reexec-npai.sh`.", "",
      "## Setup", "",
      f"* challenge: the signed `{chal}` (near-transfer-receipt-v1-2); checker identity `{ident}` = lean-checker image `sha256:{leanimg}`.",
      f"* worker: `arena-worker`, backend `firecracker` (tier cap formal, deps `{fcdeps}`), build in toolchain image `sha256:{tc}`; verify = judge `npai-verify` on the built `out/verifier.npai` (fuel = `formal_params.verify_fuel`).",
      f"* candidate: `examples/reexec-npai` (verify_route `npai-v1`, certificate `ReexecNpai.certificate`), bytecode sha256 `{img}`.", "",
      "## Checks", ""] + lines + ["", f"## Submission `{V['id']}`", "",
      f"decision **{V['decision']}**, accepted {V['accepted']}, tier `{V['tier']}`, score {V.get('score_milli')}", "",
      "| gate | status | reasons | summary |", "|---|---|---|---|"]
for g in V["gates"]:
    s = g["summary"].replace("|", "\\|").replace("\n", " ")[:220]
    md.append(f"| {g['gate']} | {g['status']} | {', '.join(g['reason_codes'])} | {s} |")
md += ["", "## Evidence edges", "", "| from | kind | to | status |", "|---|---|---|---|"]
for e in G["edges"]:
    md.append(f"| {e['from']} | {e['kind']} | {e['to']} | {e['status']} |")
md += ["", "Raw: `reexec-npai.submission.json` (API view), `reexec-npai.report.json` (signed report), `worker-excerpt.log`.", ""]
open(os.path.join(res, "README.md"), "w").write("\n".join(md))
print(f"\n{len(lines) - len(fails)}/{len(lines)} checks passed; results in {res}")
sys.exit(1 if fails else 0)
EOF
