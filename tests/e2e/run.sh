#!/usr/bin/env bash
# End-to-end happy path (`make e2e`): a real arena-server (dev mode, shared
# Postgres, its own database), the signed demo challenge, a real arena-worker
# (bwrap-dev, ARENA_DEV_UNSAFE=1), and the toy reference candidate submitted
# through the `arena` CLI. Asserts the submission reaches DECIDED with every
# required gate produced by real judge work (no fake worker), DEMO tier,
# never ranked.
#
# Options:
#   --keep            leave server/worker running and the database in place
#   --hostile         afterwards run adversarial/e2e/run.sh against the same server
#   --hostile-only C  only run the named hostile case(s) (comma list; implies --hostile)
#
# Env: ARENA_E2E_PG (default postgres://arena:arena@127.0.0.1:55471),
#      ARENA_E2E_DB (default arena_e2e_runners), ARENA_E2E_PORT (default 18471;
#      the worker API uses PORT+1), ARENA_E2E_WORK (default a temp dir).
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
PG="${ARENA_E2E_PG:-postgres://arena:arena@127.0.0.1:55471}"
DB="${ARENA_E2E_DB:-arena_e2e_runners}"
PORT="${ARENA_E2E_PORT:-18471}"
WPORT=$((PORT + 1))
WORK="${ARENA_E2E_WORK:-$(mktemp -d "${TMPDIR:-/tmp}/arena-e2e.XXXXXX")}"
mkdir -p "$WORK"
CHALLENGE=chl_54c65fe7c73c5abcfe500681889177bc
KEEP=0
HOSTILE=0
HOSTILE_ONLY=""
while [ $# -gt 0 ]; do
  case "$1" in
    --keep) KEEP=1 ;;
    --hostile) HOSTILE=1 ;;
    --hostile-only) HOSTILE=1; HOSTILE_ONLY="$2"; shift ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
  shift
done

say() { printf '\n== %s\n' "$*"; }
die() { echo "E2E FAIL: $*" >&2; exit 1; }

export RUSTC_WRAPPER="${RUSTC_WRAPPER:-sccache}"
say "build (arena-server, arena-worker, arena CLI)"
( cd "$REPO" && cargo build -q -j 8 -p arena-server -p arena-worker -p arena-cli )
BIN="$REPO/target/debug"

# Admin SQL on the shared server: local psql if present, else the psql inside
# the dev Postgres container (ARENA_E2E_PG_CONTAINER, default arena-pg).
pg_admin() {
  if command -v psql >/dev/null 2>&1; then
    psql "$PG/postgres" -v ON_ERROR_STOP=1 -q "$@"
  else
    docker exec -i "${ARENA_E2E_PG_CONTAINER:-arena-pg}" psql -U arena -d postgres -v ON_ERROR_STOP=1 -q "$@"
  fi
}
case "$DB" in arena_e2e_*) ;; *) die "refusing to manage database $DB (must start with arena_e2e_)";; esac
say "database $DB (dropped and recreated; never touches other databases)"
pg_admin -c "DROP DATABASE IF EXISTS $DB WITH (FORCE)" -c "CREATE DATABASE $DB" >/dev/null
DBURL="$PG/$DB"
"$BIN/arena-server" migrate --database-url "$DBURL" >"$WORK/migrate.log" 2>&1 || { cat "$WORK/migrate.log"; die "migrate"; }

PIDS=()
cleanup() {
  for p in "${PIDS[@]:-}"; do [ -n "$p" ] && kill "$p" 2>/dev/null || true; done
  wait 2>/dev/null || true
  if [ "$KEEP" = 0 ]; then
    pg_admin -c "DROP DATABASE IF EXISTS $DB WITH (FORCE)" >/dev/null 2>&1 || true
  else
    echo "kept: work dir $WORK, database $DB"
  fi
}
trap cleanup EXIT

AGENT_TOKEN="e2e-agent-$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \n')"
WORKER_TOKEN="e2e-worker-$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \n')"

say "arena-server on 127.0.0.1:$PORT (worker API :$WPORT)"
mkdir -p "$WORK/objects"
env ARENA_DATABASE_URL="$DBURL" \
  ARENA_BIND_ADDR="127.0.0.1:$PORT" ARENA_WORKER_API_BIND_ADDR="127.0.0.1:$WPORT" \
  ARENA_ADMIN_TOKEN="e2e-admin" ARENA_BOOTSTRAP_AGENT_TOKEN="$AGENT_TOKEN" ARENA_WORKER_TOKEN="$WORKER_TOKEN" \
  ARENA_BOOTSTRAP_WORKER_SANDBOX=bwrap-dev \
  ARENA_LEASE_SECS=120 ARENA_RETRY_BACKOFF_SECS=1 ARENA_QUOTA_SUBMISSIONS_PER_DAY=500 ARENA_RATE_LIMIT_PER_MINUTE=600 \
  "$BIN/arena-server" serve --dev --object-store-dir "$WORK/objects" \
    --challenges-dir "$REPO/challenges" \
    --governance-pubkey-file "$REPO/challenges/governance-dev.pub" \
    --security-dir "$REPO/security" \
  >"$WORK/server.log" 2>&1 &
PIDS+=($!)
for _ in $(seq 1 100); do
  curl -sf "http://127.0.0.1:$PORT/healthz" >/dev/null 2>&1 && break
  sleep 0.2
done
curl -sf "http://127.0.0.1:$PORT/healthz" >/dev/null || { tail -50 "$WORK/server.log"; die "server did not come up"; }
curl -sf "http://127.0.0.1:$PORT/v1/challenges/$CHALLENGE" | python3 -c '
import json,sys; c=json.load(sys.stdin); assert c["tier"]=="demo", c["tier"]; print("challenge registered:", c["id"], "tier", c["tier"])' \
  || { tail -50 "$WORK/server.log"; die "demo challenge not registered"; }

say "arena-worker (bwrap-dev, DEMO-only isolation)"
env -i PATH="$PATH" HOME="$HOME" XDG_RUNTIME_DIR="${XDG_RUNTIME_DIR:-}" DBUS_SESSION_BUS_ADDRESS="${DBUS_SESSION_BUS_ADDRESS:-}" \
  ARENA_DEV_UNSAFE=1 \
  ARENA_SERVER_URL="http://127.0.0.1:$WPORT" ARENA_WORKER_TOKEN="$WORKER_TOKEN" \
  ARENA_WORKER_ID=e2e-worker ARENA_WORK_DIR="$WORK/worker" ARENA_SANDBOX_BACKEND=bwrap-dev \
  ARENA_FIXTURES_DIRS="$REPO/challenges/demo/toy-arithmetic/fixtures" \
  ARENA_DEV_BENCH_BATCH_CAP="${ARENA_DEV_BENCH_BATCH_CAP:-4}" \
  ARENA_POLL_MS=200 ARENA_HEARTBEAT_MS=5000 \
  "$BIN/arena-worker" >"$WORK/worker.log" 2>&1 &
PIDS+=($!)

export ARENA_URL="http://127.0.0.1:$PORT" ARENA_TOKEN="$AGENT_TOKEN"
say "submit the toy reference candidate via the arena CLI"
"$BIN/arena" submit "$REPO/tests/e2e/toy-candidate" --challenge "$CHALLENGE" --json >"$WORK/submit.json" \
  || { cat "$WORK/submit.json"; die "arena submit"; }
SUB=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["id"])' "$WORK/submit.json")
echo "submission $SUB"

DEADLINE=$(( $(date +%s) + ${ARENA_E2E_TIMEOUT:-900} ))
while :; do
  "$BIN/arena" status "$SUB" --json >"$WORK/status.json" 2>/dev/null || true
  STAGE=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("stage",""))' "$WORK/status.json" 2>/dev/null || echo "?")
  [ "$STAGE" = DECIDED ] && break
  [ "$(date +%s)" -gt "$DEADLINE" ] && { tail -40 "$WORK/worker.log"; die "timed out at stage $STAGE"; }
  sleep 2
done
"$BIN/arena" leaderboard --challenge "$CHALLENGE" --json >"$WORK/leaderboard.json"
"$BIN/arena" report "$SUB" -o "$WORK/report.json" >/dev/null 2>&1 || true

say "assertions"
python3 - "$WORK/status.json" "$WORK/leaderboard.json" "$REPO/challenges/$CHALLENGE.json" <<'EOF'
import json, sys
view = json.load(open(sys.argv[1]))
board = json.load(open(sys.argv[2]))
chal = json.load(open(sys.argv[3]))
fails = []
def check(cond, msg):
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond: fails.append(msg)
gates = {g["gate"]: g for g in view["gates"]}
print(f"decision={view['decision']} accepted={view['accepted']} tier={view['tier']} score={view['score_milli']}")
for g in view["gates"]:
    print(f"  {g['gate']:28} {g['status']:8} {','.join(g['reason_codes']):30} {g['summary'][:110]!r}")
check(view["stage"] == "DECIDED", "stage DECIDED")
check(view["tier"] == "demo", "run tier is demo")
for o in chal["required_obligations"]:
    g = gates.get(o)
    check(g is not None and g["status"] == "PASS", f"required gate {o} PASS")
    if g:
        check("DEMO_ONLY" in g["reason_codes"], f"{o} carries DEMO_ONLY")
        check("simulated" not in g["summary"].lower() and "fake" not in g["summary"].lower(), f"{o} produced by real judge work")
check("[bwrap-dev (DEMO-only)]" in gates["BUILD_REPRODUCIBLE"]["summary"], "build ran in the bwrap-dev sandbox")
check("cases conform" in gates["CONFORMANCE_DIFFERENTIAL"]["summary"], "conformance ran oracle cases")
check(" 0 accepted" in gates["ADVERSARIAL_PROOFS"]["summary"], "no hostile proof accepted")
check(view.get("benchmark") is not None and len(view["benchmark"]["classes"]) == len(chal["workload_suite"]["classes"]), "benchmark measured every class")
check(view["decision"] in ("ADMITTED", "INCONCLUSIVE"), "decision is ADMITTED (demo) or INCONCLUSIVE")
mine = [e for e in board if e["submission_id"] == view["id"]]
check(len(mine) == 1 and mine[0]["rank"] is None, "listed on the leaderboard with rank null (demo is never ranked)")
check(all(e["rank"] is None for e in board), "nothing ranked on a demo challenge")
sys.exit(1 if fails else 0)
EOF
echo
echo "E2E OK: $SUB decided; server log $WORK/server.log, worker log $WORK/worker.log"

if [ "$HOSTILE" = 1 ]; then
  say "adversarial live suite against the same server"
  ARGS=(--server "$ARENA_URL" --token "$AGENT_TOKEN" --challenge "$CHALLENGE" --timeout "${ARENA_HOSTILE_TIMEOUT:-600}" --report "$WORK/hostile.json")
  [ -n "$HOSTILE_ONLY" ] && ARGS+=(--only "$HOSTILE_ONLY")
  "$REPO/adversarial/e2e/run.sh" "${ARGS[@]}" | tee "$WORK/hostile.log"
fi
