#!/usr/bin/env bash
# The SP1 zkVM candidate (examples/zkvm-sp1) through the real arena pipeline:
# arena CLI -> arena-server -> arena-worker (Firecracker, production
# isolation) -> gates -> decision -> signed report -> leaderboard.
#
# Challenges (all registered on one server; local ones signed with the LOCAL
# operator key challenges/governance-local.pub, private half in
# /data/illia/nearproof-deps/keys; they live in the results dir, never in
# challenges/):
#
#   A1  chl_5ef2bc7d2068219635426e47ca46bfbb — the signed formal NEAR challenge, as is.
#   A2  e2e-local successor of A1, identical except toolchain_policy.checker_image
#       re-pinned to the production lean-checker image's identity (exactly what
#       tests/e2e/milestone-d.sh does), so FORMAL_CHECK actually runs.
#   B   EXPERIMENTAL tier, same semantics / spec / claim encoding / workload
#       generators / fixtures / security profile / formal params as A2, with
#       resource limits sized for SP1 (48 GiB RAM, 600 s prove per request)
#       and a smaller measurement procedure (batch 1, cold 1, warmup 1,
#       measured 3). Required obligations: arena-admin's experimental minimum
#       + BENCHMARK (ARTIFACT_BINDING is in that minimum).
#   M   DEMO tier "measurement-only": identical to B except tier = demo and the
#       FORMAL_CHECK-owned gates (incl. ARTIFACT_BINDING) are not required.
#       Exists because B, by policy, requires ARTIFACT_BINDING, which no
#       candidate-built native verifier (SP1) can pass, so SP1 is decided at
#       FORMAL_CHECK (fail-fast) and never measured on B. Demo is never ranked.
#
# Submissions: SP1 -> A1, A2, B, M; examples/reexec-witness -> B. (reexec is
# not submitted to M: its native-lean verifier is built by FORMAL_CHECK, which
# M does not run, so its runtime gates would have no verifier.)
#
# Env: ARENA_SP1_PG (default postgres://arena:arena@127.0.0.1:55471),
#      ARENA_SP1_DB (default arena_sp1), ARENA_SP1_PORT (default 18581; worker
#      API PORT+1), ARENA_SP1_WORK (default /data/illia/nearproof-deps/sp1-pipeline/work),
#      ARENA_SP1_RESULTS (default docs/e2e-results/sp1-pipeline),
#      ARENA_SP1_CPUS (default 8-15: host CPUs for every candidate VM),
#      ARENA_SP1_MODE=head (no local challenges; SP1 to every signed NEAR challenge,
#      superseded ones expected to refuse), ARENA_SP1_ONLY (comma list of submission labels to run; default all),
#      ARENA_SP1_TOOLCHAIN_IMAGE (default: the SP1 image from deploy/images/toolchain-sp1).
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
PG="${ARENA_SP1_PG:-postgres://arena:arena@127.0.0.1:55471}"
DB="${ARENA_SP1_DB:-arena_sp1}"
PORT="${ARENA_SP1_PORT:-18581}"
WPORT=$((PORT + 1))
WORK="${ARENA_SP1_WORK:-/data/illia/nearproof-deps/sp1-pipeline/work}"
RESULTS="${ARENA_SP1_RESULTS:-$REPO/docs/e2e-results/sp1-pipeline/run}"
CPUS="${ARENA_SP1_CPUS:-8-15}"
ONLY="${ARENA_SP1_ONLY:-}"
MODE="${ARENA_SP1_MODE:-full}"   # full | head (only the signed challenges/; SP1 to every NEAR one)
NEAR=chl_5ef2bc7d2068219635426e47ca46bfbb
GOV_KEY="${ARENA_GOV_LOCAL_KEY:-/data/illia/nearproof-deps/keys/governance-local.key}"
GOV_PUB="$REPO/challenges/governance-local.pub"
TC_IMAGES="${ARENA_TOOLCHAIN_IMAGES:-/data/illia/nearproof-deps/toolchain-images}"
TC="${ARENA_SP1_TOOLCHAIN_IMAGE:-70d2b28003f8117601772dedb7f42393e928ccfcca7356a49d675ec3f878a8a1}"
LEAN_IMAGES="${LEAN_CHECKER_IMAGES:-/data/illia/nearproof-deps/lean-checker/images}"
ORACLE="${ARENA_NEAR_ORACLE:-$REPO/oracle/target/debug/near-arena-oracle}"
TIMEOUT="${ARENA_SP1_TIMEOUT:-21600}"
mkdir -p "$WORK" "$RESULTS/challenges"

say() { printf '\n== %s  [%s] load: %s\n' "$*" "$(date -u +%H:%M:%S)" "$(cut -d' ' -f1-3 /proc/loadavg)"; }
die() { echo "SP1 E2E FAIL: $*" >&2; exit 1; }
pg_admin() {
  if command -v psql >/dev/null 2>&1; then psql "$PG/postgres" -v ON_ERROR_STOP=1 -q "$@"
  else docker exec -i "${ARENA_E2E_PG_CONTAINER:-arena-pg}" psql -U arena -d postgres -v ON_ERROR_STOP=1 -q "$@"; fi
}
newest() { ls -t "$1"/*.json | head -1 | xargs basename | sed 's/\.json$//'; }
want() { [ -z "$ONLY" ] || [[ ",$ONLY," == *",$1,"* ]]; }

export RUSTC_WRAPPER="${RUSTC_WRAPPER:-sccache}"
say "build"
( cd "$REPO" && cargo build -q -j 8 -p arena-server -p arena-worker -p arena-cli -p arena-admin -p arena-formal-checker )
BIN="$REPO/target/debug"
[ -x "$ORACLE" ] || die "no near-arena-oracle at $ORACLE"
[ -d "$TC_IMAGES/$TC" ] || die "toolchain image $TC not installed (deploy/images/toolchain-sp1/build.sh)"
for v in vendor vendor-guest; do
  [ -d "$REPO/examples/zkvm-sp1/source/$v" ] || die "examples/zkvm-sp1/source/$v missing: run examples/zkvm-sp1/build-recipe/vendor.sh"
done

say "challenges"
LEAN_IMG="$LEAN_IMAGES/$(newest "$LEAN_IMAGES")"
IDENT=$(env ARENA_LEAN_SYSROOT="$LEAN_IMG/arena/tc" ARENA_LEAN4EXPORT="$LEAN_IMG/arena/tools/lean4export" \
  ARENA_NANODA="$LEAN_IMG/arena/tools/nanoda_bin" ARENA_LEAN4LEAN="$LEAN_IMG/arena/tools/lean4lean" \
  ARENA_AUDIT_BIN="$LEAN_IMG/arena/tools/arena-audit" "$BIN/formal-check" --print-image-digest)
echo "lean-checker image $(basename "$LEAN_IMG"), checker identity $IDENT"
CH="$WORK/challenges"
rm -rf "$CH"; mkdir -p "$CH"
cp "$REPO/challenges/"*.json "$REPO/challenges/"*.sig "$REPO/challenges/"*.pub "$CH/"
A2= B= M=
CHALS=()
for f in "$CH"/chl_*.json; do CHALS+=("$(basename "$f" .json)"); done
if [ "$MODE" = head ]; then
  # Only the signed challenges in challenges/ (no local re-pins / twins).
  "$BIN/arena-admin" verify --pubkey "$GOV_PUB" --pubkey "$REPO/challenges/governance-dev.pub" \
    --security-dir "$REPO/security" --all-in "$CH" | tee "$RESULTS/challenges/verify.txt"
  printf '%s\n' "${CHALS[@]}" > "$RESULTS/challenges/ids.txt"
else
python3 - "$REPO/challenges/$NEAR.json" "$IDENT" "$WORK" <<'EOF'
import json, sys, copy, datetime
src, ident, work = sys.argv[1:]
base = json.load(open(src))
t0 = datetime.datetime.fromisoformat(base["created_at"].replace("Z", "+00:00"))
ts = lambda s: (t0 + datetime.timedelta(seconds=s)).strftime("%Y-%m-%dT%H:%M:%SZ")

# A2: the milestone-d re-pin (identical except checker_image; supersedes A1).
a2 = copy.deepcopy(base)
a2["toolchain_policy"]["checker_image"] = ident
a2["season"] = base["season"] + "-e2e-local"
a2["supersedes"] = None
a2["created_at"] = ts(1)
json.dump(a2, open(f"{work}/a2.draft.json", "w"), indent=2)

# B: EXPERIMENTAL, sized for SP1. Semantics, spec, claim encoding, workload
# generators, fixtures, held-out commitment, security profile and
# formal_params are unchanged; formal_params.max_proof_bytes stays 8 MiB
# because the reference certificate's statement is instantiated with it.
b = copy.deepcopy(a2)
b["tier"] = "experimental"
b["season"] = base["season"] + "-EXPERIMENTAL-sp1-measurement"
b["required_obligations"] = ["PKG_WELLFORMED", "BUILD_REPRODUCIBLE", "ARTIFACT_BINDING",
    "CONFORMANCE_DIFFERENTIAL", "ADVERSARIAL_PROOFS", "PROVER_RELIABILITY", "RESOURCE_LIMITS", "BENCHMARK"]
b["hardware_profile"] = {
    "id": "nearproof-local-ryzen9-9950x3d-fc8-48g",
    "cpu_model": "AMD Ryzen 9 9950X3D 16-Core Processor (local operator host, shared; Firecracker microVM with 8 vCPUs pinned to host CPUs 8-15 per candidate run)",
    "vcpus": 8, "ram_bytes": 48 << 30, "gpu": None}
b["resource_limits"]["max_ram_bytes"] = 48 << 30
b["resource_limits"]["max_prove_ms"] = 600000
b["measurement"] = {"warmup_runs": 1, "measured_runs": 3, "aggregation": "median", "outlier_mad_k": 5,
                    "cold_runs": 1, "concurrency": 1, "per_run_timeout_ms": 600000}
for c in b["workload_suite"]["classes"]:
    c["batch_size"] = 1
b["created_at"] = ts(2)
json.dump(b, open(f"{work}/b.draft.json", "w"), indent=2)

# M: DEMO measurement-only twin of B (no FORMAL_CHECK-owned gate required).
m = copy.deepcopy(b)
m["tier"] = "demo"
m["season"] = base["season"] + "-DEMO-sp1-measurement-only"
m["required_obligations"] = ["PKG_WELLFORMED", "BUILD_REPRODUCIBLE",
    "CONFORMANCE_DIFFERENTIAL", "ADVERSARIAL_PROOFS", "PROVER_RELIABILITY", "RESOURCE_LIMITS", "BENCHMARK"]
m["created_at"] = ts(3)
json.dump(m, open(f"{work}/m.draft.json", "w"), indent=2)
EOF
sign_new() { # draft -> prints new id
  local before; before=$(ls "$CH" | sort)
  "$BIN/arena-admin" "$@" --key "$GOV_KEY" --challenges-dir "$CH" --security-dir "$REPO/security" >"$WORK/sign.log" 2>&1 \
    || { cat "$WORK/sign.log" >&2; die "sign $*"; }
  comm -13 <(echo "$before") <(ls "$CH" | sort) | grep -o '^chl_[0-9a-f]\{32\}' | head -1
}
A2=$(sign_new supersede --old "$CH/$NEAR.json" --draft "$WORK/a2.draft.json" --pubkey "$GOV_PUB")
B=$(sign_new sign "$WORK/b.draft.json")
M=$(sign_new sign "$WORK/m.draft.json")
"$BIN/arena-admin" verify --pubkey "$GOV_PUB" --pubkey "$REPO/challenges/governance-dev.pub" \
  --security-dir "$REPO/security" "$CH/$NEAR.json" "$CH/$A2.json" "$CH/$B.json" "$CH/$M.json" | tee "$RESULTS/challenges/verify.txt"
for c in "$A2" "$B" "$M"; do cp "$CH/$c.json" "$CH/$c.sig" "$RESULTS/challenges/"; done
printf 'A1 %s\nA2 %s\nB %s\nM %s\n' "$NEAR" "$A2" "$B" "$M" | tee "$RESULTS/challenges/ids.txt"
CHALS+=("$A2" "$B" "$M")
fi

say "database $DB"
case "$DB" in arena_sp1*) ;; *) die "refusing to manage database $DB";; esac
pg_admin -c "DROP DATABASE IF EXISTS $DB WITH (FORCE)" -c "CREATE DATABASE $DB" >/dev/null
DBURL="$PG/$DB"
"$BIN/arena-server" migrate --database-url "$DBURL" >"$WORK/migrate.log" 2>&1 || { cat "$WORK/migrate.log"; die migrate; }

PIDS=()
cleanup() { for p in "${PIDS[@]:-}"; do [ -n "$p" ] && kill "$p" 2>/dev/null || true; done; wait 2>/dev/null || true; }
trap cleanup EXIT

AGENT_TOKEN="sp1-agent-$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \n')"
say "arena-server on 127.0.0.1:$PORT"
rm -rf "$WORK/objects"; mkdir -p "$WORK/objects"
env ARENA_DATABASE_URL="$DBURL" ARENA_BIND_ADDR="127.0.0.1:$PORT" ARENA_WORKER_API_BIND_ADDR="127.0.0.1:$WPORT" \
  ARENA_ADMIN_TOKEN=sp1-admin ARENA_BOOTSTRAP_AGENT_TOKEN="$AGENT_TOKEN" \
  ARENA_LEASE_SECS=600 ARENA_RETRY_BACKOFF_SECS=5 ARENA_QUOTA_SUBMISSIONS_PER_DAY=500 ARENA_QUOTA_ACTIVE_RUNS=8 \
  ARENA_RATE_LIMIT_PER_MINUTE=600 \
  "$BIN/arena-server" serve --dev --object-store-dir "$WORK/objects" --challenges-dir "$CH" \
    --governance-pubkey-file "$REPO/challenges/governance-dev.pub,$GOV_PUB" \
    --security-dir "$REPO/security" >"$WORK/server.log" 2>&1 &
PIDS+=($!)
for _ in $(seq 1 100); do curl -sf "http://127.0.0.1:$PORT/healthz" >/dev/null 2>&1 && break; sleep 0.2; done
for c in "${CHALS[@]}"; do
  curl -sf "http://127.0.0.1:$PORT/v1/challenges/$c" | python3 -c 'import json,sys; c=json.load(sys.stdin); print("registered", c["id"], c["tier"])' \
    || { tail -40 "$WORK/server.log"; die "challenge $c not registered"; }
done

say "Firecracker worker (tier cap formal), candidate VMs on host CPUs $CPUS"
FC_TOKEN=$("$BIN/arena-server" create-worker --database-url "$DBURL" --name sp1-fc --sandbox firecracker --tier-cap formal | sed -n 's/^token //p')
CLEAN="$WORK/clean"
rm -rf "$CLEAN"; mkdir -p "$CLEAN"
( cd "$REPO" && git ls-files -- formal-core spec/lean oracle/fixtures/public | tar -cf - -T - ) | tar -xf - -C "$CLEAN"
env -i PATH="$PATH" HOME="$HOME" \
  ARENA_SERVER_URL="http://127.0.0.1:$WPORT" ARENA_WORKER_TOKEN="$FC_TOKEN" \
  ARENA_WORKER_ID=sp1-fc-worker ARENA_WORK_DIR="$WORK/fc-worker" ARENA_SANDBOX_BACKEND=firecracker \
  ARENA_FC_DEPS="${ARENA_FC_DEPS:-/data/illia/nearproof-deps/firecracker}" \
  ARENA_IMAGES_DIR="$TC_IMAGES" ARENA_BUILD_TOOLCHAIN_IMAGE="sha256:$TC" \
  ARENA_BUILD_MOUNTS="$LEAN_IMG/arena/tc:/opt/lean" \
  ARENA_BUILD_PATH="/opt/lean/bin:/usr/local/rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:/usr/local/cargo/bin:/usr/local/bin:/usr/bin:/bin" \
  ARENA_FORMAL_REPO="$CLEAN" ARENA_FORMAL_CONFIGS_DIR="$REPO/runners/formal-checker/challenges" \
  ARENA_LEAN_CHECKER_IMAGES="$LEAN_IMAGES" \
  ARENA_NEAR_ORACLE="$ORACLE" ARENA_WORKLOAD_GENERATORS="$REPO/spec/workloads/near-transfer-receipt-v1" \
  ARENA_FIXTURES_DIRS="$CLEAN/oracle/fixtures/public" ARENA_CONFORMANCE_SAMPLES=3 \
  ARENA_RUN_CPUS="$CPUS" ARENA_BENCH_CPUS="$CPUS" \
  ARENA_LEASE_SECONDS=600 ARENA_POLL_MS=500 ARENA_HEARTBEAT_MS=10000 \
  "$BIN/arena-worker" >"$WORK/fc-worker.log" 2>&1 &
PIDS+=($!)

export ARENA_URL="http://127.0.0.1:$PORT" ARENA_TOKEN="$AGENT_TOKEN"
stage_dir() { # src label challenge -> package copy (git-tracked files + vendored crates) bound to the challenge
  local d="$WORK/cand-$2"; rm -rf "$d"; mkdir -p "$d"
  ( cd "$REPO/$1" && git ls-files | tar -cf - -T - ) | tar -xf - -C "$d"
  if [ "$1" = examples/zkvm-sp1 ]; then
    cp -r "$REPO/$1/source/vendor" "$REPO/$1/source/vendor-guest" "$d/source/"
  fi
  sed -i "s/^challenge = .*/challenge = \"$3\"/" "$d/candidate.toml"
  echo "$d"
}
declare -A SUBS
submit() { # label src challenge
  local d; d=$(stage_dir "$2" "$1" "$3")
  if ! "$BIN/arena" submit "$d" --challenge "$3" --json >"$RESULTS/$1.submit.json" 2>"$RESULTS/$1.submit.err.txt"; then
    # A refusal (e.g. a superseded, closed challenge) is a result, not a script failure.
    echo "$1 -> REFUSED by the server (challenge $3): $(cat "$RESULTS/$1.submit.json" "$RESULTS/$1.submit.err.txt" | tr '\n' ' ')" | tee -a "$RESULTS/submissions.txt"
    return 0
  fi
  rm -f "$RESULTS/$1.submit.err.txt"
  SUBS[$1]=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["id"])' "$RESULTS/$1.submit.json")
  echo "$1 -> ${SUBS[$1]} (challenge $3)" | tee -a "$RESULTS/submissions.txt"
}
: > "$RESULTS/submissions.txt"
say "submissions"
# Order = job order on the single worker (jobs lease FIFO by creation).
want sp1-M && submit sp1-M examples/zkvm-sp1 "$M"
want reexec-B && submit reexec-B examples/reexec-witness "$B"
want sp1-B && submit sp1-B examples/zkvm-sp1 "$B"
want sp1-A2 && submit sp1-A2 examples/zkvm-sp1 "$A2"
want sp1-A1 && submit sp1-A1 examples/zkvm-sp1 "$NEAR"
if [ "$MODE" = head ]; then
  # Every signed NEAR challenge in challenges/, newest first; superseded ones
  # are closed by the server and must refuse the submission.
  for c in $(cd "$CH" && grep -l '"name": "near-transfer-receipt' chl_*.json | xargs -n1 python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["created_at"], sys.argv[1][:-5])' | sort -r | cut -d' ' -f2); do
    submit "sp1-$c" examples/zkvm-sp1 "$c"
  done
fi

say "waiting for decisions"
DEADLINE=$(( $(date +%s) + TIMEOUT ))
while :; do
  pending=0
  for l in "${!SUBS[@]}"; do
    f="$RESULTS/$l.submission.json"
    "$BIN/arena" status "${SUBS[$l]}" --json >"$f.tmp" 2>/dev/null && mv "$f.tmp" "$f" || true
    st=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("stage",""))' "$f" 2>/dev/null || echo "?")
    [ "$st" = DECIDED ] || pending=$((pending + 1))
  done
  [ "$pending" = 0 ] && break
  [ "$(date +%s)" -gt "$DEADLINE" ] && { tail -30 "$WORK/fc-worker.log"; die "timed out with $pending pending"; }
  echo "$(date -u +%H:%M:%S) load $(cut -d' ' -f1-3 /proc/loadavg) pending $pending" >>"$RESULTS/progress.log"
  sleep 30
done
for l in "${!SUBS[@]}"; do
  "$BIN/arena" report "${SUBS[$l]}" -o "$RESULTS/$l.report.json" >/dev/null 2>&1 || true
done
for c in "${CHALS[@]}"; do
  "$BIN/arena" leaderboard --challenge "$c" --json >"$RESULTS/leaderboard.$c.json" || true
done
cp "$WORK/server.log" "$RESULTS/server.log.txt" 2>/dev/null || true
grep -v -i "token" "$WORK/fc-worker.log" >"$RESULTS/fc-worker.log.txt" 2>/dev/null || true
say "done"
for l in "${!SUBS[@]}"; do
  python3 - "$RESULTS/$l.submission.json" "$l" <<'EOF'
import json, sys
v = json.load(open(sys.argv[1]))
print(f"\n{sys.argv[2]}: {v['id']} decision={v['decision']} accepted={v['accepted']} tier={v['tier']} score={v.get('score_milli')}")
for g in v["gates"]:
    print(f"  {g['gate']:28} {g['status']:8} {','.join(g['reason_codes']):34} {g['summary'][:150]!r}")
EOF
done
