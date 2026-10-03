#!/usr/bin/env bash
# Milestone D end to end against the formal NEAR challenge, with production
# isolation (every stage in Firecracker microVMs, formal tier):
#
#   1. reference candidate examples/reexec-witness            -> ADMITTED (formal tier)
#   2. prover-only child examples/reexec-witness-fast --parent -> PROVER_ONLY, formal gates
#                                                                 reused_from the parent, ADMITTED
#   3. NEAR hostile cases (adversarial/hostile-submissions/near-*) -> REJECTED with their reasons
#   4. a verifier change (the reference with a trivially edited model) --parent
#                                                              -> VERIFIER_OR_PROTOCOL, formal
#                                                                 obligations re-checked (no reuse)
#
# Results (submission views, reports, hostile per-case JSON, a summary) are
# written to docs/e2e-results/milestone-d/ (override with ARENA_E2E_RESULTS).
#
# The signed NEAR challenge chl_5ef2bc7d2068219635426e47ca46bfbb pins
# toolchain_policy.checker_image to the identity of one build of the host
# checker tools; the production worker runs the digest-pinned lean-checker
# image, whose tools have a different identity. This script therefore signs,
# with the LOCAL operator governance key (challenges/governance-local.pub,
# private half in /data/illia/nearproof-deps/keys), an e2e-local successor
# challenge that differs ONLY in checker_image (re-pinned to the image's
# identity) and supersedes chl_5ef2…. It lives in the e2e work dir, never in
# challenges/. That re-pin is a governance action; see the results README.
#
# Requirements: shared Postgres, docker + KVM (fc-runner image), the
# toolchain and lean-checker images (deploy/images/*), a built
# oracle/target/debug/near-arena-oracle (oracle/scripts/link-nearcore.sh).
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
PG="${ARENA_E2E_PG:-postgres://arena:arena@127.0.0.1:55471}"
DB="${ARENA_E2E_DB:-arena_e2e_milestone_d}"
PORT="${ARENA_E2E_PORT:-18571}"
WPORT=$((PORT + 1))
WORK="${ARENA_E2E_WORK:-$(mktemp -d "${TMPDIR:-/tmp}/arena-e2e-d.XXXXXX")}"
RESULTS="${ARENA_E2E_RESULTS:-$REPO/docs/e2e-results/milestone-d}"
# current head of the NEAR chain (v1-2: production checker pin, vm_per_batch,
# baseline; supersedes v1.1 chl_f7eb…; the server closes superseded challenges)
NEAR="${ARENA_E2E_NEAR:-chl_3be93793610370275ae40f36a475f01f}"
GOV_KEY="${ARENA_GOV_LOCAL_KEY:-/data/illia/nearproof-deps/keys/governance-local.key}"
TC_IMAGES="${ARENA_TOOLCHAIN_IMAGES:-/data/illia/nearproof-deps/toolchain-images}"
LEAN_IMAGES="${LEAN_CHECKER_IMAGES:-/data/illia/nearproof-deps/lean-checker/images}"
ORACLE="${ARENA_NEAR_ORACLE:-$REPO/oracle/target/debug/near-arena-oracle}"
TIMEOUT="${ARENA_E2E_TIMEOUT:-3600}"
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
( cd "$REPO" && cargo build -q -j 8 -p arena-server -p arena-worker -p arena-cli -p arena-admin -p arena-formal-checker )
BIN="$REPO/target/debug"
[ -x "$ORACLE" ] || die "no near-arena-oracle at $ORACLE"

say "NEAR challenge $NEAR: checker identity of the production lean-checker image"
LEAN_IMG="$LEAN_IMAGES/$(newest "$LEAN_IMAGES")"
IDENT=$(env ARENA_LEAN_SYSROOT="$LEAN_IMG/arena/tc" ARENA_LEAN4EXPORT="$LEAN_IMG/arena/tools/lean4export" \
  ARENA_NANODA="$LEAN_IMG/arena/tools/nanoda_bin" ARENA_LEAN4LEAN="$LEAN_IMG/arena/tools/lean4lean" \
  ARENA_AUDIT_BIN="$LEAN_IMG/arena/tools/arena-audit" "$BIN/formal-check" --print-image-digest)
echo "lean-checker image $(basename "$LEAN_IMG"), checker identity $IDENT"
CH="$WORK/challenges"
rm -rf "$CH"; mkdir -p "$CH"
cp "$REPO/challenges/"*.json "$REPO/challenges/"*.sig "$REPO/challenges/"*.pub "$CH/"
PINNED=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["toolchain_policy"]["checker_image"])' "$REPO/challenges/$NEAR.json")
LOCAL_SUCCESSOR=0
if [ "$PINNED" = "$IDENT" ]; then
  echo "signed $NEAR pins this checker ($IDENT): no local successor"
  E2E_NEAR=$NEAR
else
LOCAL_SUCCESSOR=1
echo "signed $NEAR pins $PINNED != $IDENT: signing an e2e-local successor"
python3 - "$REPO/challenges/$NEAR.json" "$IDENT" "$WORK/near-e2e.draft.json" <<'EOF'
import json, sys, datetime
d = json.load(open(sys.argv[1]))
d["toolchain_policy"]["checker_image"] = sys.argv[2]
d["season"] = d["season"] + "-e2e-local"
d["supersedes"] = None
# strictly later than the superseded definition
t = datetime.datetime.fromisoformat(d["created_at"].replace("Z", "+00:00")) + datetime.timedelta(seconds=1)
d["created_at"] = t.strftime("%Y-%m-%dT%H:%M:%SZ")
json.dump(d, open(sys.argv[3], "w"), indent=2)
EOF
"$BIN/arena-admin" supersede --old "$CH/$NEAR.json" --draft "$WORK/near-e2e.draft.json" --key "$GOV_KEY" \
  --pubkey "$REPO/challenges/governance-local.pub" --challenges-dir "$CH" --security-dir "$REPO/security" >"$WORK/supersede.log" 2>&1 \
  || { cat "$WORK/supersede.log"; die "sign e2e-local challenge"; }
E2E_NEAR=$(comm -13 <(ls "$REPO/challenges/" | sort) <(ls "$CH" | sort) | grep -o '^chl_[0-9a-f]\{32\}' | head -1)
[ -n "$E2E_NEAR" ] && [ -f "$CH/$E2E_NEAR.json" ] || { ls "$CH"; cat "$WORK/supersede.log"; die "e2e challenge id"; }
echo "e2e-local challenge $E2E_NEAR (supersedes $NEAR)"
fi

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
  ARENA_LEASE_SECS=600 ARENA_RETRY_BACKOFF_SECS=1 ARENA_QUOTA_SUBMISSIONS_PER_DAY=500 ARENA_QUOTA_ACTIVE_RUNS=8 \
  ARENA_RATE_LIMIT_PER_MINUTE=600 \
  "$BIN/arena-server" serve --dev --object-store-dir "$WORK/objects" --challenges-dir "$CH" \
    --governance-pubkey-file "$REPO/challenges/governance-dev.pub,$REPO/challenges/governance-local.pub" \
    --security-dir "$REPO/security" >"$WORK/server.log" 2>&1 &
PIDS+=($!)
for _ in $(seq 1 100); do curl -sf "http://127.0.0.1:$PORT/healthz" >/dev/null 2>&1 && break; sleep 0.2; done
curl -sf "http://127.0.0.1:$PORT/v1/challenges/$E2E_NEAR" >/dev/null || { tail -40 "$WORK/server.log"; die "e2e challenge not registered"; }

say "Firecracker worker (tier cap formal)"
FC_TOKEN=$("$BIN/arena-server" create-worker --database-url "$DBURL" --name e2e-fc --sandbox firecracker --tier-cap formal | sed -n 's/^token //p')
CLEAN="$WORK/clean"
rm -rf "$CLEAN"; mkdir -p "$CLEAN"
( cd "$REPO" && git ls-files -- formal-core spec/lean oracle/fixtures/public | tar -cf - -T - ) | tar -xf - -C "$CLEAN"
TC=$(newest "$TC_IMAGES")
env -i PATH="$PATH" HOME="$HOME" \
  ARENA_SERVER_URL="http://127.0.0.1:$WPORT" ARENA_WORKER_TOKEN="$FC_TOKEN" \
  ARENA_WORKER_ID=e2e-fc-worker ARENA_WORK_DIR="$WORK/fc-worker" ARENA_SANDBOX_BACKEND=firecracker \
  ARENA_FC_DEPS="${ARENA_FC_DEPS:-/data/illia/nearproof-deps/firecracker}" \
  ARENA_IMAGES_DIR="$TC_IMAGES" ARENA_BUILD_TOOLCHAIN_IMAGE="sha256:$TC" \
  ARENA_BUILD_MOUNTS="$LEAN_IMG/arena/tc:/opt/lean" \
  ARENA_BUILD_PATH="/opt/lean/bin:/usr/local/rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:/usr/local/cargo/bin:/usr/local/bin:/usr/bin:/bin" \
  ARENA_FORMAL_REPO="$CLEAN" ARENA_FORMAL_CONFIGS_DIR="$REPO/runners/formal-checker/challenges" \
  ARENA_LEAN_CHECKER_IMAGES="$LEAN_IMAGES" \
  ARENA_NEAR_ORACLE="$ORACLE" ARENA_WORKLOAD_GENERATORS="$REPO/spec/workloads/near-transfer-receipt-v1" \
  ARENA_FIXTURES_DIRS="$CLEAN/oracle/fixtures/public" ARENA_CONFORMANCE_SAMPLES=3 \
  ${ARENA_DEV_BENCH_BATCH_CAP:+ARENA_DEV_BENCH_BATCH_CAP="$ARENA_DEV_BENCH_BATCH_CAP"} \
  ARENA_LEASE_SECONDS=600 ARENA_POLL_MS=500 ARENA_HEARTBEAT_MS=10000 \
  "$BIN/arena-worker" >"$WORK/fc-worker.log" 2>&1 &
PIDS+=($!)

export ARENA_URL="http://127.0.0.1:$PORT" ARENA_TOKEN="$AGENT_TOKEN"
stage_dir() { # src name -> copy with the e2e challenge id
  local d="$WORK/cand-$2"; rm -rf "$d"; mkdir -p "$d"
  ( cd "$REPO/$1" && git ls-files | tar -cf - -T - ) | tar -xf - -C "$d"
  sed -i "s/^challenge = .*/challenge = \"$E2E_NEAR\"/" "$d/candidate.toml"
  echo "$d"
}
submit() { # dir name [parent]
  local args=("$1" --challenge "$E2E_NEAR" --json)
  [ -n "${3:-}" ] && args+=(--parent "$3")
  "$BIN/arena" submit "${args[@]}" >"$WORK/submit-$2.json" || { cat "$WORK/submit-$2.json"; die "submit $2"; }
  python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["id"])' "$WORK/submit-$2.json"
}
wait_decided() { # sub name
  local deadline=$(( $(date +%s) + TIMEOUT )) stage
  while :; do
    "$BIN/arena" status "$1" --json >"$RESULTS/$2.submission.json" 2>/dev/null || true
    stage=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("stage",""))' "$RESULTS/$2.submission.json" 2>/dev/null || echo "?")
    [ "$stage" = DECIDED ] && break
    [ "$(date +%s)" -gt "$deadline" ] && { tail -30 "$WORK/fc-worker.log"; die "$2 timed out at stage $stage"; }
    sleep 5
  done
  "$BIN/arena" report "$1" -o "$RESULTS/$2.report.json" >/dev/null 2>&1 || true
}

say "1. reference candidate"
REF_DIR=$(stage_dir examples/reexec-witness reference)
REF=$(submit "$REF_DIR" reference); echo "reference $REF"
wait_decided "$REF" reference

say "2. prover-only child (--parent reference)"
FAST_DIR=$(stage_dir examples/reexec-witness-fast fast-child)
FAST=$(submit "$FAST_DIR" fast-child "$REF"); echo "fast child $FAST"
wait_decided "$FAST" fast-child

say "4. verifier change (reference with a trivially edited model, --parent reference)"
VC_DIR=$(stage_dir examples/reexec-witness verifier-change)
printf '\n-- e2e: trivial verifier-model change (comment only)\n' >> "$VC_DIR/formal/ReexecWitness/Model.lean"
VC=$(submit "$VC_DIR" verifier-change "$REF"); echo "verifier change $VC"
wait_decided "$VC" verifier-change

say "3. NEAR hostile cases"
set +e
"$REPO/adversarial/e2e/run.sh" --server "$ARENA_URL" --token "$AGENT_TOKEN" --challenge "$E2E_NEAR" \
  --only near-reexec-skip-refund,near-reexec-malicious-executable --timeout "$TIMEOUT" \
  --report "$RESULTS/hostile-near.json" | tee "$WORK/hostile.log"
HOSTILE_RC=${PIPESTATUS[0]}
set -e
"$BIN/arena" leaderboard --challenge "$E2E_NEAR" --json >"$RESULTS/leaderboard.json"

say "assertions + summary"
python3 - "$RESULTS" "$E2E_NEAR" "$NEAR" "$REF" "$FAST" "$VC" "$IDENT" "$(basename "$LEAN_IMG")" "$TC" "$HOSTILE_RC" "$LOCAL_SUCCESSOR" "${ARENA_FC_DEPS:-/data/illia/nearproof-deps/firecracker}" "${ARENA_DEV_BENCH_BATCH_CAP:-none}" <<'EOF'
import json, sys, os, datetime
res, chal, orig, ref, fast, vc, ident, leanimg, tc, hrc, local, fcdeps, cap = sys.argv[1:14]
load = lambda n: json.load(open(os.path.join(res, f"{n}.submission.json")))
R, F, V = load("reference"), load("fast-child"), load("verifier-change")
hostile = json.load(open(os.path.join(res, "hostile-near.json"))) if os.path.exists(os.path.join(res, "hostile-near.json")) else {}
FORMAL = {"ARTIFACT_BINDING", "FORMAL_SEMANTIC_SOUNDNESS", "FORMAL_SEMANTIC_COMPLETENESS",
          "FORMAL_CRYPTO_SOUNDNESS", "FORMAL_IMPL_CONNECTION", "AXIOM_AUDIT"}
fails, lines = [], []
def check(c, m):
    lines.append(("- [x] " if c else "- [ ] **FAIL** ") + m)
    print(("ok   " if c else "FAIL ") + m)
    if not c: fails.append(m)
def gates(v): return {g["gate"]: g for g in v["gates"]}
def table(name, v):
    out = [f"### {name}: `{v['id']}`", "",
           f"decision **{v['decision']}**, accepted {v['accepted']}, tier `{v['tier']}`, change class `{v.get('change_class')}`, score {v.get('score_milli')}", "",
           "| gate | status | reasons | reused_from | summary |", "|---|---|---|---|---|"]
    for g in v["gates"]:
        s = g["summary"].replace("|", "\\|").replace("\n", " ")[:160]
        out.append(f"| {g['gate']} | {g['status']} | {', '.join(g['reason_codes'])} | {g.get('reused_from') or ''} | {s} |")
    return out + [""]
r, f, v = gates(R), gates(F), gates(V)
check(R["decision"] == "ADMITTED" and R["accepted"] is True, "reference ADMITTED (accepted)")
check(R["tier"] == "formal", "reference evaluated at formal tier (Firecracker, no DEMO_ONLY)")
check(all(g["status"] in ("PASS", "NOT_APPLICABLE") for g in R["gates"]), "every reference gate PASS")
check(all("DEMO_ONLY" not in g["reason_codes"] for g in R["gates"]), "no DEMO_ONLY on the reference")
check(F.get("change_class") == "PROVER_ONLY", "fast child classified PROVER_ONLY")
check(all(f[g].get("reused_from") == ref for g in FORMAL if g in f), "fast child's formal gates reused_from the reference")
check(F["decision"] == "ADMITTED", "fast child ADMITTED")
check(all(f[g]["status"] == "PASS" and not f[g].get("reused_from") for g in ("BUILD_REPRODUCIBLE", "CONFORMANCE_DIFFERENTIAL", "ADVERSARIAL_PROOFS", "BENCHMARK") if g in f),
      "fast child's build/conformance/adversarial/benchmark re-ran")
check(V.get("change_class") == "VERIFIER_OR_PROTOCOL", "verifier change classified VERIFIER_OR_PROTOCOL")
check(all(not v[g].get("reused_from") for g in FORMAL if g in v), "verifier change: formal obligations re-checked (nothing reused)")
check(V["decision"] == "ADMITTED", "verifier change (comment-only, still certified) ADMITTED after the re-check")
for name, o in sorted(hostile.items()):
    check(o.get("decision") not in ("ADMITTED",) and o.get("accepted") is not True, f"hostile {name}: not admitted ({o.get('decision')})")
    check(bool(o.get("ok")), f"hostile {name}: matches expect.json (failed {o.get('failed_gates')}, reasons {o.get('reason_codes')})")
check(len(hostile) == 2, "both NEAR hostile cases ran")
if local == "0":
    check(chal == orig, f"evaluated against the signed challenge {orig} itself (no local successor)")
    check(R.get("score_milli") is not None, f"reference scored against the pinned baseline (score {R.get('score_milli')})")
md = ["# Milestone D e2e — formal NEAR challenge, Firecracker", "",
      f"Run: {datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')} on the shared dev host. Generated by `tests/e2e/milestone-d.sh`.", "",
      "## Setup", "",
      (f"* challenge: the signed `{chal}` itself (no local successor); its `toolchain_policy.checker_image` `{ident}` is the checker identity of the production lean-checker image `sha256:{leanimg}`." if local == "0" else
       f"* challenge: e2e-local `{chal}`, superseding the signed `{orig}`; identical except `toolchain_policy.checker_image` re-pinned to `{ident}` (the checker identity of lean-checker image `sha256:{leanimg}`). Signed with the LOCAL operator key (`challenges/governance-local.pub`)."),
      f"* worker: one `arena-worker`, backend `firecracker` (tier cap formal, deps `{fcdeps}`); builds in toolchain image `sha256:{tc}` with the Lean toolchain from the lean-checker image mounted read-only; FORMAL_CHECK in the lean-checker image; NEAR oracle `near-arena-oracle` (public fixtures + judge-sampled cases); benchmark batch cap: {cap}. Scores (if any) are dev-host numbers against the challenge's pinned dev-host baseline.",
      "* candidates: `examples/reexec-witness` (reference, native-lean), `examples/reexec-witness-fast` (`--parent` reference), the reference with a comment appended to `formal/ReexecWitness/Model.lean` (`--parent` reference), hostile `near-reexec-skip-refund`, `near-reexec-malicious-executable`.", "",
      "## Checks", ""] + lines + ["", "## Submissions", ""]
md += table("1. reference", R) + table("2. prover-only child", F) + table("4. verifier change", V)
md += ["### 3. NEAR hostile cases", "", "| case | decision | failed gates | reasons | expected | ok |", "|---|---|---|---|---|---|"]
for name, o in sorted(hostile.items()):
    md.append(f"| {name} | {o.get('decision')} | {', '.join(o.get('failed_gates', []))} | {', '.join(o.get('reason_codes', []))} | {', '.join(o.get('expected_failing_gates', []))} / {', '.join(o.get('expected_reason_codes', []))} | {o.get('ok')} |")
md += ["", f"Raw: `*.submission.json` (API views), `*.report.json` (signed reports), `hostile-near.json`, `leaderboard.json`.", ""]
open(os.path.join(res, "README.md"), "w").write("\n".join(md))
print(f"\n{len(lines) - len(fails)}/{len(lines)} checks passed; results in {res}")
sys.exit(1 if fails else 0)
EOF
